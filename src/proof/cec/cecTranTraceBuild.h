// Observation-CEX constraints are disjunctions over evaluations of ONE permanent
// recipe.  Their first-difference argument is documented in STRAN2.md.
// Branching converts the disjunctions to partial on/off sets for the native
// iterator.  SAT/PDR never select a recipe or a truth-table completion.
typedef struct Cec_TranTbBranch_t_ {
    Vec_Int_t * values;
    int clause;
} Cec_TranTbBranch_t;
typedef struct Cec_TranTb_t_ {
    Gia_Man_t * p;
    Vec_Int_t * pool;
    Vec_Int_t * observations;
    Gia_Man_t * observedSource;
    Vec_Wrd_t * patterns;
    Vec_Ptr_t * clauses, * work, * bank;
    int root, words, feedback, outputScope, budget, branchLimit, branchCount, proposals;
    int exhausted, branchCapped, proofs, replay, sat, unknown, direct, winnerNew;
    int cone, rawFrames, coneFrames, rawTerms, coneTerms;
    int costAware, costEvaluated, costRejected, oldBoundExcluded;
    int oldBoundPositive, oldBoundProved, zeroNewProved, zeroNewCommits;
    long long costRawGates, costNewGates;
    int cutAware, cutMulti, cutViews, cutCapped, cutKit, cutBdc, cutPositive;
    int cutProofs, cutCommitKit, cutCommitBdc;
    int cutOldBoundExcluded, cutOldBoundPositive, cutOldBoundProved;
    long long cutRawGates, cutNewGates;
    Cec_TranFrozenHash_t frozenHash;
    int * costRefs;
    char * costMffcMark;
    Vec_Int_t * costMffc, * costBoundary;
    abctime proofTime;
} Cec_TranTb_t;

static int Cec_TranTbMapLit( int * pMap, int Lit )
{
    return Abc_LitNotCond(pMap[Abc_Lit2Var(Lit)], Abc_LitIsCompl(Lit));
}

static int Cec_TranTbRecipeLit( int Code, int * pMap, int * pGates )
{
    int Lit;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return Cec_TranTbMapLit(pMap, Code);
    Lit = Cec_TranRecipeGateLit(Code);
    return Abc_LitNotCond(pGates[Abc_Lit2Var(Lit)], Abc_LitIsCompl(Lit));
}

static int Cec_TranTbCode( int code, unsigned char * values, int * gates )
{
    int lit=Cec_TranRecipeCodeIsGate(code)?Cec_TranRecipeGateLit(code):code;
    return (Cec_TranRecipeCodeIsGate(code)?gates[Abc_Lit2Var(lit)]:values[Abc_Lit2Var(lit)]) ^ Abc_LitIsCompl(lit);
}

// Price a recipe in the current frozen AIG, not by its syntactic gate count.
// Structural hashing may reuse recipe nodes, while reused internal divisors
// become support boundaries and can keep part of the old MFFC alive.  The
// final cleaned-network check remains the commit authority.
static int Cec_TranTbActualGain( Cec_TranTb_t * b, Cec_TranCand_t const * cand,
    int * pNew )
{
    int Gain;
    assert( b->costAware && b->costRefs && b->costMffcMark );
    Vec_IntClear( b->costBoundary );
    *pNew = Cec_TranFrozenRecipeCost( b->p, &b->frozenHash, cand, NULL,
        b->costBoundary );
    Gain = Cec_TranCandFrozenGainWithRefs( b->p, &b->frozenHash, cand,
        NULL, NULL, b->costRefs, b->costMffcMark, b->costMffc,
        b->costBoundary );
    b->costEvaluated++;
    b->costRawGates += cand->nGates;
    b->costNewGates += *pNew;
    return Gain;
}

// A frontier obtained by repeatedly replacing one AND leaf with both fanins
// is a structural cut: every PI-to-root path still crosses a leaf.  Enumerate
// several such frontiers instead of treating an arbitrary divisor subset as
// an independent support.  The existing per-root q budget bounds the number
// of stored views; the four-leaf limit is the classic rewrite truth-table
// domain and keeps exact function computation exhaustive.
static int Cec_TranTbCutKnown( Vec_Ptr_t * vCuts, Vec_Int_t * vCut )
{
    Vec_Int_t * vOld;
    int i;
    Vec_PtrForEachEntry(Vec_Int_t *,vCuts,vOld,i)
        if ( Vec_IntEqual(vOld,vCut) ) return 1;
    return 0;
}

static Vec_Ptr_t * Cec_TranTbCuts( Cec_TranTb_t * b, int iRoot )
{
    Vec_Ptr_t * vCuts=Vec_PtrAlloc(16);
    Vec_Int_t * vCut=Vec_IntAlloc(4), * vNew;
    int i,k,iLeaf,iFan;
    Vec_IntPush(vCut,iRoot); Vec_PtrPush(vCuts,vCut);
    for ( i=0; i<Vec_PtrSize(vCuts); ++i )
    {
        vCut=(Vec_Int_t *)Vec_PtrEntry(vCuts,i);
        Vec_IntForEachEntry(vCut,iLeaf,k)
        {
            Gia_Obj_t * pLeaf=Gia_ManObj(b->p,iLeaf);
            if ( !Gia_ObjIsAnd(pLeaf) ) continue;
            vNew=Vec_IntDup(vCut); Vec_IntRemove(vNew,iLeaf);
            iFan=Gia_ObjFaninId0p(b->p,pLeaf);
            if ( iFan ) Vec_IntPushUniqueOrder(vNew,iFan);
            iFan=Gia_ObjFaninId1p(b->p,pLeaf);
            if ( iFan ) Vec_IntPushUniqueOrder(vNew,iFan);
            if ( Vec_IntSize(vNew)>4 || Cec_TranTbCutKnown(vCuts,vNew) )
            { Vec_IntFree(vNew); continue; }
            if ( Vec_PtrSize(vCuts)-1 >= b->budget )
            { b->cutCapped=1; Vec_IntFree(vNew); continue; }
            Vec_PtrPush(vCuts,vNew);
        }
        if ( !b->cutMulti ) break;
    }
    return vCuts;
}

// Synthesize the complete root function over one proven structural cut.
// Kit and BDC see the same full-care truth table.  This lane is additive: it
// does not replace the temporal ODC constructor or force its don't-cares to a
// strict completion.
static int Cec_TranTbCutCandidate( Cec_TranRoot_t * pRoot,
    Vec_Int_t * vLeaves, word Truth, int fBdc, Cec_TranCand_t * pCand )
{
    unsigned Off[8]={0}, On[8]={0};
    Vec_Int_t * vRanks=Vec_IntAlloc(Vec_IntSize(vLeaves));
    Vec_Int_t * vMemory=NULL, * vBdc=NULL;
    Kit_Graph_t * pGraph=NULL;
    int i,Code,nGates=0;
    memset(pCand,0,sizeof(*pCand));
    for ( i=0; i<Vec_IntSize(vLeaves); ++i ) Vec_IntPush(vRanks,i);
    if ( fBdc )
    {
        word Care=~(word)0;
        vBdc=Bdc_ManBidecResub(&Truth,&Care,Vec_IntSize(vLeaves));
        if ( vBdc==NULL || Vec_IntSize(vBdc)<3 || !(Vec_IntSize(vBdc)&1) )
            goto cleanup;
        nGates=(Vec_IntSize(vBdc)-1)/2;
    }
    else
    {
        On[0]=(unsigned)Truth; Off[0]=~On[0];
        vMemory=Vec_IntAlloc(0);
        pGraph=Kit_TruthToGraph2(Off,On,Vec_IntSize(vLeaves),vMemory);
        if ( pGraph==NULL ) goto cleanup;
        nGates=Kit_GraphNodeNum(pGraph);
    }
    if ( nGates>CEC_TRAN_RECIPE_NODES_MAX ) goto cleanup;
    pCand->iTarget=pRoot->iObj; pCand->iDiv0=pCand->iDiv1=-1;
    pCand->nMffc=pRoot->nMffc; pCand->nGates=nGates;
    if ( nGates ) pCand->Recipe=Cec_TranRecipeAlloc(2*nGates);
    if ( fBdc )
    {
        for ( i=0; i<2*nGates; ++i )
            pCand->Recipe[i]=Cec_TranBdcLitToRecipeCode(
                Vec_IntEntry(vBdc,i),vLeaves,vRanks,Vec_IntSize(vLeaves));
        pCand->iOut=Cec_TranBdcLitToRecipeCode(Vec_IntEntryLast(vBdc),
            vLeaves,vRanks,Vec_IntSize(vLeaves));
    }
    else if ( Kit_GraphIsConst(pGraph) )
        pCand->iOut=Kit_GraphIsConst1(pGraph);
    else
    {
        for ( i=0; i<nGates; ++i )
        {
            Kit_Node_t const * pNode=pGraph->pNodes+Vec_IntSize(vLeaves)+i;
            pCand->Recipe[2*i]=Cec_TranKitEdgeToRecipeCode(pNode->eEdge0,
                vLeaves,vRanks,Vec_IntSize(vLeaves));
            pCand->Recipe[2*i+1]=Cec_TranKitEdgeToRecipeCode(pNode->eEdge1,
                vLeaves,vRanks,Vec_IntSize(vLeaves));
        }
        pCand->iOut=Cec_TranKitEdgeToRecipeCode(pGraph->eRoot,
            vLeaves,vRanks,Vec_IntSize(vLeaves));
    }
    pCand->nKind=CEC_TRAN_CAND_CONSTR; pCand->fStrict=1;
    pCand->fKitPortfolio=!fBdc; pCand->fBdcPortfolio=fBdc;
    Cec_TranCandCanonicalizeRecipe(pCand);
    for ( i=-1; i<2*pCand->nGates; ++i )
    {
        Code=i<0?pCand->iOut:pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) || !Abc_Lit2Var(Code) ) continue;
        if ( pCand->iDiv0==-1 ) pCand->iDiv0=Code;
        else if ( Abc_Lit2Var(pCand->iDiv0)!=Abc_Lit2Var(Code) )
        { pCand->iDiv1=Code; break; }
    }
    Vec_IntFree(vRanks); Vec_IntFreeP(&vMemory); Vec_IntFreeP(&vBdc);
    if ( pGraph ) Kit_GraphFree(pGraph);
    return 1;
cleanup:
    Vec_IntFree(vRanks); Vec_IntFreeP(&vMemory); Vec_IntFreeP(&vBdc);
    if ( pGraph ) Kit_GraphFree(pGraph);
    return 0;
}

// Keep the complete transition relation, but expose the chosen observation
// boundary as POs. A nullable recipe selects the original system. No window
// cutpoints are free inputs: all outside context is copied conservatively.
static Gia_Man_t * Cec_TranTbObserve( Cec_TranTb_t * b, Cec_TranCand_t * cand )
{
    Gia_Man_t * q=Gia_ManStart(Gia_ManObjNum(b->p)+100);
    int * map=ABC_CALLOC(int,Gia_ManObjNum(b->p));
    int i,j,id,gates[CEC_TRAN_RECIPE_NODES_MAX];
    Gia_Obj_t * o;
    q->pName=Abc_UtilStrsav("tracebuild_window_observation");
    Gia_ManForEachCi(b->p,o,i) map[Gia_ObjId(b->p,o)]=Gia_ManAppendCi(q);
    Gia_ManHashAlloc(q);
    Gia_ManForEachAnd(b->p,o,i)
    {
        map[i]=Cec_TranHashGate(q,o,Cec_TranTbMapLit(map,Gia_ObjFaninLit0p(b->p,o)),Cec_TranTbMapLit(map,Gia_ObjFaninLit1p(b->p,o)));
        if ( cand && i==b->root )
        {
            for ( j=0; j<cand->nGates; ++j )
                gates[j]=Gia_ManHashAnd(q,Cec_TranTbRecipeLit(cand->Recipe[2*j],map,gates),Cec_TranTbRecipeLit(cand->Recipe[2*j+1],map,gates));
            map[i]=Cec_TranTbRecipeLit(cand->iOut,map,gates);
        }
    }
    Gia_ManForEachCo(b->p,o,i) map[Gia_ObjId(b->p,o)]=Cec_TranTbMapLit(map,Gia_ObjFaninLit0p(b->p,o));
    Vec_IntForEachEntry(b->observations,id,i) Gia_ManAppendCo(q,map[id]);
    Gia_ManForEachRi(b->p,o,i) Gia_ManAppendCo(q,map[Gia_ObjId(b->p,o)]);
    Gia_ManHashStop(q); Gia_ManSetRegNum(q,Gia_ManRegNum(b->p)); ABC_FREE(map);
    return q;
}

static void Cec_TranTbBoundary( Cec_TranTb_t * b, Cec_ParTran_t * pars )
{
    Gia_Obj_t * o;
    int i, overflow;
    b->observations=Vec_IntAlloc(16);
    if ( b->outputScope )
    {
        Gia_ManForEachPo(b->p,o,i) Vec_IntPush(b->observations,Gia_ObjId(b->p,o));
        b->observedSource=b->p;
    }
    else
    {
        Vec_Int_t * nodes=Vec_IntAlloc(32);
        if ( pars->fOdcStrict || (pars->nExplore&16384) ) Vec_IntPush(b->observations,b->root);
        else Cec_TranWindowCollect(b->p,b->root,Cec_TranWindowDepth(pars),
            CEC_TRAN_RECIPE_NODES_MAX-pars->nDepNodesMax,nodes,b->observations,&overflow);
        assert(Vec_IntSize(b->observations)>0);
        Vec_IntFree(nodes); b->observedSource=Cec_TranTbObserve(b,NULL);
    }
}

static int Cec_TranTbPattern( Cec_TranTb_t * b, unsigned char * values )
{
    word * bits=ABC_CALLOC(word,b->words);
    int i, id, found=-1, n=Vec_WrdSize(b->patterns)/b->words;
    Vec_IntForEachEntry(b->pool,id,i) if ( values[id] ) bits[i>>6] |= (word)1<<(i&63);
    for ( i=0; i<n; ++i )
        if ( !memcmp(bits,Vec_WrdArray(b->patterns)+(size_t)i*b->words,sizeof(word)*b->words) ) { found=i; break; }
    if ( found<0 )
    {
        found=n;
        for ( i=0; i<b->words; ++i ) Vec_WrdPush(b->patterns,bits[i]);
        Abc_Print(1,"tracebuild-pattern root=%d row=%d values=",b->root,found);
        for ( i=0; i<Vec_IntSize(b->pool); ++i ) Abc_Print(1,"%d",(int)((bits[i>>6]>>(i&63))&1));
        Abc_Print(1,"\n");
    }
    ABC_FREE(bits); return found;
}

// Backward temporal support of ONE actually failing observation. Treat root
// as an unknown function of the ENTIRE admissible pool, not just the failed
// recipe's support. This closes dependencies through possible feedback in a
// future recipe. No simulation sensitivity or source-state invariant is used.
// Space is O(objects + registers + frames), with one frame marked at a time.
static unsigned char * Cec_TranTbConeFrames( Cec_TranTb_t * b, int observation, int frames )
{
    unsigned char * keep=ABC_CALLOC(unsigned char,frames);
    unsigned char * marked=ABC_CALLOC(unsigned char,Gia_ManObjNum(b->p));
    Vec_Int_t * previous=Vec_IntAlloc(Gia_ManRegNum(b->p));
    Gia_Obj_t * o;
    int f,i,j,id;
    marked[observation]=1;
    for ( f=frames-1; f>=0; --f )
    {
        for ( i=Gia_ManObjNum(b->p)-1; i>0; --i )
        {
            if ( !marked[i] ) continue;
            o=Gia_ManObj(b->p,i);
            if ( i==b->root )
            {
                keep[f]=1;
                Vec_IntForEachEntry(b->pool,id,j)
                { assert(id<b->root); marked[id]=1; }
            }
            else if ( Gia_ObjIsAnd(o) )
            { marked[Gia_ObjFaninId0p(b->p,o)]=1; marked[Gia_ObjFaninId1p(b->p,o)]=1; }
            else if ( Gia_ObjIsCo(o) ) marked[Gia_ObjFaninId0p(b->p,o)]=1;
        }
        if ( !f ) break;
        Vec_IntClear(previous);
        Gia_ManForEachRo(b->p,o,i)
            if ( marked[Gia_ObjId(b->p,o)] ) Vec_IntPush(previous,Gia_ObjId(b->p,Gia_ManRi(b->p,i)));
        if ( !Vec_IntSize(previous) ) break;
        memset(marked,0,Gia_ManObjNum(b->p));
        Vec_IntForEachEntry(previous,id,i) marked[id]=1;
    }
    ABC_FREE(marked); Vec_IntFree(previous); return keep;
}

// Simulate the source and permanently overridden candidate in the original
// object numbering.  Divisors precede root, so no candidate-side cutpoint is
// unconstrained. Learn only after a disagreement at the chosen boundary.
static void Cec_TranTbLearn( Cec_TranTb_t * b, Cec_TranCand_t * cand, Abc_Cex_t * cex )
{
    unsigned char * vals[2], * states[2];
    Vec_Int_t * clause=Vec_IntAlloc(16);
    Vec_Int_t * frameTerms=b->cone?Vec_IntAlloc(cex->iFrame+1):NULL;
    Gia_Obj_t * o;
    int f, side, i, j, bad=0, badObject=-1, term, nObj=Gia_ManObjNum(b->p);
    for ( side=0; side<2; ++side )
    { vals[side]=ABC_CALLOC(unsigned char,nObj); states[side]=ABC_CALLOC(unsigned char,Gia_ManRegNum(b->p)); }
    assert(cex->nPis==Gia_ManPiNum(b->p));
    for ( f=0; f<=cex->iFrame && !bad; ++f )
    {
        for ( side=0; side<2; ++side )
        {
            unsigned char * v=vals[side];
            Gia_ManForEachPi(b->p,o,i) v[Gia_ObjId(b->p,o)]=Abc_InfoHasBit(cex->pData,cex->nRegs+f*cex->nPis+i);
            Gia_ManForEachRo(b->p,o,i) v[Gia_ObjId(b->p,o)]=states[side][i];
            Gia_ManForEachAnd(b->p,o,i)
            {
                int a=v[Gia_ObjFaninId0p(b->p,o)]^Gia_ObjFaninC0(o);
                int c=v[Gia_ObjFaninId1p(b->p,o)]^Gia_ObjFaninC1(o);
                v[i]=Gia_ObjIsXor(o)?a^c:a&c;
                if ( side && i==b->root )
                {
                    int gates[CEC_TRAN_RECIPE_NODES_MAX];
                    for ( j=0; j<cand->nGates; ++j )
                        gates[j]=Cec_TranTbCode(cand->Recipe[2*j],v,gates)&Cec_TranTbCode(cand->Recipe[2*j+1],v,gates);
                    v[i]=Cec_TranTbCode(cand->iOut,v,gates);
                    term=Abc_Var2Lit(Cec_TranTbPattern(b,v),!v[i]);
                    if ( frameTerms ) Vec_IntPush(frameTerms,term);
                    assert(Vec_IntFind(clause,term^1)<0);
                    if ( Vec_IntFind(clause,term)<0 ) Vec_IntPush(clause,term);
                }
            }
            Gia_ManForEachCo(b->p,o,i) v[Gia_ObjId(b->p,o)]=v[Gia_ObjFaninId0p(b->p,o)]^Gia_ObjFaninC0(o);
            Gia_ManForEachRi(b->p,o,i) states[side][i]=v[Gia_ObjId(b->p,o)];
        }
        Vec_IntForEachEntry(b->observations,j,i)
            if ( vals[0][j]!=vals[1][j] ) { bad=1; if ( badObject<0 ) badObject=j; }
    }
    assert(bad && Vec_IntSize(clause)>0);
    b->rawFrames+=f; b->rawTerms+=Vec_IntSize(clause);
    if ( frameTerms )
    {
        unsigned char * keep=Cec_TranTbConeFrames(b,badObject,f);
        assert(Vec_IntSize(frameTerms)==f);
        Abc_Print(1,"tracebuild-cone-slice root=%d clause=%d bad-object=%d frames=%d selected-time-pattern-value=",
            b->root,Vec_PtrSize(b->clauses),badObject,f);
        j=0;
        Vec_IntForEachEntry(frameTerms,term,i)
            if ( keep[i] ) Abc_Print(1,"%s%d:%d:%d",j++?",":"",i,Abc_Lit2Var(term),Abc_LitIsCompl(term));
        Abc_Print(1,"\n");
        Vec_IntClear(clause);
        Vec_IntForEachEntry(frameTerms,term,i)
            if ( keep[i] ) { ++b->coneFrames; if ( Vec_IntFind(clause,term)<0 ) Vec_IntPush(clause,term); }
        assert(Vec_IntSize(clause)>0);
        ABC_FREE(keep); Vec_IntFree(frameTerms);
    }
    else b->coneFrames+=f;
    b->coneTerms+=Vec_IntSize(clause);
    Abc_Print(1,"tracebuild-clause root=%d id=%d boundary=%s bad-frame=%d terms=",b->root,Vec_PtrSize(b->clauses),b->outputScope?"output":"window",f-1);
    Vec_IntForEachEntry(clause,term,i) Abc_Print(1,"%s%d:%d",i?",":"",Abc_Lit2Var(term),Abc_LitIsCompl(term));
    Abc_Print(1,"\n"); Vec_PtrPush(b->clauses,clause);
    for ( side=0; side<2; ++side ) { ABC_FREE(vals[side]); ABC_FREE(states[side]); }
}

static Cec_TranTbBranch_t * Cec_TranTbBranch( Vec_Int_t * values, int clause )
{
    Cec_TranTbBranch_t * s=ABC_ALLOC(Cec_TranTbBranch_t,1);
    s->values=values?Vec_IntDup(values):Vec_IntAlloc(16); s->clause=clause;
    return s;
}

static void Cec_TranTbBranchFree( Cec_TranTbBranch_t * s )
{ Vec_IntFree(s->values); ABC_FREE(s); }

// Partition an unsatisfied clause t0 OR t1 OR ... into disjoint branches
// t0; !t0 & t1; !t0 & !t1 & t2; ... .  Unit propagation is the one-term case.
// Truncation is solely an explicit search budget, never an UNSAT conclusion.
static Cec_TranTbBranch_t * Cec_TranTbReady( Cec_TranTb_t * b )
{
    while ( Vec_PtrSize(b->work) )
    {
        Cec_TranTbBranch_t * s=(Cec_TranTbBranch_t *)Vec_PtrPop(b->work);
        int split=0, i, term, value, n=Vec_WrdSize(b->patterns)/b->words;
        while ( Vec_IntSize(s->values)<n ) Vec_IntPush(s->values,-1);
        for ( ; s->clause<Vec_PtrSize(b->clauses); ++s->clause )
        {
            Vec_Int_t * clause=(Vec_Int_t *)Vec_PtrEntry(b->clauses,s->clause);
            Vec_Int_t * freeTerms=Vec_IntAlloc(Vec_IntSize(clause));
            int satisfied=0;
            Vec_IntForEachEntry(clause,term,i)
            {
                value=Vec_IntEntry(s->values,Abc_Lit2Var(term));
                if ( value==Abc_LitIsCompl(term) ) { satisfied=1; break; }
                if ( value<0 ) Vec_IntPush(freeTerms,term);
            }
            if ( satisfied ) { Vec_IntFree(freeTerms); continue; }
            if ( Vec_IntSize(freeTerms)==1 )
            {
                term=Vec_IntEntry(freeTerms,0); Vec_IntWriteEntry(s->values,Abc_Lit2Var(term),Abc_LitIsCompl(term));
                Vec_IntFree(freeTerms); continue;
            }
            if ( Vec_IntSize(freeTerms)>1 )
            {
                Vec_Ptr_t * children=Vec_PtrAlloc(Vec_IntSize(freeTerms));
                Cec_TranTbBranch_t * child;
                Vec_IntForEachEntry(freeTerms,term,i)
                {
                    if ( Vec_PtrSize(b->work)+Vec_PtrSize(children)>=b->budget ) { ++b->branchCapped; break; }
                    child=Cec_TranTbBranch(s->values,s->clause+1);
                    Vec_IntWriteEntry(child->values,Abc_Lit2Var(term),Abc_LitIsCompl(term));
                    Vec_PtrPush(children,child);
                    Vec_IntWriteEntry(s->values,Abc_Lit2Var(term),!Abc_LitIsCompl(term));
                }
                for ( i=Vec_PtrSize(children)-1; i>=0; --i ) Vec_PtrPush(b->work,Vec_PtrEntry(children,i));
                Vec_PtrFree(children);
            }
            Vec_IntFree(freeTerms); split=1; break;
        }
        if ( !split ) return s;
        Cec_TranTbBranchFree(s);
    }
    return NULL;
}

static Cec_TranSim_t * Cec_TranTbSim( Cec_TranTb_t * b, Cec_TranTbBranch_t * s, word ** pCare )
{
    int i,j,id,n=Vec_IntSize(s->values), words=Abc_MaxInt(1,(n+63)/64);
    Cec_TranSim_t * sim=Cec_TranSimStartRootBatch(b->p,words,1);
    *pCare=ABC_CALLOC(word,words);
    for ( i=0; i<n; ++i )
    {
        word * bits=Vec_WrdArray(b->patterns)+(size_t)i*b->words, mask=(word)1<<(i&63);
        int target=Vec_IntEntry(s->values,i);
        if ( target<0 ) continue;
        (*pCare)[i>>6] |= mask;
        if ( target ) Cec_TranSimObj(sim,b->root)[i>>6] |= mask;
        Vec_IntForEachEntry(b->pool,id,j)
            if ( (bits[j>>6]>>(j&63))&1 ) Cec_TranSimObj(sim,id)[i>>6] |= mask;
    }
    return sim;
}

// 1=full PDR proof, 0=real boundary trace, -1=UNKNOWN. Return the cleaned
// candidate only on proof; borrowed CEX is valid while the common bank lives.
static int Cec_TranTbCheck( Cec_TranTb_t * b, Cec_TranCand_t * cand,
    Gia_Man_t ** result, Abc_Cex_t ** cex, int * id )
{
    Vec_Int_t * one=Vec_IntAlloc(1);
    Gia_Man_t * dup, * clean, * product, * observedCandidate;
    int k,status;
    abctime start=Abc_Clock();
    assert(Cec_TranProofHistoryTopoValid(b->p,cand));
    Vec_IntPush(one,0); dup=Cec_TranDupRootBundle(b->p,cand,one); Vec_IntFree(one);
    clean=Cec_TranCleanupKeepRegs(dup,NULL); Gia_ManStop(dup);
    observedCandidate=b->outputScope?clean:Cec_TranTbObserve(b,cand);
    *result=NULL; *cex=NULL;
    Vec_PtrForEachEntry(Abc_Cex_t *,b->bank,*cex,k)
        if ( Cec_TranRelReplay(b->observedSource,observedCandidate,*cex) ) break;
    if ( k<Vec_PtrSize(b->bank) )
    {
        ++b->replay;
        if ( !b->outputScope ) Gia_ManStop(observedCandidate);
        Gia_ManStop(clean); b->proofTime+=Abc_Clock()-start; return 0;
    }
    ++b->proofs;
    product=Gia_ManMiter(b->observedSource,observedCandidate,0,0,1,0,0);
    status=Cec_TranRelPdr(product,b->outputScope?"tracebuild-product":"tracebuild-window",id,b->bank);
    Gia_ManStop(product);
    if ( !b->outputScope ) Gia_ManStop(observedCandidate);
    b->proofTime+=Abc_Clock()-start;
    if ( status==1 ) { *result=clean; *cex=NULL; return 1; }
    if ( status==0 ) { ++b->sat; *cex=(Abc_Cex_t *)Vec_PtrEntryLast(b->bank); }
    else { ++b->unknown; *cex=NULL; }
    Gia_ManStop(clean); return status;
}

static Gia_Man_t * Cec_TranTbSearch( Cec_TranTb_t * b, Cec_ParTran_t * pars,
    Cec_TranRoot_t * root, Cec_TranCand_t * winner, int * proofId )
{
    Cec_TranCand_t cand;
    Cec_TranTbBranch_t * branch;
    Gia_Man_t * clean=NULL;
    Abc_Cex_t * cex;
    int i, f, status, lit;
    // Same seed oracle and material in both arms. No old-root signature is
    // a constraint. A valid Direct alternative marks this root out of scope.
    for ( i=-1; i<Vec_IntSize(b->pool); ++i ) for ( f=0; f<2; ++f )
    {
        lit=i<0?f:Abc_Var2Lit(Vec_IntEntry(b->pool,i),f);
        cand=Cec_TranCandCreateLiteral(b->root,lit,root->nMffc,i<0?0:1,0);
        status=Cec_TranTbCheck(b,&cand,&clean,&cex,proofId);
        if ( status==1 ) { ++b->direct; Gia_ManStop(clean); return NULL; }
        if ( status==0 ) Cec_TranTbLearn(b,&cand,cex);
    }
    Vec_PtrPush(b->work,Cec_TranTbBranch(NULL,0));
    // A branch with no native recipe is not a recipe proposal. The explored
    // and pending branch populations are both bounded by the explicit q budget.
    while ( b->proposals<b->budget && (!b->branchLimit || b->branchCount<b->branchLimit) && (branch=Cec_TranTbReady(b))!=NULL )
    {
        Cec_TranDepScratch_t dep;
        word * care;
        Cec_TranSim_t * sim=Cec_TranTbSim(b,branch,&care);
        int cursor[6]={0}, exhausted=0, attempt, raw, changed=0;
        void * cache=NULL, * it;
        abctime tm=0;
        ++b->branchCount;
        Abc_ResubPrepareManager(sim->nSlots);
        Cec_TranDepScratchStart(&dep,sim->nSlots,Vec_IntSize(b->pool),1);
        // The actual-cost lane prices new physical nodes after frozen hashing.
        // Keep the true MFFC for that accounting, but let its native iterator
        // use the existing N syntax budget rather than the raw MFFC-1 bound.
        it=Cec_TranDependencyIteratorStartWithRawBudget(sim,pars,root,b->pool,
            care,&dep,cursor,&cache,b->costAware?pars->nDepNodesMax:-1);
        while ( b->proposals<b->budget )
        {
            status=Cec_TranDependencyIteratorNext(sim,root,b->pool,care,0,&dep,it,&cand,
                &attempt,&exhausted,NULL,&raw,&tm);
            if ( exhausted ) { ++b->exhausted; break; }
            if ( status<=0 ) continue;
            if ( b->costAware )
            {
                int nNew, ActualGain=Cec_TranTbActualGain(b,&cand,&nNew);
                int fOldExcluded=cand.nGates >= root->nMffc;
                b->oldBoundExcluded += fOldExcluded;
                b->oldBoundPositive += fOldExcluded && ActualGain > 0;
                if ( fOldExcluded )
                    Abc_Print(1,"tracebuild-cost-witness root=%d raw-gates=%d old-limit=%d new-gates=%d retained=%d exact-gain=%d status=%s\n",
                        b->root,cand.nGates,root->nMffc-1,nNew,
                        root->nMffc-ActualGain-nNew,ActualGain,
                        ActualGain>0?"positive":"nonpositive");
                // The baseline never saw candidates outside its raw bound.
                // Only spend proof budget on a newly exposed candidate when
                // frozen-DAG accounting says it can have positive local gain.
                if ( fOldExcluded && ActualGain <= 0 )
                {
                    b->costRejected++;
                    Cec_TranCandRecipeRelease(&cand);
                    continue;
                }
            }
            ++b->proposals;
            Abc_Print(1,"tracebuild-proposal root=%d index=%d branch=%d clauses=%d out=%d recipe=",
                b->root,b->proposals,b->branchCount,Vec_PtrSize(b->clauses),cand.iOut);
            for ( i=0; i<2*cand.nGates; ++i ) Abc_Print(1,"%s%d",i?",":"",cand.Recipe[i]);
            Abc_Print(1,"\n");
            status=Cec_TranTbCheck(b,&cand,&clean,&cex,proofId);
            if ( status==1 && Cec_TranGain(b->p,clean)>0 )
            {
                Cec_TranFrozenHash_t hash;
                Vec_Int_t * boundary=Vec_IntAlloc(32);
                char * covered=ABC_CALLOC(char,Gia_ManObjNum(b->p));
                int nNew;
                Cec_TranFrozenHashStart(b->p,&hash);
                nNew=Cec_TranFrozenRecipeCost(b->p,&hash,&cand,covered,boundary);
                Cec_TranFrozenHashStop(&hash); ABC_FREE(covered); Vec_IntFree(boundary);
                if ( b->costAware && cand.nGates >= root->nMffc )
                    b->oldBoundProved++;
                if ( b->costAware && nNew==0 )
                    b->zeroNewProved++;
                if ( nNew>0 || b->costAware )
                {
                    b->winnerNew=nNew;
                    b->zeroNewCommits += nNew==0;
                    *winner=cand;
                    break;
                }
            }
            if ( status==1 ) { Gia_ManStop(clean); clean=NULL; }
            if ( status==0 && b->feedback )
            { Cec_TranTbLearn(b,&cand,cex); changed=1; }
            Cec_TranCandRecipeRelease(&cand);
            if ( changed ) break;
        }
        Abc_ResubIteratorResumeStop(it,cursor); if ( cache ) Abc_ResubRootCacheStop(cache);
        Cec_TranDepScratchStop(&dep); Abc_ResubPrepareManager(0); Cec_TranSimStop(sim); ABC_FREE(care);
        if ( changed ) Vec_PtrPush(b->work,branch); else Cec_TranTbBranchFree(branch);
        if ( clean ) return clean;
    }
    return NULL;
}

static Gia_Man_t * Cec_TranTbCutSearch( Cec_TranTb_t * b,
    Cec_ParTran_t * pPars, Cec_TranRoot_t * pRoot, Cec_TranSim_t * pSim,
    Cec_TranCand_t * pWinner, int * pProofId )
{
    Cec_TranCand_t Best={0};
    Vec_Ptr_t * vCuts=Cec_TranTbCuts(b,pRoot->iObj);
    Vec_Int_t * vCut;
    Gia_Man_t * pClean=NULL;
    Abc_Cex_t * pCex;
    int c,fBdc,HaveBest=0,BestNew=0,Status;
    int nCuts=b->cutMulti?Vec_PtrSize(vCuts):Abc_MinInt(2,Vec_PtrSize(vCuts));
    b->cutViews=nCuts-1;
    Gia_ObjComputeTruthTableStart(b->p,4);
    for ( c=1; c<nCuts; ++c )
    {
        word Truth;
        vCut=(Vec_Int_t *)Vec_PtrEntry(vCuts,c);
        if ( Vec_IntSize(vCut)==0 || Vec_IntSize(vCut)>4 ) continue;
        Truth=*Gia_ObjComputeTruthTableCut(b->p,
            Gia_ManObj(b->p,pRoot->iObj),vCut);
        for ( fBdc=0; fBdc<=pPars->fBdcPortfolio; ++fBdc )
        {
            Cec_TranCand_t Cand;
            int nNew,Gain;
            if ( !Cec_TranTbCutCandidate(pRoot,vCut,Truth,fBdc,&Cand) )
                continue;
            if ( fBdc ) b->cutBdc++; else b->cutKit++;
            if ( Cand.nGates>pPars->nDepNodesMax ||
                 !Cec_TranRecipeStructurallyValid(pSim,&Cand) ||
                 !Cec_TranRecipeMatchesRoot(pSim,&Cand,NULL) )
            { Cec_TranCandRecipeRelease(&Cand); continue; }
            Gain=Cec_TranTbActualGain(b,&Cand,&nNew);
            b->cutRawGates+=Cand.nGates; b->cutNewGates+=nNew;
            b->cutOldBoundExcluded += Cand.nGates>=pRoot->nMffc;
            if ( Gain<=0 ) { Cec_TranCandRecipeRelease(&Cand); continue; }
            b->cutPositive++;
            b->cutOldBoundPositive += Cand.nGates>=pRoot->nMffc;
            Cand.Gain=Cand.nDiscoveryGain=Gain;
            Abc_Print(1,"tracebuild-cut-candidate root=%d cut=%d leaves=%d constructor=%s raw-gates=%d old-limit=%d new-gates=%d exact-gain=%d truth=%016llx support=",
                b->root,c,Vec_IntSize(vCut),fBdc?"bdc":"kit",
                Cand.nGates,pRoot->nMffc-1,nNew,Gain,
                (unsigned long long)Truth);
            {
                int j,iLeaf;
                Vec_IntForEachEntry(vCut,iLeaf,j)
                    Abc_Print(1,"%s%d",j?",":"",iLeaf);
                Abc_Print(1,"\n");
            }
            if ( !HaveBest || Gain>Best.Gain ||
                 (Gain==Best.Gain && nNew<BestNew) ||
                 (Gain==Best.Gain && nNew==BestNew && Cand.nGates<Best.nGates) )
            {
                if ( HaveBest ) Cec_TranCandRecipeRelease(&Best);
                Best=Cand; BestNew=nNew; HaveBest=1;
            }
            else Cec_TranCandRecipeRelease(&Cand);
        }
    }
    Vec_PtrForEachEntry(Vec_Int_t *,vCuts,vCut,c) Vec_IntFree(vCut);
    Vec_PtrFree(vCuts); Gia_ObjComputeTruthTableStop(b->p);
    if ( !HaveBest ) return NULL;
    b->cutProofs++;
    Status=Cec_TranTbCheck(b,&Best,&pClean,&pCex,pProofId);
    if ( Status==1 && Cec_TranGain(b->p,pClean)>0 )
    {
        b->winnerNew=BestNew;
        b->cutOldBoundProved += Best.nGates>=pRoot->nMffc;
        b->cutCommitKit=Best.fKitPortfolio;
        b->cutCommitBdc=Best.fBdcPortfolio;
        *pWinner=Best;
        return pClean;
    }
    if ( Status==1 ) Gia_ManStop(pClean);
    else if ( Status==0 )
        Abc_Print(1,"tracebuild-cut-error root=%d status=SAT strict-cut-candidate=1\n",b->root);
    Cec_TranCandRecipeRelease(&Best);
    return NULL;
}

static Gia_Man_t * Cec_TranRunTraceBuild( Gia_Man_t * p, Cec_ParTran_t * pPars )
{
    Cec_ParTran_t pars=*pPars;
    Vec_Ptr_t * bank=Vec_PtrAlloc(16);
    int round=0, commits=0, total=0, k;
    Abc_Cex_t * cex;
    pars.nRootConstrTop=(pPars->nExplore&524288)?320:pPars->nRootConstrTop;
    pars.nConstrBaseMax=(pPars->nExplore&8388608)?128:pPars->nConstrBaseMax;
    assert(pPars->nRelObs==27 && pPars->fOutputProof);
    assert(pars.nRootConstrTop>0);
    for ( ; !pPars->nOutputRounds || round < pPars->nOutputRounds; )
    {
        Cec_TranPatDb_t * db=Cec_TranPatDbStart(p,0);
        Cec_TranSim_t * sim=Cec_TranSimStart(p,&pars,db);
        Cec_TranProf_t prof={0};
        Cec_TranRoot_t * roots=ABC_ALLOC(Cec_TranRoot_t,Gia_ManAndNum(p));
        word * care=Cec_TranRelCare(sim);
        char * marked=ABC_CALLOC(char,Gia_ManObjNum(p));
        Vec_Int_t * mffc=Vec_IntAlloc(128), * tfo=Vec_IntAlloc(128);
        Gia_Man_t * next=NULL;
        Gia_Obj_t * o;
        int i,r,n=0, counts[3]={0},gains[3]={0};
        abctime start=Abc_Clock(), proof=0;
        Gia_ManCreateRefs(p); Gia_ManStaticFanoutStart(p);
        Gia_ManForEachAnd(p,o,i)
        {
            roots[n].iObj=i; roots[n].nMffc=Gia_NodeMffcSize(p,o);
            if ( roots[n].nMffc>1 ) ++n;
        }
        qsort(roots,n,sizeof(Cec_TranRoot_t),Cec_TranRootCompare);
        for ( r=0; r<n && !next; ++r )
        {
            Cec_TranTb_t b={0};
            Cec_TranCand_t winner;
            Cec_TranDivRank_t * ranks;
            Cec_TranTbBranch_t * branch;
            Vec_Int_t * clause;
            int id,rs,ws,ss,j;
            b.p=p; b.root=roots[r].iObj; b.bank=bank;
            b.outputScope=1; b.feedback=1; b.cone=1;
            b.costAware=1; b.cutAware=1; b.cutMulti=1;
            b.budget=pars.nRootConstrTop; b.branchLimit=b.budget;
            Cec_TranTbBoundary(&b,&pars);
            b.pool=Cec_TranCollectDivPool(p,b.root,pars.nConstrMax,
                Abc_MaxInt(4*pars.nConstrBaseMax,pars.nConstrBaseMax+32),pars.fUseMffcDivs,
                NULL,NULL,marked,mffc,pars.fUseTfoDivs,pars.nConstrBaseMax,tfo,NULL);
            ranks=Cec_TranRankDivReservoir(sim,b.root,b.pool,&pars,&prof,care+(size_t)b.root*sim->nSlots);
            Cec_TranSelectRankedDivPool(b.pool,ranks,pars.nConstrBaseMax,NULL);
            b.words=Abc_MaxInt(1,(Vec_IntSize(b.pool)+63)/64);
            b.patterns=Vec_WrdAlloc(128); b.clauses=Vec_PtrAlloc(32); b.work=Vec_PtrAlloc(32);
            Cec_TranFrozenHashStart(p,&b.frozenHash);
            b.costRefs=Cec_TranMffcRefsStart(p,NULL);
            b.costMffcMark=ABC_CALLOC(char,Gia_ManObjNum(p));
            b.costMffc=Vec_IntAlloc(128);
            b.costBoundary=Vec_IntAlloc(32);
            Abc_Print(1,"tracebuild-root round=%d root=%d mffc=%d mode=%d boundary=%s B=%d q=%d N=%d branch-limit=%d pending-limit=%d pool=",
                round,b.root,roots[r].nMffc,pPars->nRelObs,b.outputScope?"output":"window",pars.nConstrBaseMax,b.budget,pars.nDepNodesMax,b.branchLimit,b.budget);
            Vec_IntForEachEntry(b.pool,i,j) Abc_Print(1,"%s%d",j?",":"",i);
            Abc_Print(1,"\n");
            Abc_Print(1,"tracebuild-constructor root=%d kind=native-iterator recipe-gate-limit=%d\n",b.root,pars.nDepNodesMax);
            if ( Vec_IntSize(b.pool) ) next=Cec_TranTbSearch(&b,&pars,roots+r,&winner,&id);
            if ( !next && !b.direct )
                next=Cec_TranTbCutSearch(&b,&pars,roots+r,sim,&winner,&id);
            if ( next )
            {
                abctime cp=Abc_Clock();
                if ( !b.outputScope )
                {
                    Gia_Man_t * product=Gia_ManMiter(p,next,0,0,1,0,0);
                    int audit=Cec_TranRelPdr(product,"tracebuild-output-audit",NULL,NULL);
                    Gia_ManStop(product);
                    // A PO failure would contradict complete-window coverage.
                    assert(audit!=0);
                    if ( audit!=1 ) { Gia_ManStop(next); next=NULL; Cec_TranCandRecipeRelease(&winner); }
                }
                if ( next )
                {
                rs=Cec_TranRelOldProof(p,&winner,&pars,0); ws=Cec_TranRelOldProof(p,&winner,&pars,1);
                ss=Cec_TranRelStateProof(p,next); proof+=Abc_Clock()-cp;
                assert(b.outputScope || (ws!=0 && ss!=0));
                gains[2]=Cec_TranGain(p,next); counts[2]=1; total+=gains[2]; ++commits;
                Cec_TranRelDumpGia(p,id,"before"); Cec_TranRelDumpGia(next,id,"after");
                Abc_Print(1,"tracebuild-commit round=%d proof=%d root=%d gain=%d gates=%d new-gates=%d root-status=%d window-status=%d state-status=%d out=%d recipe=",
                    round,id,b.root,gains[2],winner.nGates,b.winnerNew,rs,ws,ss,winner.iOut);
                for ( i=0; i<2*winner.nGates; ++i ) Abc_Print(1,"%s%d",i?",":"",winner.Recipe[i]);
                Abc_Print(1,"\n"); Cec_TranCandRecipeRelease(&winner);
                }
            }
            Abc_Print(1,"tracebuild-search root=%d proposals=%d branches=%d exhausted=%d capped=%d proofs=%d sat=%d unknown=%d replay=%d direct-capable=%d clauses=%d patterns=%d material=%d gain=%d\n",
                b.root,b.proposals,b.branchCount,b.exhausted,b.branchCapped,b.proofs,b.sat,b.unknown,b.replay,b.direct,Vec_PtrSize(b.clauses),Vec_WrdSize(b.patterns)/b.words,Vec_IntSize(b.pool),gains[2]);
            Abc_Print(1,"tracebuild-cone root=%d enabled=%d raw-frames=%d kept-frames=%d raw-terms=%d kept-terms=%d\n",b.root,b.cone,b.rawFrames,b.coneFrames,b.rawTerms,b.coneTerms);
            Abc_Print(1,"tracebuild-cost root=%d enabled=%d evaluated=%d rejected=%d old-bound-excluded=%d old-bound-positive=%d old-bound-proved=%d zero-new-proved=%d zero-new-commits=%d raw-gates=%lld new-gates=%lld\n",
                b.root,b.costAware,b.costEvaluated,b.costRejected,
                b.oldBoundExcluded,b.oldBoundPositive,b.oldBoundProved,
                b.zeroNewProved,b.zeroNewCommits,b.costRawGates,b.costNewGates);
            Abc_Print(1,"tracebuild-cut root=%d enabled=%d multi=%d views=%d capped=%d kit=%d bdc=%d positive=%d proofs=%d commit-kit=%d commit-bdc=%d old-bound-excluded=%d old-bound-positive=%d old-bound-proved=%d raw-gates=%lld new-gates=%lld\n",
                b.root,b.cutAware,b.cutMulti,b.cutViews,b.cutCapped,b.cutKit,b.cutBdc,
                b.cutPositive,b.cutProofs,b.cutCommitKit,b.cutCommitBdc,
                b.cutOldBoundExcluded,b.cutOldBoundPositive,b.cutOldBoundProved,
                b.cutRawGates,b.cutNewGates);
            proof+=b.proofTime;
            Vec_PtrForEachEntry(Vec_Int_t *,b.clauses,clause,i) Vec_IntFree(clause);
            Vec_PtrForEachEntry(Cec_TranTbBranch_t *,b.work,branch,i) Cec_TranTbBranchFree(branch);
            Vec_PtrFree(b.clauses); Vec_PtrFree(b.work); Vec_WrdFree(b.patterns); Vec_IntFree(b.pool); ABC_FREE(ranks);
            Cec_TranFrozenHashStop(&b.frozenHash);
            ABC_FREE(b.costRefs); ABC_FREE(b.costMffcMark);
            Vec_IntFree(b.costMffc); Vec_IntFree(b.costBoundary);
            if ( !b.outputScope ) Gia_ManStop(b.observedSource);
            Vec_IntFree(b.observations);
        }
        Cec_TranRelCommitProfile(Gia_ManAndNum(p),next?Gia_ManAndNum(next):Gia_ManAndNum(p),Gia_ManRegNum(p),counts,gains,
            Cec_TranTimeSec(Abc_Clock()-start),Cec_TranTimeSec(proof));
        Vec_IntFree(mffc); Vec_IntFree(tfo); ABC_FREE(marked); ABC_FREE(care); ABC_FREE(roots);
        Cec_TranSimStop(sim); Cec_TranPatDbStop(db); Gia_ManStaticFanoutStop(p); ABC_FREE(p->pRefs);
        if ( !next ) break;
        Gia_ManStop(p); p=next; ++round;
    }
    Vec_PtrForEachEntry(Abc_Cex_t *,bank,cex,k) Abc_CexFree(cex);
    Vec_PtrFree(bank);
    Abc_Print(1,"tracebuild-summary mode=27 boundary=output commits=%d gain=%d\n",commits,total);
    return p;
}

static int Cec_TranTraceBuildSelfTest()
{
    Cec_TranTb_t b={0};
    Cec_ParTran_t pars;
    Cec_TranCand_t winner;
    Cec_TranRoot_t root;
    Cec_TranTbBranch_t * branch;
    Gia_Man_t * result;
    Vec_Int_t * clause;
    Abc_Cex_t * cex;
    int i,j,id;
    // Exhaustive disjoint-cover check of the clause-to-on/off adapter.
    int seen[8]={0};
    b.budget=320; b.words=1; b.patterns=Vec_WrdStart(3);
    b.work=Vec_PtrAlloc(8); b.clauses=Vec_PtrAlloc(8);
    clause=Vec_IntAlloc(2); Vec_IntPush(clause,0); Vec_IntPush(clause,3); Vec_PtrPush(b.clauses,clause);
    clause=Vec_IntAlloc(2); Vec_IntPush(clause,2); Vec_IntPush(clause,5); Vec_PtrPush(b.clauses,clause);
    Vec_PtrPush(b.work,Cec_TranTbBranch(NULL,0));
    while ( (branch=Cec_TranTbReady(&b))!=NULL )
    {
        for ( i=0; i<8; ++i )
        {
            int match=1;
            for ( j=0; j<3; ++j ) if ( Vec_IntEntry(branch->values,j)>=0 && Vec_IntEntry(branch->values,j)!=((i>>j)&1) ) match=0;
            seen[i]+=match;
        }
        Cec_TranTbBranchFree(branch);
    }
    for ( i=0; i<8; ++i ) assert(seen[i]==((!(i&1)||((i>>1)&1))&&(!((i>>1)&1)||((i>>2)&1))));
    Vec_PtrForEachEntry(Vec_Int_t *,b.clauses,clause,i) Vec_IntFree(clause);
    Vec_PtrFree(b.work); Vec_PtrFree(b.clauses); Vec_WrdFree(b.patterns);
    // Exercise the production native-constructor path with complete-pool
    // temporal cone slicing and a permanently output-equivalent state fork.
    memset(&b,0,sizeof(b));
    Cec_ManTranSetDefaultParams(&pars); pars.nRootConstrTop=320;
    b.p=Cec_TranRelWitness(1,0,&b.root);
    root.iObj=b.root; root.nMffc=2;
    b.pool=Vec_IntAlloc(4); Vec_IntPush(b.pool,1); Vec_IntPush(b.pool,2); Vec_IntPush(b.pool,3);
    b.words=1; b.budget=320; b.branchLimit=320;
    b.feedback=1; b.outputScope=1; b.cone=1;
    {
        unsigned char * keep=Cec_TranTbConeFrames(&b,Gia_ObjId(b.p,Gia_ManPo(b.p,0)),4);
        assert(!keep[0] && !keep[1] && keep[2] && !keep[3]); ABC_FREE(keep);
        Vec_IntPush(b.pool,Gia_ObjId(b.p,Gia_ManRo(b.p,1)));
        keep=Cec_TranTbConeFrames(&b,Gia_ObjId(b.p,Gia_ManPo(b.p,0)),4);
        assert(keep[0] && keep[1] && keep[2] && !keep[3]); ABC_FREE(keep);
        Vec_IntPop(b.pool);
    }
    Cec_TranTbBoundary(&b,&pars);
    b.patterns=Vec_WrdAlloc(32); b.work=Vec_PtrAlloc(16); b.clauses=Vec_PtrAlloc(16); b.bank=Vec_PtrAlloc(16);
    result=Cec_TranTbSearch(&b,&pars,&root,&winner,&id);
    assert(result && winner.nGates==1 && Vec_PtrSize(b.clauses)>0);
    assert(Cec_TranRelStateProof(b.p,result)==0);
    Cec_TranRelDumpGia(b.p,20,"tracebuild-before"); Cec_TranRelDumpGia(result,20,"tracebuild-after");
    // The identical recipe must be rejected at the RI/window boundary.
    Vec_IntFree(b.observations); b.outputScope=0;
    Gia_ManStaticFanoutStart(b.p); Cec_TranTbBoundary(&b,&pars);
    {
        Gia_Man_t * unexpected;
        assert(Cec_TranTbCheck(&b,&winner,&unexpected,&cex,&id)==0);
        Cec_TranTbLearn(&b,&winner,cex);
    }
    Gia_ManStaticFanoutStop(b.p); Gia_ManStop(b.observedSource); Vec_IntFree(b.observations);
    Cec_TranCandRecipeRelease(&winner); Gia_ManStop(result); Gia_ManStop(b.p);
    Vec_PtrForEachEntry(Vec_Int_t *,b.clauses,clause,i) Vec_IntFree(clause);
    Vec_PtrForEachEntry(Cec_TranTbBranch_t *,b.work,branch,i) Cec_TranTbBranchFree(branch);
    Vec_PtrForEachEntry(Abc_Cex_t *,b.bank,cex,i) Abc_CexFree(cex);
    Vec_PtrFree(b.work); Vec_PtrFree(b.clauses); Vec_PtrFree(b.bank); Vec_WrdFree(b.patterns); Vec_IntFree(b.pool);
    // A raw two-gate recipe can cost one physical node because its first gate
    // already exists.  Keep that shared node alive as a replacement boundary,
    // and verify that exact gain (2 removed - 1 new) is positive even though
    // the old raw gate limit nMffc-1 would exclude the recipe.
    {
        Cec_TranFrozenHash_t hash;
        Cec_TranCand_t cand;
        Vec_Int_t * vMffc=Vec_IntAlloc(8), * vBoundary=Vec_IntAlloc(8);
        char * pMffc;
        int * pRefs;
        int a,bLit,c,x,t,rootId,nNew,gain;
        Gia_Man_t * p=Gia_ManStart(16);
        p->pName=Abc_UtilStrsav("tracebuild_actual_cost_witness");
        a=Gia_ManAppendCi(p); bLit=Gia_ManAppendCi(p); c=Gia_ManAppendCi(p);
        Gia_ManHashAlloc(p);
        x=Gia_ManHashAnd(p,a,bLit);
        t=Gia_ManHashAnd(p,a,c);
        rootId=Abc_Lit2Var(Gia_ManHashAnd(p,t,bLit));
        Gia_ManAppendCo(p,x); Gia_ManAppendCo(p,Abc_Var2Lit(rootId,0));
        Gia_ManHashStop(p); Gia_ManSetRegNum(p,0); Gia_ManCreateRefs(p);
        memset(&cand,0,sizeof(cand));
        cand.iTarget=rootId; cand.iDiv0=a; cand.iDiv1=bLit;
        cand.nMffc=2; cand.nKind=CEC_TRAN_CAND_CONSTR; cand.nGates=2;
        cand.Recipe=Cec_TranRecipeAlloc(4);
        cand.Recipe[0]=a; cand.Recipe[1]=bLit;
        cand.Recipe[2]=Cec_TranRecipeGateCode(0,0); cand.Recipe[3]=c;
        cand.iOut=Cec_TranRecipeGateCode(1,0);
        Cec_TranFrozenHashStart(p,&hash);
        pRefs=Cec_TranMffcRefsStart(p,NULL);
        pMffc=ABC_CALLOC(char,Gia_ManObjNum(p));
        nNew=Cec_TranFrozenRecipeCost(p,&hash,&cand,NULL,vBoundary);
        gain=Cec_TranCandFrozenGainWithRefs(p,&hash,&cand,NULL,NULL,pRefs,
            pMffc,vMffc,vBoundary);
        assert(cand.nGates >= cand.nMffc && nNew==1 && gain==1);
        // Exercise the discovery helper and the downstream pre-proof filter.
        // The shared-node recipe must survive only in actual-cost mode.
        {
            Cec_TranCandVec_t Candidates={0}, Frontier={0};
            Cec_TranRoot_t Root={0};
            Cec_TranProf_t * Prof=ABC_CALLOC(Cec_TranProf_t,1);
            char * Covered=ABC_CALLOC(char,Gia_ManObjNum(p));
            char * Used=ABC_CALLOC(char,Gia_ManObjNum(p));
            int nMffc=-1;
            assert(Cec_TranQualityCostGainOne(p,&cand,NULL,NULL,&nMffc)==1);
            assert(nMffc==2);
            Root.iObj=rootId; Root.nMffc=2;
            cand.nStatus=CEC_TRAN_STATE_CANDIDATE;
            Cec_TranCandVecPush(&Candidates,cand);
            Cec_TranRootPrepareSeqFrontier(p,&Root,1,&Candidates,Covered,
                Used,pMffc,vMffc,vBoundary,0,&Frontier,Prof);
            assert(Frontier.nSize==(Cec_TranQualityActualCost()?1:0));
            if(Frontier.nSize) assert(Frontier.pArray[0].Gain==1);
            Cec_TranCandVecStop(&Candidates); Cec_TranCandVecStop(&Frontier);
            ABC_FREE(Covered); ABC_FREE(Used); ABC_FREE(Prof);
        }
        // Exercise actual native discovery, not just the manual cost witness.
        // The shared a&b node is deliberately absent from the iterator pool:
        // with it present, a one-raw-gate recipe could hide the old bound bug.
        // This tests fixed-support discovery, not novelty versus other pools.
        {
            Cec_TranSim_t Sim={0};
            Cec_TranDepScratch_t Dep;
            Cec_TranRoot_t Root={0};
            Cec_ParTran_t Pars;
            Vec_Int_t * vPool=Vec_IntAlloc(3);
            Gia_Obj_t * pObj;
            int Mode,Obj,Found[4]={0},Positive[4]={0};
            Cec_ManTranSetDefaultParams(&Pars);
            Pars.fUseConstr=1; Pars.nDepNodesMax=2;
            Root.iObj=rootId; Root.nMffc=Gia_NodeMffcSize(p,Gia_ManObj(p,rootId));
            assert(Root.nMffc==2);
            assert(Cec_TranDependencyGateLimit(&Pars,&Root,-1)==1);
            assert(Cec_TranDependencyGateLimit(&Pars,&Root,-2)==0);
            assert(Cec_TranDependencyGateLimit(&Pars,&Root,0)==0);
            assert(Cec_TranDependencyGateLimit(&Pars,&Root,1)==1);
            assert(Cec_TranDependencyGateLimit(&Pars,&Root,2)==2);
            assert(Cec_TranDependencyGateLimit(&Pars,&Root,100)==2);
            Pars.fUseConstr=0;
            assert(Cec_TranDependencyGateLimit(&Pars,&Root,2)==0);
            Pars.fUseConstr=1;
            Sim.pGia=p; Sim.nSlots=Sim.nWords=Sim.nFrames=1;
            Sim.pSims=ABC_CALLOC(word,Gia_ManObjNum(p));
            Cec_TranSimObj(&Sim,Abc_Lit2Var(a))[0]=ABC_CONST(0xaaaaaaaaaaaaaaaa);
            Cec_TranSimObj(&Sim,Abc_Lit2Var(bLit))[0]=ABC_CONST(0xcccccccccccccccc);
            Cec_TranSimObj(&Sim,Abc_Lit2Var(c))[0]=ABC_CONST(0xf0f0f0f0f0f0f0f0);
            Gia_ManForEachAnd(p,pObj,Obj)
                Cec_TranSimObj(&Sim,Obj)[0]=
                    Cec_TranSimLit(&Sim,Gia_ObjFaninLit0p(p,pObj),0) &
                    Cec_TranSimLit(&Sim,Gia_ObjFaninLit1p(p,pObj),0);
            Vec_IntPush(vPool,Abc_Lit2Var(a));
            Vec_IntPush(vPool,Abc_Lit2Var(bLit));
            Vec_IntPush(vPool,Abc_Lit2Var(c));
            assert(Vec_IntFind(vPool,Abc_Lit2Var(x))<0);
            Cec_TranDepScratchStart(&Dep,1,Vec_IntSize(vPool),1);
            Abc_ResubPrepareManager(1);
            for ( Mode=0; Mode<4; ++Mode )
            {
                int Cursor[6]={0},Exhausted=0,Attempt,Raw,Status,Calls=0;
                void * Cache=NULL,* Iter;
                abctime Time=0;
                Cec_TranCand_t Native;
                // Default and explicit one-gate modes must remain equal;
                // budget 100 must still be capped by the user's N=2.
                Iter=Mode==0 ? Cec_TranDependencyIteratorStart(&Sim,&Pars,
                    &Root,vPool,NULL,&Dep,Cursor,&Cache) :
                    Cec_TranDependencyIteratorStartWithRawBudget(&Sim,&Pars,
                        &Root,vPool,NULL,&Dep,Cursor,&Cache,Mode==3?100:Mode);
                while ( !Exhausted )
                {
                    assert(++Calls<64);
                    Status=Cec_TranDependencyIteratorNext(&Sim,&Root,vPool,
                        NULL,1,&Dep,Iter,&Native,&Attempt,&Exhausted,NULL,&Raw,&Time);
                    if ( Status<=0 ) continue;
                    assert(Native.nGates<=Pars.nDepNodesMax);
                    assert(Cec_TranRecipeMatchesRoot(&Sim,&Native,NULL));
                    ++Found[Mode];
                    if ( Native.nGates>=Root.nMffc )
                    {
                        Vec_IntClear(vBoundary);
                        nNew=Cec_TranFrozenRecipeCost(p,&hash,&Native,NULL,vBoundary);
                        gain=Cec_TranCandFrozenGainWithRefs(p,&hash,&Native,
                            NULL,NULL,pRefs,pMffc,vMffc,vBoundary);
                        if ( gain>0 )
                        {
                            assert(nNew==1 && gain==1);
                            ++Positive[Mode];
                        }
                    }
                    Cec_TranCandRecipeRelease(&Native);
                }
                Abc_ResubIteratorResumeStop(Iter,Cursor);
                if ( Cache ) Abc_ResubRootCacheStop(Cache);
                assert(Root.nMffc==2);
            }
            assert(Found[0]==0 && Found[1]==0);
            assert(Positive[2]>0 && Positive[2]==Positive[3]);
            assert(Found[2]==Found[3]);
            // Use the real candidate collector, including its cost gate.
            {
                Cec_TranCandVec_t Empty={0}, Build={0};
                Cec_TranRootCursor_t Cursor={0};
                Cec_TranDiscStat_t Stat={0};
                Cec_TranProf_t * Prof=ABC_CALLOC(Cec_TranProf_t,1);
                Cec_TranDivRank_t Ranks[3];
                int k;
                memset(Ranks,0,sizeof(Ranks));
                for(k=0;k<3;k++) Ranks[k].iPos=k;
                Pars.nRootConstrTop=Pars.nRootProofBatch=0;
                Cec_TranCollectRootConstructedIter(p,&Sim,&Pars,&Root,&Cursor,
                    0,&Empty,NULL,NULL,pMffc,vMffc,vPool,NULL,1,Ranks,
                    &Empty,&Build,&Dep,&Stat,Prof);
                assert((Build.nSize>0)==Cec_TranQualityActualCost());
                for(k=0;k<Build.nSize;k++) assert(Build.pArray[k].Gain>0);
                Cec_TranCandVecStop(&Build);
                Cec_TranRootCursorCacheStop(&Cursor);
                ABC_FREE(Prof);
                Abc_Print(1,"stran-quality-native-cost-selftest: PASS actual=%d discovery-and-frontier=1\n",Cec_TranQualityActualCost());
            }
            Abc_ResubPrepareManager(0);
            Cec_TranDepScratchStop(&Dep);
            Vec_IntFree(vPool); ABC_FREE(Sim.pSims);
            Abc_Print(1,"tracebuild-raw-budget-selftest: PASS default=1 explicit-N=2 native-over-bound-positive=%d shared-divisor-absent=1 invalid-closed=1\n",Positive[2]);
        }
        memset(&b,0,sizeof(b)); b.p=p; b.budget=320; b.cutMulti=1;
        {
            Vec_Ptr_t * vCuts=Cec_TranTbCuts(&b,rootId);
            Vec_Int_t * vCut;
            int k,found=0;
            Vec_PtrForEachEntry(Vec_Int_t *,vCuts,vCut,k)
            {
                assert(Vec_IntSize(vCut)<=4);
                found |= Vec_IntSize(vCut)==3 &&
                    Vec_IntEntry(vCut,0)==Abc_Lit2Var(a) &&
                    Vec_IntEntry(vCut,1)==Abc_Lit2Var(bLit) &&
                    Vec_IntEntry(vCut,2)==Abc_Lit2Var(c);
                Vec_IntFree(vCut);
            }
            assert(found && Vec_PtrSize(vCuts)>=3 && !b.cutCapped);
            Vec_PtrFree(vCuts);
        }
        Cec_TranFrozenHashStop(&hash); Cec_TranCandRecipeRelease(&cand);
        ABC_FREE(pRefs); ABC_FREE(pMffc); Vec_IntFree(vMffc);
        Vec_IntFree(vBoundary); Gia_ManStop(p);
    }
    Abc_Print(1,"tracebuild-selftest disjoint clauses, native temporal-cone construction, structural cuts and actual-cost bound PASS\n");
    return 1;
}
