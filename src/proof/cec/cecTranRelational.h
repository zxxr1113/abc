// ODC candidate relations as explicit k-inductive predicates.
// Unlike speculative node replacement, the unrolling contains the original
// transition function at every frame.  A SAT assignment can remove only the
// queried relation; it never partitions unrelated endpoints into classes.
// This is the standard conjunctive invariant (Houdini) fixed point, not a
// bounded-model-checking proof and not a retry of a failed correspondence run.

static int Cec_TranRelationalMode( Cec_ParTran_t const * pPars )
{
    char const * s = getenv("ABC_ODC_RELATIONAL_PROOF");
    if ( !s ) return pPars->fRoute1;
    if ( !strcmp(s, "0") ) return 0;
    if ( !strcmp(s, "1") ) return 1;
    if ( !strcmp(s, "2") ) return 2; // observe both, consume legacy status
    Abc_Print( -1, "stran-quality-invalid-option: ABC_ODC_RELATIONAL_PROOF must be 0, 1 or 2\n" );
    exit( 2 );
    return 0;
}

typedef struct Cec_TranRelUnroll_t_ {
    Gia_Man_t * p;
    Vec_Int_t * vQueries; // frame-major XOR(root, recipe)
    sat_solver * pSat;
    int nRelations;
    int nFrames;
} Cec_TranRelUnroll_t;

static void Cec_TranRelClause( sat_solver * pSat, int * pLits, int nLits )
{
    // Do not put the insertion inside assert: NDEBUG must preserve semantics.
    int ok = sat_solver_addclause( pSat, pLits, pLits + nLits );
    assert( ok );
    if ( !ok ) abort(); // only acyclic gate definitions are added
}

static Cec_TranRelUnroll_t Cec_TranRelUnroll( Gia_Man_t * p,
    Vec_Int_t * vPairs, int nFrames, int fReset )
{
    Cec_TranRelUnroll_t u;
    Gia_Obj_t * o;
    int * old = ABC_CALLOC( int, Gia_ManObjNum(p) );
    int * cur = ABC_CALLOC( int, Gia_ManObjNum(p) );
    int f, i, a, b, q, z, clause[3], x, y;
    assert( nFrames > 0 && !(Vec_IntSize(vPairs) & 1) );
    memset( &u, 0, sizeof(u) );
    u.nRelations = Vec_IntSize(vPairs) / 2;
    u.nFrames = nFrames;
    u.vQueries = Vec_IntAlloc( 0 );
    u.p = Gia_ManStart( Gia_ManObjNum(p) );
    Gia_ManHashStart( u.p );
    for ( f = 0; f < nFrames; f++ )
    {
        int * tmp;
        cur[0] = 0;
        Gia_ManForEachPi( p, o, i )
            cur[Gia_ObjId(p,o)] = Gia_ManAppendCi( u.p );
        Gia_ManForEachRo( p, o, i )
            cur[Gia_ObjId(p,o)] = f ? old[Gia_ObjId(p,Gia_ManRi(p,i))] :
                fReset ? 0 : Gia_ManAppendCi( u.p );
        Gia_ManForEachObj1( p, o, i )
        {
            if ( Gia_ObjIsCi(o) ) continue;
            a = Abc_LitNotCond( cur[Gia_ObjFaninId0p(p,o)], Gia_ObjFaninC0(o) );
            if ( Gia_ObjIsCo(o) || Gia_ObjIsBuf(o) ) cur[i] = a;
            else
            {
                b = Abc_LitNotCond( cur[Gia_ObjFaninId1p(p,o)], Gia_ObjFaninC1(o) );
                cur[i] = Cec_TranHashGate( u.p, o, a, b );
            }
        }
        for ( i = 0; i < u.nRelations; i++ )
        {
            a = Vec_IntEntry(vPairs,2*i); b = Vec_IntEntry(vPairs,2*i+1);
            a = Abc_LitNotCond(cur[Abc_Lit2Var(a)], Abc_LitIsCompl(a));
            b = Abc_LitNotCond(cur[Abc_Lit2Var(b)], Abc_LitIsCompl(b));
            q = Gia_ManHashXor(u.p,a,b);
            Vec_IntPush(u.vQueries,q);
        }
        tmp = old; old = cur; cur = tmp;
    }
    ABC_FREE(old); ABC_FREE(cur);
    Gia_ManHashStop(u.p);
    u.pSat = sat_solver_new();
    sat_solver_setnvars(u.pSat,Gia_ManObjNum(u.p));
    clause[0] = 1; Cec_TranRelClause(u.pSat,clause,1); // false constant
    Gia_ManForEachAnd(u.p,o,i)
    {
        a=Gia_ObjFaninLit0p(u.p,o); b=Gia_ObjFaninLit1p(u.p,o);
        z=Abc_Var2Lit(i,0);
        if ( Gia_ObjIsXor(o) )
            for ( x=0; x<2; x++ ) for ( y=0; y<2; y++ )
            {
                clause[0]=a^x; clause[1]=b^y; clause[2]=z^(1^x^y);
                Cec_TranRelClause(u.pSat,clause,3);
            }
        else
        {
            clause[0]=z^1; clause[1]=a; Cec_TranRelClause(u.pSat,clause,2);
            clause[0]=z^1; clause[1]=b; Cec_TranRelClause(u.pSat,clause,2);
            clause[0]=z; clause[1]=a^1; clause[2]=b^1;
            Cec_TranRelClause(u.pSat,clause,3);
        }
    }
    return u;
}

static void Cec_TranRelUnrollStop( Cec_TranRelUnroll_t * u )
{
    sat_solver_delete(u->pSat);
    Vec_IntFree(u->vQueries);
    Gia_ManStop(u->p);
}

// Result: 1 proved, 0 refuted by base/induction, -1 solver budget unknown.
// Induction SAT is NOT a reachable counterexample and is never fed to Guide.
static Vec_Int_t * Cec_TranRelationalProve( Gia_Man_t * p,
    Vec_Int_t * vPairs, Cec_ParTran_t * pPars, int * pnRounds )
{
    int n = Vec_IntSize(vPairs)/2, k = pPars->nFrames;
    Vec_Int_t * vStatus = Vec_IntStartFull(n);
    Cec_TranRelUnroll_t base, ind;
    int i, f, q, status, changed=1, rounds=0, alive=0, incomplete=0;
    int baseSat=0, baseUnknown=0, indSat=0, indUnknown=0;
    long long baseQueries=0, indQueries=0;
    abctime clk = Abc_Clock();
    assert(k > 0);
    base = Cec_TranRelUnroll(p,vPairs,k,1);
    for ( i=0; i<n; i++ )
    {
        Vec_IntWriteEntry(vStatus,i,1);
        for ( f=0; f<k; f++ )
        {
            q = Vec_IntEntry(base.vQueries,f*n+i);
            baseQueries++;
            status = sat_solver_solve(base.pSat,&q,&q+1,pPars->nBTLimit,0,0,0);
            if ( status == l_False ) continue;
            Vec_IntWriteEntry(vStatus,i,status==l_True ? 0 : -1);
            baseSat += status==l_True; baseUnknown += status==l_Undef;
            break;
        }
        alive += Vec_IntEntry(vStatus,i)==1;
    }
    Cec_TranRelUnrollStop(&base);
    ind = Cec_TranRelUnroll(p,vPairs,k+1,0);
    // A removed hypothesis invalidates earlier UNSAT answers in that round.
    // Recheck every surviving obligation until a complete unchanged round.
    // Assumptions, not permanent clauses, allow hypotheses to be withdrawn.
    while ( pPars->nStepsMax < 0 || rounds < pPars->nStepsMax )
    {
        int guard, clause[2];
        changed=0; rounds++;
        guard = Abc_Var2Lit(sat_solver_nvars(ind.pSat),0);
        sat_solver_setnvars(ind.pSat,sat_solver_nvars(ind.pSat)+1);
        // One fresh round activation represents the entire current conjunction.
        // Old activations are unassumed and can be false.  No removed predicate
        // remains a permanent hypothesis, and each SAT query has two literals.
        for ( f=0; f<k; f++ ) for ( i=0; i<n; i++ )
            if ( Vec_IntEntry(vStatus,i)==1 )
            {
                clause[0]=guard^1;
                clause[1]=Abc_LitNot(Vec_IntEntry(ind.vQueries,f*n+i));
                Cec_TranRelClause(ind.pSat,clause,2);
            }
        for ( i=0; i<n; i++ )
        {
            int assumptions[2];
            if ( Vec_IntEntry(vStatus,i)!=1 ) continue;
            assumptions[0]=guard;
            assumptions[1]=Vec_IntEntry(ind.vQueries,k*n+i);
            indQueries++;
            status = sat_solver_solve(ind.pSat,assumptions,assumptions+2,
                pPars->nBTLimit,0,0,0);
            if ( status==l_False ) continue;
            Vec_IntWriteEntry(vStatus,i,status==l_True ? 0 : -1);
            indSat += status==l_True; indUnknown += status==l_Undef;
            changed=1; alive--;
        }
        if ( !changed || !alive ) break;
    }
    // A base certificate or a partial induction round is never a proof.
    // Preserve the caller's explicit step budget even in the research lane.
    if ( changed && alive )
    {
        incomplete=alive;
        for(i=0;i<n;i++) if(Vec_IntEntry(vStatus,i)==1)
            Vec_IntWriteEntry(vStatus,i,-1);
        alive=0;
    }
    assert(rounds <= n+1);
    Abc_Print(1,"stran-root relational-proof: schema=1 depth=%d relations=%d proved=%d rounds=%d base-queries=%lld base-sat=%d base-unknown=%d ind-queries=%lld ind-sat=%d ind-unknown=%d incomplete=%d seconds=%.6f\n",
        k,n,alive,rounds,baseQueries,baseSat,baseUnknown,indQueries,indSat,indUnknown,incomplete,
        (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    Cec_TranRelUnrollStop(&ind);
    *pnRounds=rounds;
    return vStatus;
}

// These two definitions follow this private fragment in cecTrans.c.  The
// diagnostic uses the real prepared proof wrapper and bundle cleanup, while
// leaving discovery, proof inputs and all production defaults unchanged.
static Vec_Int_t * Cec_TranProveRootBatch( Gia_Man_t * p,
    Cec_TranCand_t const * pHelpers, int nHelpers,
    Cec_TranCand_t const * pCands, int nCands, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, int fCombOnly, Vec_Str_t ** pvStage );
static Gia_Man_t * Cec_TranDupRootBundle( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, Vec_Int_t * vSelected );

// Independent scalar evaluator for the small, PI-free diagnostic graphs.
// It enumerates original free states; no SAT model or simulation row is used.
static int Cec_TranRelStrongRootEval( Gia_Man_t * p, int State, int * Values )
{
    Gia_Obj_t * o;
    int i, a, b, Next = 0;
    assert(Gia_ManPiNum(p)==0 && Gia_ManRegNum(p)==4);
    Values[0]=0;
    Gia_ManForEachCi(p,o,i) Values[Gia_ObjId(p,o)]=(State>>i)&1;
    Gia_ManForEachObj1(p,o,i)
    {
        if ( Gia_ObjIsCi(o) ) continue;
        a=Values[Gia_ObjFaninId0p(p,o)]^Gia_ObjFaninC0(o);
        if ( Gia_ObjIsCo(o) || Gia_ObjIsBuf(o) ) Values[i]=a;
        else
        {
            b=Values[Gia_ObjFaninId1p(p,o)]^Gia_ObjFaninC1(o);
            assert(!Gia_ObjIsMux(p,o));
            Values[i]=Gia_ObjIsXor(o) ? a^b : a&b;
        }
    }
    Gia_ManForEachRi(p,o,i) Next |= Values[Gia_ObjId(p,o)]<<i;
    return Next;
}

// Exact F1 conjunctive-induction oracle over all 16 original states.  This
// does not claim completeness for reachability: weak P is reachable-valid
// in both examples but cannot be established by the supplied F1 predicate
// set.  SAT/refuted induction predicates therefore are not reset teachers.
static void Cec_TranRelStrongRootOracle( Gia_Man_t * p,
    Vec_Int_t * vPairs, Vec_Int_t * vStatus )
{
    int * Values=ABC_ALLOC(int,Gia_ManObjNum(p));
    int Truth[16], Next[16], Alive, Prev, State, i, a, b, n;
    n=Vec_IntSize(vPairs)/2; assert(n>0 && n<8);
    for ( State=0; State<16; State++ )
    {
        Truth[State]=0;
        Next[State]=Cec_TranRelStrongRootEval(p,State,Values);
        for ( i=0; i<n; i++ )
        {
            a=Vec_IntEntry(vPairs,2*i); b=Vec_IntEntry(vPairs,2*i+1);
            a=Values[Abc_Lit2Var(a)]^Abc_LitIsCompl(a);
            b=Values[Abc_Lit2Var(b)]^Abc_LitIsCompl(b);
            if ( a==b ) Truth[State] |= 1<<i;
        }
    }
    Alive=Truth[0];
    do {
        Prev=Alive;
        for ( State=0; State<16; State++ )
            if ( (Truth[State]&Prev)==Prev ) Alive &= Truth[Next[State]];
    } while ( Alive!=Prev );
    assert(Vec_IntSize(vStatus)==n);
    for ( i=0; i<n; i++ ) assert(Vec_IntEntry(vStatus,i)==((Alive>>i)&1));
    ABC_FREE(Values);
}

static int Cec_TranRelStrongRootSelfTest()
{
    Cec_ParTran_t Pars;
    Cec_TranProf_t Prof;
    Cec_TranCand_t Cand, Other, Exit, Helpers[4];
    Gia_Man_t * p, * pBatch, * pDup, * pClean;
    Vec_Int_t * vPairs, * vCombPairs, * vQueries, * vStatus;
    Vec_Int_t * vSelected=Vec_IntAlloc(1);
    Vec_Str_t * vStage;
    char * SavedEnv=getenv("ABC_ODC_RELATIONAL_PROOF") ?
        Abc_UtilStrsav(getenv("ABC_ODC_RELATIONAL_PROOF")) : NULL;
    int * Values, * NewValues;
    int a, b, c, q, t, r, y, Swap, Arm, State, Next, rounds, i;
    int Seen, RootDiff, ExitDiff, Expected;
    if ( setenv("ABC_ODC_RELATIONAL_PROOF","1",1) ) abort();
    Cec_ManTranSetDefaultParams(&Pars);
    Pars.fOdcFanout=Pars.fOdcProofScope=1;
    Pars.nFrames=1; Pars.nBTLimit=Pars.nCombBTLimit=1000;
    Pars.nStepsMax=-1;
    for ( Swap=0; Swap<2; Swap++ )
    {
        // Source: r=(a&b)&c, y=r&q.  Proposed fresh Build h=a&c costs
        // one AND instead of r's two-AND MFFC.  D=q is nonconstant.
        // Identity a/b/c: root R is inductive, but masked P alone is not.
        // Swap a/b: R alone is not inductive; same-graph Strict alternative
        // H:r=b&c closes the conjunction.  All registers reset to zero.
        p=Gia_ManStart(32);
        a=Gia_ManAppendCi(p); b=Gia_ManAppendCi(p);
        c=Gia_ManAppendCi(p); q=Gia_ManAppendCi(p);
        t=Gia_ManAppendAnd(p,a,b);
        r=Gia_ManAppendAnd(p,t,c); y=Gia_ManAppendAnd(p,r,q);
        Gia_ManAppendCo(p,y);
        Gia_ManAppendCo(p,Swap ? b : a);
        Gia_ManAppendCo(p,Swap ? a : b);
        Gia_ManAppendCo(p,c); Gia_ManAppendCo(p,q^1);
        Gia_ManSetRegNum(p,4); Gia_ManCreateRefs(p);
        assert(Gia_NodeMffcSize(p,Gia_ManObj(p,Abc_Lit2Var(r)))==2);
        Cand=Cec_TranCandCreateLiteral(Abc_Lit2Var(r),a,2,CEC_TRAN_CAND_CONSTR,0);
        Cand.nGates=1; Cand.Recipe=Cec_TranRecipeAlloc(2);
        Cand.Recipe[0]=a; Cand.Recipe[1]=c;
        Cand.iDiv1=c; Cand.iOut=Cec_TranRecipeGateCode(0,0); Cand.Gain=1;
        Other=Cec_TranCandCreateLiteral(Abc_Lit2Var(r),b,2,CEC_TRAN_CAND_CONSTR,0);
        Other.nGates=1; Other.Recipe=Cec_TranRecipeAlloc(2);
        Other.Recipe[0]=b; Other.Recipe[1]=c;
        Other.iDiv1=c; Other.iOut=Cec_TranRecipeGateCode(0,0); Other.Gain=1;
        Exit=Cec_TranCandCreateLiteral(Abc_Lit2Var(y),a,3,CEC_TRAN_CAND_CONSTR,0);
        Exit.nGates=2; Exit.Recipe=Cec_TranRecipeAlloc(4);
        Exit.Recipe[0]=a; Exit.Recipe[1]=c;
        Exit.Recipe[2]=Cec_TranRecipeGateCode(0,0); Exit.Recipe[3]=q;
        Exit.iOut=Cec_TranRecipeGateCode(1,0);
        Helpers[0]=Cand; Helpers[1]=Other; // borrowed immutable recipes
        for ( Arm=0; Arm<3; Arm++ )
        {
            Expected=Arm==2 || (Arm==1 && !Swap);
            pBatch=Cec_TranBuildRootBatch(p,Arm ? Helpers : NULL,Arm,
                &Exit,1,0,&vPairs,&vCombPairs,&vQueries,NULL,NULL);
            vStatus=Cec_TranRelationalProve(pBatch,vPairs,&Pars,&rounds);
            assert(Vec_IntEntry(vStatus,Arm)==Expected);
            Cec_TranRelStrongRootOracle(pBatch,vPairs,vStatus);
            Vec_IntFree(vStatus); Vec_IntFree(vPairs);
            Vec_IntFree(vCombPairs); Vec_IntFree(vQueries); Gia_ManStop(pBatch);
            // The actual prepared wrapper must consume only P's status;
            // auxiliary relations must neither shift nor prove the wrong edit.
            memset(&Prof,0,sizeof(Prof));
            vStatus=Cec_TranProveRootBatch(p,Arm ? Helpers : NULL,Arm,
                &Exit,1,&Pars,&Prof,0,&vStage);
            assert(Vec_IntSize(vStatus)==1 && Vec_StrSize(vStage)==1);
            assert(Vec_IntEntry(vStatus,0)==Expected);
            assert(Vec_StrEntry(vStage,0)==(Expected ? 2 : 0));
            Vec_IntFree(vStatus); Vec_StrFree(vStage);
            Abc_Print(1,"stran-root strong-helper diagnostic: schema=1 swap=%d arm=%d helper-relations=%d exit-proved=%d exact-build-gain=1 automatic-discovery=0\n",
                Swap,Arm,Arm,Expected);
        }
        // A base-invalid and an induction-invalid helper are withdrawn.
        // Surviving predicates must be rechecked to a complete fixed point.
        Helpers[2]=Cec_TranCandCreateLiteral(Abc_Lit2Var(q),1,0,CEC_TRAN_CAND_CONST,1);
        Helpers[3]=Cec_TranCandCreateLiteral(Abc_Lit2Var(q),0,0,CEC_TRAN_CAND_CONST,1);
        pBatch=Cec_TranBuildRootBatch(p,Helpers,4,&Exit,1,0,
            &vPairs,&vCombPairs,&vQueries,NULL,NULL);
        vStatus=Cec_TranRelationalProve(pBatch,vPairs,&Pars,&rounds);
        assert(rounds==2 && Vec_IntEntry(vStatus,2)==0 && Vec_IntEntry(vStatus,3)==0);
        assert(Vec_IntEntry(vStatus,0)==1 && Vec_IntEntry(vStatus,1)==1 && Vec_IntEntry(vStatus,4)==1);
        Cec_TranRelStrongRootOracle(pBatch,vPairs,vStatus); Vec_IntFree(vStatus);
        Pars.nStepsMax=1;
        vStatus=Cec_TranRelationalProve(pBatch,vPairs,&Pars,&rounds);
        assert(rounds==1 && Vec_IntEntry(vStatus,2)==0 && Vec_IntEntry(vStatus,3)==0);
        assert(Vec_IntEntry(vStatus,0)==-1 && Vec_IntEntry(vStatus,1)==-1 && Vec_IntEntry(vStatus,4)==-1);
        Vec_IntFree(vStatus); Pars.nStepsMax=0;
        vStatus=Cec_TranRelationalProve(pBatch,vPairs,&Pars,&rounds);
        assert(rounds==0 && Vec_IntEntry(vStatus,2)==0);
        for ( i=0; i<5; i++ ) if ( i!=2 ) assert(Vec_IntEntry(vStatus,i)==-1);
        Vec_IntFree(vStatus); Pars.nStepsMax=-1;
        Vec_IntFree(vPairs); Vec_IntFree(vCombPairs); Vec_IntFree(vQueries); Gia_ManStop(pBatch);
        // Only the diagnosed profitable recipe is rebuilt.  H is proof-only
        // and never enters this selection or its exact cleanup attribution.
        Vec_IntClear(vSelected); Vec_IntPush(vSelected,0);
        pDup=Cec_TranDupRootBundle(p,&Cand,vSelected);
        pClean=Cec_TranCleanupKeepRegs(pDup,NULL);
        assert(Gia_ManAndNum(p)==3 && Gia_ManAndNum(pClean)==2);
        assert(Cec_TranGain(p,pClean)==1);
        Values=ABC_ALLOC(int,Gia_ManObjNum(p));
        NewValues=ABC_ALLOC(int,Gia_ManObjNum(pClean));
        Seen=RootDiff=ExitDiff=0;
        for ( State=0; State<16; State++ )
        {
            Next=Cec_TranRelStrongRootEval(p,State,Values);
            assert(Cec_TranRelStrongRootEval(pClean,State,NewValues)==Next);
            RootDiff += Values[Abc_Lit2Var(r)] != (((State>>0)&1)&((State>>2)&1));
            ExitDiff += Values[Gia_ObjId(p,Gia_ManPo(p,0))] !=
                NewValues[Gia_ObjId(pClean,Gia_ManPo(pClean,0))];
        }
        assert(RootDiff>0 && ExitDiff>0);
        State=0;
        while ( !(Seen&(1<<State)) )
        {
            Seen |= 1<<State;
            Next=Cec_TranRelStrongRootEval(p,State,Values);
            assert(Cec_TranRelStrongRootEval(pClean,State,NewValues)==Next);
            assert(Values[Gia_ObjId(p,Gia_ManPo(p,0))]==
                NewValues[Gia_ObjId(pClean,Gia_ManPo(pClean,0))]);
            State=Next;
        }
        assert(Seen==((1<<0)|(1<<8)));
        ABC_FREE(Values); ABC_FREE(NewValues);
        Gia_ManStop(pDup); Gia_ManStop(pClean);
        Cec_TranCandRecipeRelease(&Cand); Cec_TranCandRecipeRelease(&Other);
        Cec_TranCandRecipeRelease(&Exit); Gia_ManStop(p);
    }
    Vec_IntFree(vSelected);
    if ( SavedEnv )
    {
        if ( setenv("ABC_ODC_RELATIONAL_PROOF",SavedEnv,1) ) abort();
        ABC_FREE(SavedEnv);
    }
    else if ( unsetenv("ABC_ODC_RELATIONAL_PROOF") ) abort();
    Abc_Print(1,"stran ODC strong-root/Strict-helper three-arm Build diagnostic: PASS (oracle=16-states, injection-not-discovery)\n");
    return 1;
}

static int Cec_TranRelationalSelfTest()
{
    // Mutual invariant: a'=b, b'=a, reset a=b=0.  a=0 or b=0 alone
    // is not inductive, but their conjunction is.  Add false q'=!q,
    // and a property that passes reset but fails at the next time step.
    Gia_Man_t * p=Gia_ManStart(32);
    Vec_Int_t * pairs=Vec_IntAlloc(8), * s;
    Cec_ParTran_t pars, savedPars;
    int a,b,q,x,rounds;
    Gia_ManHashStart(p);
    x=Gia_ManAppendCi(p); a=Gia_ManAppendCi(p);
    b=Gia_ManAppendCi(p); q=Gia_ManAppendCi(p);
    Gia_ManAppendCo(p,x); // independent current PI must not be reset to zero
    Gia_ManAppendCo(p,b); Gia_ManAppendCo(p,a); Gia_ManAppendCo(p,q^1);
    Gia_ManSetRegNum(p,3); Gia_ManHashStop(p);
    Vec_IntPushTwo(pairs,a,0); Vec_IntPushTwo(pairs,b,0);
    Vec_IntPushTwo(pairs,q,0); Vec_IntPushTwo(pairs,x,0);
    Cec_ManTranSetDefaultParams(&pars); pars.nFrames=1; pars.nBTLimit=1000;
    s=Cec_TranRelationalProve(p,pairs,&pars,&rounds);
    assert(Vec_IntEntry(s,0)==1 && Vec_IntEntry(s,1)==1);
    assert(Vec_IntEntry(s,2)==0 && Vec_IntEntry(s,3)==0);
    Vec_IntFree(s);
    // Reaching the step limit is not itself UNKNOWN: a complete unchanged
    // first round proves the mutual invariant even with a one-round cap.
    savedPars=pars; pars.nStepsMax=1;
    Vec_IntClear(pairs); Vec_IntPushTwo(pairs,a,0); Vec_IntPushTwo(pairs,b,0);
    s=Cec_TranRelationalProve(p,pairs,&pars,&rounds);
    assert(Vec_IntEntry(s,0)==1 && Vec_IntEntry(s,1)==1 && rounds==1);
    Vec_IntFree(s); pars=savedPars;
    Vec_IntClear(pairs); Vec_IntPushTwo(pairs,a,0);
    s=Cec_TranRelationalProve(p,pairs,&pars,&rounds);
    assert(Vec_IntEntry(s,0)==0); Vec_IntFree(s);
    Vec_IntClear(pairs); Vec_IntPushTwo(pairs,q,0); pars.nFrames=2;
    s=Cec_TranRelationalProve(p,pairs,&pars,&rounds);
    assert(Vec_IntEntry(s,0)==0); Vec_IntFree(s);
    Gia_ManStop(p);
    // Withdrawal regression: a'=b, b'=1.  Initially a=0 appears inductive
    // under b=0, but b=0 fails.  The next round must withdraw that assumption
    // and refute a=0 as well (no stale permanent hypothesis).
    p=Gia_ManStart(16); Gia_ManHashStart(p);
    a=Gia_ManAppendCi(p); b=Gia_ManAppendCi(p);
    Gia_ManAppendCo(p,b); Gia_ManAppendCo(p,1);
    Gia_ManSetRegNum(p,2); Gia_ManHashStop(p);
    Vec_IntClear(pairs); Vec_IntPushTwo(pairs,a,0); Vec_IntPushTwo(pairs,b,0);
    savedPars=pars; pars.nFrames=1; pars.nStepsMax=-1;
    s=Cec_TranRelationalProve(p,pairs,&pars,&rounds);
    assert(Vec_IntEntry(s,0)==0 && Vec_IntEntry(s,1)==0 && rounds==2);
    Vec_IntFree(s);
    // b=0 is refuted in round one; a=0 needs round two after withdrawing
    // b=0.  A capped surviving predicate has no fixed-point certificate.
    pars.nStepsMax=1;
    s=Cec_TranRelationalProve(p,pairs,&pars,&rounds);
    assert(Vec_IntEntry(s,0)==-1 && Vec_IntEntry(s,1)==0 && rounds==1);
    Vec_IntFree(s);
    // Reset base checks alone cannot establish either invariant.
    pars.nStepsMax=0;
    s=Cec_TranRelationalProve(p,pairs,&pars,&rounds);
    assert(Vec_IntEntry(s,0)==-1 && Vec_IntEntry(s,1)==-1 && rounds==0);
    Vec_IntFree(s); pars=savedPars;
    Vec_IntFree(pairs); Gia_ManStop(p);
    return Cec_TranRelStrongRootSelfTest();
}
