// Proof-only Boolean-difference factorization. Included by cecTranOdc.h.
// For each exit e(r,s), Shannon expansion gives
//   e(r,s) XOR e(h,s) = (r XOR h) AND (e(0,s) XOR e(1,s)).
// Thus ALL frozen-window exits are preserved iff (r XOR h) AND D == 0,
// where D is the OR of their Boolean differences. D depends on the window,
// not the replacement. Reconvergence is preserved by shared cofactors.
// The masked-pair representation (r AND D) = (h AND D) is equivalent and
// avoids building a per-candidate XOR for correspondence/multi-literal CBS.
// No simulation care mask or previously proved certificate is reused here.

static int Cec_TranWindowFactorCare( Gia_Man_t * p, Gia_Man_t * pNew,
    int Root, Cec_ParTran_t * pPars, int * pnNodes, int * pnEnds,
    int * pfFull )
{
    Vec_Int_t * vNodes = Vec_IntAlloc(32), * vEnds = Vec_IntAlloc(16);
    int Cof[2][CEC_TRAN_RECIPE_NODES_MAX+1];
    int overflow, i, j, k, a, side, ends, Care = 0;
    Cec_TranWindowCollect(p,Root,Cec_TranWindowDepth(pPars),
        CEC_TRAN_RECIPE_NODES_MAX-pPars->nDepNodesMax,vNodes,vEnds,&overflow);
    *pnNodes = Vec_IntSize(vNodes);
    *pnEnds = Vec_IntSize(vEnds);
    *pfFull = pPars->fOdcStrict || (pPars->nExplore & 16384) ||
        Vec_IntFind(vEnds,Root) >= 0;
    assert(*pnEnds > 0 && *pnNodes <= CEC_TRAN_RECIPE_NODES_MAX+1);
    if ( *pfFull )
        Care = 1;
    else
    {
        for ( side = 0; side < 2; side++ )
        {
            Cof[side][0] = side;
            for ( i = 1; i < Vec_IntSize(vNodes); i++ )
            {
                Gia_Obj_t * pObj = Gia_ManObj(p,Vec_IntEntry(vNodes,i));
                int Lits[2];
                assert(Gia_ObjIsAnd(pObj) && !Gia_ObjIsXor(pObj) &&
                    !Gia_ObjIsMux(p,pObj) && !Gia_ObjIsBuf(pObj));
                for ( j = 0; j < 2; j++ )
                {
                    a = j ? Gia_ObjFaninLit1p(p,pObj) : Gia_ObjFaninLit0p(p,pObj);
                    k = Vec_IntFind(vNodes,Abc_Lit2Var(a));
                    assert(k < i);
                    Lits[j] = k < 0 ? Cec_TranCopyLit(p,a) :
                        Abc_LitNotCond(Cof[side][k],Abc_LitIsCompl(a));
                }
                Cof[side][i] = Gia_ManHashAnd(pNew,Lits[0],Lits[1]);
            }
        }
        Vec_IntForEachEntry(vEnds,ends,i)
        {
            k = Vec_IntFind(vNodes,ends);
            assert(k >= 0);
            a = Gia_ManHashXor(pNew,Cof[0][k],Cof[1][k]);
            Care = Gia_ManHashOr(pNew,Care,a);
        }
    }
    Vec_IntFree(vNodes); Vec_IntFree(vEnds);
    return Care;
}

static Gia_Man_t * Cec_TranBuildWindowFactorBatch( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, int nCands, Cec_ParTran_t * pPars,
    Vec_Int_t ** pvPairs, Vec_Int_t ** pvCombPairs, Vec_Int_t ** pvQueries,
    Vec_Int_t ** pvAndLeaves, Vec_Str_t ** pvAndCounts, int * pnFull )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vPairs = Vec_IntAlloc(2*nCands);
    Vec_Int_t * vCombPairs = Vec_IntAlloc(2*nCands);
    Vec_Int_t * vQueries = Vec_IntAlloc(nCands);
    Vec_Int_t * vAndLeaves = pPars->fUseCbsMultiLit ? Vec_IntAlloc(2*nCands) : NULL;
    Vec_Str_t * vAndCounts = pPars->fUseCbsMultiLit ? Vec_StrAlloc(nCands) : NULL;
    int * pCare = ABC_FALLOC(int,Gia_ManObjNum(p));
    int * pNodes = ABC_CALLOC(int,Gia_ManObjNum(p));
    int * pEnds = ABC_CALLOC(int,Gia_ManObjNum(p));
    int * pFull = ABC_CALLOC(int,Gia_ManObjNum(p));
    int * pPiProxies = Gia_ManPiNum(p) ? ABC_FALLOC(int,2*Gia_ManPiNum(p)) : NULL;
    int Gates[CEC_TRAN_RECIPE_NODES_MAX];
    int Leaves[2*CEC_TRAN_RECIPE_NODES_MAX+1];
    int i, k, r, Root, Rep, Bad, Care, nRoots = 0, nBefore, nAfterCopy, nLeaves;
    long long nCofactorNodes = 0, nOriginalExits = 0, nUnfactoredWindowNodes = 0;
    assert(nCands > 0);
    *pnFull = 0;
    Gia_ManFillValue(p);
    pNew = Gia_ManStart(Gia_ManObjNum(p)+4*nCands+16);
    pNew->pName = Abc_UtilStrsav("stran_window_boolean_difference");
    Gia_ManHashAlloc(pNew);
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi(p,pObj,i) pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachAnd(p,pObj,i)
        pObj->Value = Cec_TranHashGate(pNew,pObj,
            Gia_ObjFanin0Copy(pObj),Gia_ObjFanin1Copy(pObj));
    nAfterCopy = Gia_ManAndNum(pNew);
    for ( i = 0; i < nCands; i++ )
    {
        r = pCands[i].iTarget;
        if ( pCare[r] == -1 )
        {
            nBefore = Gia_ManAndNum(pNew);
            pCare[r] = Cec_TranWindowFactorCare(p,pNew,r,pPars,
                pNodes+r,pEnds+r,pFull+r);
            nCofactorNodes += Gia_ManAndNum(pNew)-nBefore;
            nRoots++;
        }
        Care = pCare[r];
        // Match the original strict fallback exactly for oversized recipes.
        if ( pCands[i].nGates+pNodes[r]-1 > CEC_TRAN_RECIPE_NODES_MAX )
            Care = 1;
        *pnFull += pFull[r] ||
            pCands[i].nGates+pNodes[r]-1 > CEC_TRAN_RECIPE_NODES_MAX;
        nOriginalExits += (pPars->fOdcStrict || (pPars->nExplore & 16384) ||
            pCands[i].nGates+pNodes[r]-1 > CEC_TRAN_RECIPE_NODES_MAX) ? 1 : pEnds[r];
        nUnfactoredWindowNodes += pNodes[r]-1;
        Root = Cec_TranCopyLit(p,Abc_Var2Lit(r,0));
        Rep = Cec_TranRecipeBuildMapped(p,pNew,pCands+i,Gates);
        Root = Gia_ManHashAnd(pNew,Root,Care);
        Rep = Gia_ManHashAnd(pNew,Rep,Care);
        Vec_IntPushTwo(vCombPairs,Root,Rep);
        if ( !pPars->fUseCbsMultiLit )
            Vec_IntPush(vQueries,Gia_ManHashXor(pNew,Root,Rep));
        if ( vAndCounts )
        {
            // With D=1, a masked pair is exactly the original strict-root
            // relation. Its recipe leaf decomposition remains valid. Other
            // masked predicates must use generic equality CBS.
            nLeaves = Care == 1 ?
                Cec_TranRecipeCollectAndLeaves(pCands+i,Leaves) : 0;
            for ( k = 0; k < nLeaves; k++ )
                Vec_IntPush(vAndLeaves,Cec_TranRecipeCopyCode(p,
                    Leaves[k],Gates,pCands[i].nGates));
            Vec_StrPush(vAndCounts,(char)nLeaves);
        }
        Root = Cec_TranRootClassEndpoint(pNew,Root,Gia_ManPiNum(p),pPiProxies);
        Rep = Cec_TranRootClassEndpoint(pNew,Rep,Gia_ManPiNum(p),pPiProxies);
        Vec_IntPushTwo(vPairs,Root,Rep);
    }
    Vec_IntForEachEntry(vQueries,Bad,i) Gia_ManAppendCo(pNew,Bad);
    Vec_IntForEachEntry(vPairs,Bad,i) Gia_ManAppendCo(pNew,Bad);
    Gia_ManForEachRi(p,pObj,i) Gia_ManAppendCo(pNew,Gia_ObjFanin0Copy(pObj));
    Gia_ManHashStop(pNew);
    Gia_ManSetRegNum(pNew,Gia_ManRegNum(p));
    nBefore = Gia_ManAndNum(pNew);
    pNew = Gia_ManCleanup(pTemp=pNew);
    Gia_ManDupRemapLiterals(vPairs,pTemp);
    Gia_ManDupRemapLiterals(vCombPairs,pTemp);
    Gia_ManDupRemapLiterals(vQueries,pTemp);
    if ( vAndLeaves ) Gia_ManDupRemapLiterals(vAndLeaves,pTemp);
    Gia_ManStop(pTemp);
    if ( pPars->fProfile )
        Abc_Print(1,"window-factor graph: encoding=%s candidates=%d roots=%d original-exits=%lld factored-obligations=%d unshared-window-node-visits=%lld cofactor-new-ands=%lld source-copy-ands=%d before-cleanup-ands=%d proof-ands=%d\n",
            "masked-pair",nCands,nRoots,nOriginalExits,nCands,nUnfactoredWindowNodes,
            nCofactorNodes,nAfterCopy,nBefore,Gia_ManAndNum(pNew));
    ABC_FREE(pCare); ABC_FREE(pNodes); ABC_FREE(pEnds); ABC_FREE(pFull); ABC_FREE(pPiProxies);
    *pvPairs=vPairs; *pvCombPairs=vCombPairs; *pvQueries=vQueries;
    *pvAndLeaves = vAndLeaves;
    *pvAndCounts = vAndCounts;
    return pNew;
}

static Vec_Int_t * Cec_TranProveWindowFactorBatch( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, int nCands, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, int fCombOnly, Vec_Str_t ** pvStage, int * pnFull )
{
    Vec_Int_t * vPairs, * vCombPairs, * vQueries, * vAndLeaves;
    Vec_Str_t * vAndCounts;
    abctime clk = Abc_Clock();
    Gia_Man_t * pBatch = Cec_TranBuildWindowFactorBatch(p,pCands,nCands,pPars,
        &vPairs,&vCombPairs,&vQueries,&vAndLeaves,&vAndCounts,pnFull);
    pProf->timeRootCbsGraph += Abc_Clock()-clk;
    return Cec_TranProveRootBatchPrepared(pBatch,pCands,nCands,0,
        pPars,pProf,fCombOnly,pvStage,vPairs,vCombPairs,vQueries,vAndLeaves,vAndCounts);
}

// Exhaustive truth-table oracle over the independently built original and
// factored proof graphs. This catches care polarity, reconvergence and omitted
// exits even if the two SAT call paths happen to return the same status.
static word Cec_TranWindowFactorTruth( Gia_Man_t * p, Vec_Int_t * vPairs )
{
    word * Values = ABC_CALLOC(word,Gia_ManObjNum(p));
    Gia_Obj_t * pObj;
    word a, b, Bad = 0;
    int i, k, Lit;
    assert(Gia_ManCiNum(p) <= 6);
    Gia_ManForEachCi(p,pObj,i)
        for ( k = 0; k < 64; k++ )
            if ( (k >> i) & 1 ) Values[Gia_ObjId(p,pObj)] |= (word)1 << k;
    Gia_ManForEachAnd(p,pObj,i)
    {
        a = Values[Gia_ObjFaninId0p(p,pObj)];
        b = Values[Gia_ObjFaninId1p(p,pObj)];
        if ( Gia_ObjFaninC0(pObj) ) a = ~a;
        if ( Gia_ObjFaninC1(pObj) ) b = ~b;
        assert(!Gia_ObjIsMux(p,pObj));
        Values[i] = Gia_ObjIsBuf(pObj) ? a : Gia_ObjIsXor(pObj) ? a^b : a&b;
    }
    for ( i = 0; i < Vec_IntSize(vPairs); i += 2 )
    {
        Lit=Vec_IntEntry(vPairs,i); a=Values[Abc_Lit2Var(Lit)];
        if ( Abc_LitIsCompl(Lit) ) a=~a;
        Lit=Vec_IntEntry(vPairs,i+1); b=Values[Abc_Lit2Var(Lit)];
        if ( Abc_LitIsCompl(Lit) ) b=~b;
        Bad |= a^b;
    }
    ABC_FREE(Values);
    return Bad;
}

static void Cec_TranWindowFactorCheck( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, Cec_ParTran_t * pPars )
{
    Cec_TranCandVec_t Obs = {0};
    Gia_Man_t * Old, * New;
    Vec_Int_t * op, * oc, * oq, * np, * nc, * nq, * leaves;
    Vec_Str_t * counts;
    int Full, Mode, Saved = pPars->fUseCbsMultiLit;
    word Truth;
    Cec_TranWindowObligations(p,pCand,pPars,&Obs);
    Old = Cec_TranBuildRootBatch(p,NULL,0,Obs.pArray,Obs.nSize,2,
        &op,&oc,&oq,NULL,NULL);
    Truth = Cec_TranWindowFactorTruth(Old,oc);
    for ( Mode = 0; Mode < 2; Mode++ )
    {
        Cec_TranProf_t Prof = {0};
        Vec_Int_t * status;
        Vec_Str_t * stage;
        pPars->fUseCbsMultiLit = Mode;
        New = Cec_TranBuildWindowFactorBatch(p,pCand,1,pPars,
            &np,&nc,&nq,&leaves,&counts,&Full);
        assert(Truth == Cec_TranWindowFactorTruth(New,nc));
        status = Cec_TranProveRootBatchPrepared(New,pCand,1,0,pPars,&Prof,1,
            &stage,np,nc,nq,leaves,counts);
        assert(Vec_IntEntry(status,0) == (Truth == 0));
        Vec_IntFree(status); Vec_StrFree(stage);
    }
    pPars->fUseCbsMultiLit = Saved;
    Vec_IntFree(op); Vec_IntFree(oc); Vec_IntFree(oq);
    Gia_ManStop(Old); Cec_TranCandVecStop(&Obs);
}

static void Cec_TranWindowFactorSequentialCheck()
{
    int Next, Mode;
    // Both machines start with RO=0. RI=0 makes the predicate invariant;
    // RI=1 permits a violating assignment in the next frame. The latter
    // must not pass merely because the reset frame has zero observability.
    for ( Next = 0; Next < 2; Next++ ) for ( Mode = 0; Mode < 2; Mode++ )
    {
        Cec_ParTran_t Pars;
        Cec_TranProf_t Prof = {0};
        Cec_TranCand_t Cand = {0};
        Gia_Man_t * p = Gia_ManStart(16);
        Vec_Int_t * status;
        Vec_Str_t * stage;
        int Full, x=Gia_ManAppendCi(p), y=Gia_ManAppendCi(p);
        int ro=Gia_ManAppendCi(p), r=Gia_ManAppendAnd(p,x,ro);
        int out=Gia_ManAppendAnd(p,r,y);
        Gia_ManAppendCo(p,out); Gia_ManAppendCo(p,Next);
        Gia_ManSetRegNum(p,1);
        Gia_ManStaticFanoutStart(p);
        Cec_ManTranSetDefaultParams(&Pars);
        Pars.nFrames=2; Pars.nBTLimit=1000; Pars.nCombBTLimit=1000;
        Pars.nDepNodesMax=20; Pars.nExplore=134217728;
        Pars.fUseCbsMultiLit=Mode;
        Cand.iTarget=Abc_Lit2Var(r); Cand.nKind=CEC_TRAN_CAND_CONST;
        Cand.iOut=0;
        status=Cec_TranProveWindowFactorBatch(p,&Cand,1,&Pars,&Prof,0,&stage,&Full);
        assert(Vec_IntEntry(status,0)==!Next);
        if ( !Next ) assert(Vec_StrEntry(stage,0)==2);
        Vec_IntFree(status); Vec_StrFree(stage);
        Gia_ManStaticFanoutStop(p); Gia_ManStop(p);
    }
}
