// Focused ODC/CEX care regression.
// Private implementation fragment included only by cecTrans.c.

// Force an overflowing source and exercise the actual production selector,
// sparse gather, and repeated cache hits.  A separate dense simulation on the
// selected CI trace lanes is the oracle; the sparse array deliberately omits
// the fanout side input that made the previous L1 mask incorrect.
static int Cec_TranOdcRootCareSelfTest()
{
    Cec_ParTran_t Pars;
    Cec_TranPatDb_t * pDb;
    Cec_TranSim_t * pSource, * pBuild, * pDense;
    Gia_Man_t * p = Gia_ManStart(32);
    Gia_Obj_t * pObj;
    Vec_Int_t * vPool = Vec_IntAlloc(2);
    int Ci[4], Roots[2], Ids[64], c, f, i, j, s, d, t, h;
    int nHyp, nCovered, nReordered, nUpperWord;
    for ( i = 0; i < 4; i++ ) Ci[i] = Gia_ManAppendCi(p);
    Roots[0] = Gia_ManAppendAnd(p, Ci[0], Ci[1]);
    Roots[1] = Gia_ManAppendAnd(p, Ci[0] ^ 1, Ci[3]);
    Gia_ManAppendCo(p, Gia_ManAppendAnd(p, Roots[0], Ci[2]));
    Gia_ManAppendCo(p, Gia_ManAppendAnd(p, Roots[1], Ci[2] ^ 1));
    Cec_ManTranSetDefaultParams(&Pars);
    Pars.nSimWords = 1; Pars.nSimFrames = 4;
    pDb = Cec_TranPatDbStart(p, 137);
    for ( c = 0; c < 137; c++ )
    {
        Abc_Cex_t * pCex = Abc_CexAlloc(0, 4, 4);
        pCex->iFrame = 3;
        for ( f = 0; f < 4; f++ )
            for ( i = 0; i < 4; i++ )
                if ( Cec_TranTeachMix(1 + c + 137*f + 631*i) & 1 )
                    Abc_InfoSetBit(pCex->pData, 4*f+i);
        Vec_PtrPush(pDb->vCexes, pCex);
    }
    Cec_TranPatDbSeal(pDb);
    assert(Vec_PtrSize(pDb->vCexes) > 64*Pars.nSimWords);
    Gia_ManStaticFanoutStart(p);
    // Each cache is owned by one source/target/pool.  Recreate it when the
    // root or pool changes, and recreate source signatures in the last case.
    pSource = Cec_TranSimStart(p, &Pars, pDb);
    for ( t = 0; t < 4; t++ )
    {
        Cec_TranTeachCache_t * pCache = NULL, * pStrictCache = NULL;
        Cec_TranProf_t Prof = {0}, StrictProf = {0};
        word * pSourceCare, * pDenseCare, * pWrong;
        int iRoot = Abc_Lit2Var(Roots[t >= 2]);
        if ( t == 3 )
        {
            Abc_Cex_t * pCex;
            Cec_TranSimStop(pSource);
            Vec_PtrForEachEntry(Abc_Cex_t *, pDb->vCexes, pCex, c)
                for ( f = 0; f < 4; f++ )
                    Abc_InfoXorBit(pCex->pData, 4*f+2);
            pSource = Cec_TranSimStart(p, &Pars, pDb);
        }
        Vec_IntClear(vPool);
        Vec_IntPush(vPool, Abc_Lit2Var(Ci[t == 1 ? 1 : 0]));
        Vec_IntPush(vPool, Abc_Lit2Var(Ci[t >= 2 ? 3 : t == 1 ? 0 : 1]));
        assert(Vec_IntFind(vPool, Abc_Lit2Var(Ci[2])) < 0);
        pBuild = Cec_TranSimStartRootBatch(p, 1, 4);
        pDense = Cec_TranSimStartRootBatch(p, 1, 4);
        assert(pSource->nWords == 3 && pBuild->nWords == 1);
        pSourceCare = Cec_TranFirstLevelCare(pSource, iRoot, NULL);
        assert(Cec_TranTeachSelectCex(pSource, pDb, iRoot, vPool,
            64, Ids, &nHyp, &nCovered) == 64);
        nReordered = nUpperWord = 0;
        for ( d = 0; d < 64; d++ )
        {
            nReordered += Ids[d] != d;
            nUpperWord += Ids[d] >= 64;
            for ( j = 0; j < d; j++ ) assert(Ids[j] != Ids[d]);
        }
        assert(nReordered > 0 && nUpperWord > 0);
        // Gather CIs independently with scalar bit addressing, then simulate
        // all ANDs densely instead of copying source internal-node columns.
        Gia_ManForEachCi(p, pObj, i)
            for ( d = 0; d < 64; d++ )
                for ( f = 0; f < 4; f++ )
                    if ( Cec_TranTeachSampleValue(pSource, Gia_ObjId(p,pObj),
                        64*(f*pSource->nWords + Ids[d]/64) + Ids[d]%64) )
                        Cec_TranSimObj(pDense, Gia_ObjId(p,pObj))[f] |= (word)1 << d;
        Gia_ManForEachAnd(p, pObj, i)
            for ( s = 0; s < 4; s++ )
                Cec_TranSimObj(pDense,i)[s] =
                    Cec_TranSimLit(pDense, Gia_ObjFaninLit0p(p,pObj),s) &
                    Cec_TranSimLit(pDense, Gia_ObjFaninLit1p(p,pObj),s);
        pDenseCare = Cec_TranFirstLevelCare(pDense, iRoot, NULL);
        assert(pDenseCare[0] != pDenseCare[1]);
        for ( h = 0; h < 3; h++ )
        {
            int nWrong = 0;
            // Alternate absent and stale unfilled side inputs between hits.
            memset(pBuild->pSims, h & 1 ? 255 : 0,
                sizeof(word)*(size_t)Gia_ManObjNum(p)*pBuild->nSlots);
            Cec_TranTeachBuildSignature(pSource,pBuild,pDb,iRoot,vPool,
                &pCache,&Prof,pSourceCare);
            assert(Prof.nRootTeachSelections == 1 && Prof.nRootTeachCalls == h+1);
            assert(pCache->pCare && pCache->pSource == pSource);
            pWrong = Cec_TranFirstLevelCare(pBuild,iRoot,NULL);
            for ( s = 0; s < 4; s++ )
            {
                assert(pCache->pCare[s] == pDenseCare[s]);
                assert(Cec_TranSimObj(pBuild,iRoot)[s] == Cec_TranSimObj(pDense,iRoot)[s]);
                Vec_IntForEachEntry(vPool,j,i)
                    assert(Cec_TranSimObj(pBuild,j)[s] == Cec_TranSimObj(pDense,j)[s]);
                nWrong += pWrong[s] != pDenseCare[s];
            }
            assert(nWrong > 0); // this fixture demonstrably exposes old L1
            ABC_FREE(pWrong);
            Cec_TranTeachBuildSignature(pSource,pBuild,pDb,iRoot,vPool,
                &pStrictCache,&StrictProf,NULL);
            assert(pStrictCache->pCare == NULL);
            assert(!memcmp(pStrictCache->pSims,pCache->pSims,
                sizeof(word)*(size_t)pCache->nObjs*pBuild->nSlots));
        }
        ABC_FREE(pSourceCare); ABC_FREE(pDenseCare);
        Cec_TranTeachCacheStop(pCache); Cec_TranTeachCacheStop(pStrictCache);
        Cec_TranSimStop(pBuild); Cec_TranSimStop(pDense);
    }
    Cec_TranSimStop(pSource); Gia_ManStaticFanoutStop(p);
    Cec_TranPatDbStop(pDb); Vec_IntFree(vPool); Gia_ManStop(p);
    Abc_Print(1,"stran ODC L1 sparse-root-care overflow/selected-lanes/multiframe/cache/source/pool regression: PASS\n");
    return 1;
}
