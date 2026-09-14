// Commit draining and stable profile emission.
// Private implementation fragment included only by cecTrans.c.

static void Cec_TranPrintRootOnlyProfile( Cec_TranProf_t * p,
    int nAndBefore, int nAndAfter, int nRegBefore, int nRegAfter,
    int nRootWaves, int iPhase, int fClosure );

// Drain the proved pool to a commit fixed point without rediscovering or
// re-proving candidates.  Each iteration is one commit wave: validate every
// deferred certificate on the current graph, evaluate frozen DAG-aware gain,
// select one conflict-free batch, commit it, and remap the remainder.  Thus an
// overlap only delays a candidate to the next wave; it never discards it.
static Gia_Man_t * Cec_TranDrainProvedCommits( Gia_Man_t * p,
    Cec_ParTran_t * pPars, Cec_TranCandVec_t * pHistory,
    int iEpoch, int iPhase, int * pnBatches )
{
    static char const * pPhase[2] = { "comb", "seq" };
    int nBatches = 0, nInvalidTotal = 0;
    assert( iPhase == 0 || iPhase == 1 );
    while ( pHistory->nSize )
    {
        abctime clkTotal = Abc_Clock(), clk;
        Cec_TranProf_t Prof = {0};
        Cec_TranCandVec_t HistoryLive = {0}, Proved = {0};
        Cec_TranCandVec_t Selected = {0}, Carry = {0};
        Cec_TranPatDb_t * pDb;
        Cec_TranSim_t * pSim;
        Gia_Man_t * pNext;
        Vec_Int_t * vMffc = Vec_IntAlloc( 128 );
        Vec_Int_t * vSupport = Vec_IntAlloc( 32 );
        char * pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
        char * pSolved = ABC_CALLOC( char, Gia_ManObjNum(p) );
        char * pCovered = ABC_CALLOC( char, Gia_ManObjNum(p) );
        char * pUsed = ABC_CALLOC( char, Gia_ManObjNum(p) );
        int i, nSelected = 0, nBefore = Gia_ManAndNum( p );
        int nRegBefore = Gia_ManRegNum( p );

        // The simulation is only a structural/signature guard for certificates
        // remapped through cleanup.  This loop performs no candidate discovery
        // and makes no proof calls.
        clk = Abc_Clock();
        pDb = Cec_TranPatDbStart( p, 0 );
        Gia_ManCreateRefs( p );
        pSim = Cec_TranSimStart( p, pPars, pDb );
        Prof.timeRootSimSig += Abc_Clock() - clk;
        clk = Abc_Clock();
        for ( i = 0; i < pHistory->nSize; i++ )
        {
            Cec_TranCand_t Cand = pHistory->pArray[i];
            if ( !Cec_TranProofHistoryTopoValid(p, &Cand) ||
                 !Cec_TranRecipeStructurallyValid(pSim, &Cand) ||
                 !Cec_TranRecipeMatchesRoot(pSim, &Cand, NULL) )
            {
                Prof.nHistoryTriedInvalidated++;
                continue;
            }
            Cand.nStatus = Cand.nProofStage == 1 ?
                CEC_TRAN_STATE_PROVED_COMB : CEC_TRAN_STATE_PROVED_SEQ;
            if ( !Cec_TranCandVecContains(&HistoryLive, &Cand) )
                Cec_TranCandVecPush( &HistoryLive, Cand );
            if ( !Cec_TranCandVecContains(&Proved, &Cand) )
                Cec_TranCandVecPush( &Proved, Cand );
        }
        Prof.timeRootRefresh += Abc_Clock() - clk;
        clk = Abc_Clock();
        if ( Proved.nSize )
            nSelected = Cec_TranRootConsumeProved( p, &Proved,
                pCovered, pUsed, pSolved, pMffc, vMffc, vSupport,
                &Selected, &Prof );
        Prof.timeRootPostSelect += Abc_Clock() - clk;
        for ( i = 0; i < HistoryLive.nSize; i++ )
            if ( !Cec_TranCandVecContains(&Selected,
                    HistoryLive.pArray + i) )
                Cec_TranCandVecPush( &Carry, HistoryLive.pArray[i] );

        // Commit may stop p, so all snapshot-owned guards are released first.
        Cec_TranSimStop( pSim );
        Cec_TranPatDbStop( pDb );
        pNext = Cec_TranCommitSelectedRootOnly( p, &Selected, pPars,
            &Prof, &Carry, pHistory );
        p = pNext;
        ABC_FREE( p->pRefs );
        nInvalidTotal += Prof.nHistoryTriedInvalidated;
        if ( nSelected )
        {
            nBatches++;
            Abc_Print( 1, "stran-root commit closure: epoch=%d phase=%s wave=%d selected=%d AND=%d->%d gain=%d deferred=%d.\n",
                iEpoch + 1, pPhase[iPhase], nBatches, nSelected,
                nBefore, Gia_ManAndNum(p), nBefore - Gia_ManAndNum(p),
                pHistory->nSize );
        }

        Cec_TranCandVecStop( &HistoryLive );
        Cec_TranCandVecStop( &Proved );
        Cec_TranCandVecStop( &Selected );
        Cec_TranCandVecStop( &Carry );
        Vec_IntFree( vMffc );
        Vec_IntFree( vSupport );
        ABC_FREE( pMffc );
        ABC_FREE( pSolved );
        ABC_FREE( pCovered );
        ABC_FREE( pUsed );
        Prof.timeTotal = Abc_Clock() - clkTotal;
        if ( pPars->fProfile )
            Cec_TranPrintRootOnlyProfile( &Prof, nBefore,
                Gia_ManAndNum(p), nRegBefore, Gia_ManRegNum(p),
                0, iPhase, 1 );
        if ( !nSelected )
            break;
    }
    *pnBatches = nBatches;
    Abc_Print( 1, "stran-root commit closure fixed point: epoch=%d phase=%s batches=%d deferred=%d invalidated=%d.\n",
        iEpoch + 1, pPhase[iPhase], nBatches, pHistory->nSize,
        nInvalidTotal );
    return p;
}

static void Cec_TranPrintRootOnlyProfile( Cec_TranProf_t * p,
    int nAndBefore, int nAndAfter, int nRegBefore, int nRegAfter,
    int nRootWaves, int iPhase, int fClosure )
{
    static char const * pStage[2] = { "COMB", "SEQ" };
    static char const * pLane[2] = { "CBS", "SCORR" };
    static char const * pKind[3] = { "CONSTANT", "EXISTING", "BUILD" };
    static int const BuildStages[4] = { 1, 3, 4, 5 };
    static char const * pBuildStage[4] = {
        "one-gate", "div-gate", "gate-gate", "greedy" };
    static char const * pRankBin[CEC_TRAN_BUILD_RANK_BINS] = {
        "1", "2", "3-4", "5-8", "9-16", "17-32", "33-64", "65+" };
    static char const * pGateBin[CEC_TRAN_BUILD_GATE_BINS] = {
        "1", "2", "3", "4", "5-8", "9+" };
    static char const * pGainBin[CEC_TRAN_BUILD_GAIN_BINS] = {
        "1", "2", "3-4", "5-8", "9-16", "17+" };
    static char const * pDivRankBin[CEC_TRAN_BUILD_DIVRANK_BINS] = {
        "1-4", "5-8", "9-16", "17-32", "33-64", "65+" };
    static char const * pMffcBin[CEC_TRAN_BUILD_MFFC_BINS] = {
        "1", "2", "3-4", "5-8", "9-16", "17+" };
    static char const * pPivotRatioBin[CEC_TRAN_PIVOT_RATIO_BINS] = {
        "zero", "1-25", "26-50", "51-75", "76-100" };
    static char const * pPivotKind[CEC_TRAN_PIVOT_KIND_BINS] = {
        "literal", "pair" };
    static char const * pPivotState[2] = { "unique", "duplicate" };
    static char const * pMultiRank[CEC_TRAN_MULTIPATH_RANK_BINS] = {
        "1", "2", "3", "4", "5", "6", "7", "8", "9+" };
    abctime Times[20] = { p->timeRootSimSig, p->timeRootRefresh,
        p->timeRootDirect, p->timeRootDivCi, p->timeRootResubInit,
        p->timeRootResubEnumCanon, p->timeRootIsf, p->timeRootCbsGraph,
        p->timeRootCbsScreen, p->timeRootCbsSolve, p->timeRootScorrGraph,
        p->timeRootScorrBmc, p->timeRootScorrIndSat,
        p->timeRootScorrResim, p->timeRootScorrOther, p->timeRootPostSelect,
        p->timeRootBundleDup, p->timeRootCleanup, p->timeRootExactAudit,
        p->timeShadow };
    char const * Names[20] = { "simulation/signatures", "root/MFFC/dirty-refresh",
        "direct constant/existing generation", "divisor-reservoir/CI-ranking",
        "resub-initialization", "resub-enumeration/canonicalization",
        "Kit/BDC ISF portfolio",
        "CBS-graph/build", "CBS-screen", "CBS-solve",
        "shared-scorr-graph/SRM", "shared-scorr-BMC/base",
        "shared-scorr-induction/SAT", "shared-scorr-resimulation/refinement",
        "shared-scorr-fixed-point/other", "post-fixed-point-selection/waves",
        "final-bundle-duplication", "cleanup", "exact-gain-audit", "shadow-audit" };
    int i, s, k, SumSelected = 0, SumProved[2] = {0};
    int SumLaneSelected = 0, SumLaneProved[2] = {0};
    abctime SumTime = 0, Unprofiled;
    long long SumMarginal = 0;
    // phase is the current discovery/proof/commit phase; bucket encodes
    // immutable discovery phase and MFFC, surviving all closure remaps.
    for ( i = 0; i < 8; i++ )
    {
        Cec_TranDiagMffc_t const * d = &p->DiagMffc[i];
        if ( !fClosure )
            Abc_Print( 1, "stran-root diagnosis profile: schema=10 phase=%s family=mffc-work bucket=%d calls=%lld next=%lld accepted=%lld enum-sec=%.6f build-sec=%.6f\n",
                iPhase ? "seq" : "comb", i, d->Calls, d->Next, d->Accepted,
                Cec_TranTimeSec(d->EnumTime), Cec_TranTimeSec(d->BuildTime) );
        for ( k = 0; k < 2; k++ )
            Abc_Print( 1, "stran-root diagnosis profile: schema=10 phase=%s family=mffc-origin bucket=%d generated=%lld proved=%lld selected=%lld selected-and-gain=%lld\n",
                iPhase ? "seq" : "comb", 8*k+i,
                d->Outcome[k][0], d->Outcome[k][1], d->Outcome[k][2], d->SelectedGain[k] );
    }
    if ( !fClosure )
    {
        for ( i = 0; p->DiagRootAvailable && i < 8; i++ )
        {
            Cec_TranDiagBucket_t const * d = &p->DiagRoots[i];
            Abc_Print( 1, "stran-root diagnosis profile: schema=9 phase=%s family=root bucket=%d roots=%lld started=%lld exhausted=%lld next=%lld raw=%lld valid=%lld positive=%lld nonpositive=%lld duplicate=%lld collapsed=%lld invalid=%lld accepted=%lld pivots=%lld enum-sec=%.6f build-sec=%.6f\n",
                iPhase ? "seq" : "comb", i, d->Roots, d->Started,
                d->Exhausted, d->Next, d->Raw, d->Valid, d->Positive,
                d->Nonpositive, d->Duplicate, d->Collapsed, d->Invalid,
                d->Accepted, d->Pivots, Cec_TranTimeSec(d->EnumTime),
                Cec_TranTimeSec(d->BuildTime) );
        }
        for ( i = 0; i < 8; i++ )
            for ( k = 0; k < 8; k++ )
            {
                Cec_TranDiagGate_t const * d = &p->DiagGates[i][k];
                Abc_Print( 1, "stran-root diagnosis profile: schema=9 phase=%s family=gate bucket=%d count=%lld accepted=%lld nonpositive=%lld boundary=%lld rescued=%lld next-sec=%.6f\n",
                    iPhase ? "seq" : "comb", 8*i+k, d->Count, d->Accepted,
                    d->Nonpositive, d->Boundary, d->Rescued, Cec_TranTimeSec(d->Time) );
            }
        for ( i = 1; i <= 5; i++ )
            if ( i != 2 )
                for ( k = 0; k < 8; k++ )
                    Abc_Print( 1, "stran-root diagnosis profile: schema=9 phase=%s family=reject bucket=%d count=%lld next-sec=%.6f\n",
                        iPhase ? "seq" : "comb", 8*i+k,
                        p->DiagReject[i][k].Count, Cec_TranTimeSec(p->DiagReject[i][k].Time) );
        Abc_Print( 1, "stran-root diagnosis profile: schema=9 phase=%s family=time bucket=0 iterator-sec=%.6f decode-sec=%.6f exhausted-iterator-sec=%.6f\n",
            iPhase ? "seq" : "comb", Cec_TranTimeSec(p->DiagIteratorTime),
            Cec_TranTimeSec(p->DiagDecodeTime), Cec_TranTimeSec(p->DiagExhaustTime) );
    }
    Abc_Print( 1, "stran-root preprocessing-detail profile: schema=2 phase=%s exp-ci-hit=%lld exp-ci-miss=%lld exp-score-sec=%.6f exp-ci-sec=%.6f exp-obs-roots=%lld exp-obs-conflict=%lld exp-full-roots=%lld exp-full-conflict=%lld exp-obs-total=%lld exp-obs-unique=%lld exp-pruned=%lld exp-obs-sec=%.6f exp-zero-build-sec=%.6f exp-positive-build-sec=%.6f exp-zero-rank-sec=%.6f exp-positive-rank-sec=%.6f\n",
        iPhase ? "seq" : "comb", p->nExpCiHit, p->nExpCiMiss,
        Cec_TranTimeSec(p->timeExpRankScore), Cec_TranTimeSec(p->timeExpRankCi),
        p->nExpObsRoots, p->nExpObsConflict, p->nExpFullRoots, p->nExpFullConflict,
        p->nExpObsTotal, p->nExpObsUnique, p->nExpPruned,
        Cec_TranTimeSec(p->timeExpObs), Cec_TranTimeSec(p->timeExpZeroBuild),
        Cec_TranTimeSec(p->timeExpPositiveBuild), Cec_TranTimeSec(p->timeExpZeroRank),
        Cec_TranTimeSec(p->timeExpPositiveRank) );
    Abc_Print( 1, "stran-root time profile: total=%.6f sec.\n",
        Cec_TranTimeSec(p->timeTotal) );
    for ( i = 0; i < 20; i++ )
    {
        Abc_Print( 1, "  %-42s %.6f sec %6.2f%%\n", Names[i],
            Cec_TranTimeSec(Times[i]), p->timeTotal ?
            100.0 * Times[i] / p->timeTotal : 0.0 );
        SumTime += Times[i];
    }
    Unprofiled = p->timeTotal > SumTime ? p->timeTotal - SumTime : 0;
    Abc_Print( 1, "stran-root experiment-time profile: schema=9 phase=%s scope=%s total-sec=%.6f sim-sec=%.6f root-refresh-sec=%.6f direct-discovery-sec=%.6f divisor-discovery-sec=%.6f resub-init-sec=%.6f resub-enum-sec=%.6f isf-portfolio-sec=%.6f cbs-graph-sec=%.6f cbs-screen-sec=%.6f cbs-solve-sec=%.6f scorr-graph-sec=%.6f scorr-bmc-sec=%.6f scorr-induction-sec=%.6f scorr-resim-sec=%.6f scorr-other-sec=%.6f selection-repair-sec=%.6f bundle-sec=%.6f cleanup-sec=%.6f exact-audit-sec=%.6f shadow-sec=%.6f unprofiled-sec=%.6f\n",
        iPhase ? "seq" : "comb", fClosure ? "closure" : "discovery",
        Cec_TranTimeSec(p->timeTotal), Cec_TranTimeSec(p->timeRootSimSig),
        Cec_TranTimeSec(p->timeRootRefresh), Cec_TranTimeSec(p->timeRootDirect),
        Cec_TranTimeSec(p->timeRootDivCi), Cec_TranTimeSec(p->timeRootResubInit),
        Cec_TranTimeSec(p->timeRootResubEnumCanon), Cec_TranTimeSec(p->timeRootIsf),
        Cec_TranTimeSec(p->timeRootCbsGraph),
        Cec_TranTimeSec(p->timeRootCbsScreen), Cec_TranTimeSec(p->timeRootCbsSolve),
        Cec_TranTimeSec(p->timeRootScorrGraph), Cec_TranTimeSec(p->timeRootScorrBmc),
        Cec_TranTimeSec(p->timeRootScorrIndSat), Cec_TranTimeSec(p->timeRootScorrResim),
        Cec_TranTimeSec(p->timeRootScorrOther), Cec_TranTimeSec(p->timeRootPostSelect),
        Cec_TranTimeSec(p->timeRootBundleDup), Cec_TranTimeSec(p->timeRootCleanup),
        Cec_TranTimeSec(p->timeRootExactAudit), Cec_TranTimeSec(p->timeShadow),
        Cec_TranTimeSec(Unprofiled) );
    Abc_Print( 1, "stran-root ISF time profile: schema=1 phase=%s portfolio-sec=%.6f rescue-core-sec=%.6f regular-core-sec=%.6f projection-sec=%.6f kit-synthesis-sec=%.6f bdc-synthesis-sec=%.6f\n",
        iPhase ? "seq" : "comb", Cec_TranTimeSec(p->timeRootIsf),
        Cec_TranTimeSec(p->timeRootTfoCoreSelect),
        Cec_TranTimeSec(p->timeRootIsfCoreSelect),
        Cec_TranTimeSec(p->timeRootIsfProjection),
        Cec_TranTimeSec(p->timeRootKitSynthesis),
        Cec_TranTimeSec(p->timeRootBdcSynthesis) );
    Abc_Print( 1, "stran-root preprocessing-detail profile: schema=1 phase=%s div-collect-sec=%.6f div-rank-sec=%.6f div-select-sec=%.6f div-hash-sec=%.6f frontier-dead-sec=%.6f root-potential-sec=%.6f frontier-loop-sec=%.6f frontier-support-sec=%.6f frontier-gain-sec=%.6f frontier-sort-sec=%.6f frontier-pair-scans=%lld frontier-matched=%lld\n",
        iPhase ? "seq" : "comb",
        Cec_TranTimeSec(p->timeRootDivCollect),
        Cec_TranTimeSec(p->timeRootDivRank),
        Cec_TranTimeSec(p->timeRootDivSelect),
        Cec_TranTimeSec(p->timeRootDivHash),
        Cec_TranTimeSec(p->timeRootFrontDead),
        Cec_TranTimeSec(p->timeRootPotentialRefresh),
        Cec_TranTimeSec(p->timeRootFrontLoop),
        Cec_TranTimeSec(p->timeRootFrontSupport),
        Cec_TranTimeSec(p->timeRootFrontGain),
        Cec_TranTimeSec(p->timeRootFrontSort),
        p->nRootFrontPairScans, p->nRootFrontMatched );
    Abc_Print( 1, "stran-root page-reuse-detail profile: schema=2 phase=%s rank-mffc-one-first-sec=%.6f rank-mffc-one-cont-sec=%.6f rank-eligible-first-sec=%.6f rank-eligible-cont-sec=%.6f rank-mffc-one-first-calls=%lld rank-mffc-one-cont-calls=%lld rank-eligible-first-calls=%lld rank-eligible-cont-calls=%lld frontier-loop-first-sec=%.6f frontier-loop-cont-sec=%.6f frontier-pair-scans-first=%lld frontier-pair-scans-cont=%lld mffc-one-page-skips=%lld\n",
        iPhase ? "seq" : "comb",
        Cec_TranTimeSec(p->timeRootDivRankMffcOneFirst),
        Cec_TranTimeSec(p->timeRootDivRankMffcOneCont),
        Cec_TranTimeSec(p->timeRootDivRankEligibleFirst),
        Cec_TranTimeSec(p->timeRootDivRankEligibleCont),
        p->nRootDivRankMffcOneFirstCalls,
        p->nRootDivRankMffcOneContCalls,
        p->nRootDivRankEligibleFirstCalls,
        p->nRootDivRankEligibleContCalls,
        Cec_TranTimeSec(p->timeRootFrontLoopFirst),
        Cec_TranTimeSec(p->timeRootFrontLoopCont),
        p->nRootFrontPairScansFirst, p->nRootFrontPairScansCont,
        p->nRootPageMffcOneSkipped );
    Abc_Print( 1, "stran-root effect matrix: proof-origin-phase kind generated submitted proved selected marginal-AND marginal-Reg\n" );
    for ( s = 0; s < 2; s++ )
    for ( k = 0; k < 3; k++ )
    {
        Abc_Print( 1, "  %s %s %d %d %d %d %lld %lld\n", pStage[s], pKind[k],
            p->nStageKindGenerated[s][k], p->nStageKindSubmitted[s][k],
            p->nStageKindProved[s][k], p->nStageKindSelected[s][k],
            p->nStageKindMarginalAndGain[s][k],
            p->nStageKindMarginalRegGain[s][k] );
        Abc_Print( 1, "stran-root experiment-effect profile: schema=5 stage=%s kind=%s generated=%d submitted=%d proved=%d selected=%d marginal-and=%lld marginal-reg=%lld\n",
            s ? "seq" : "comb", k == CEC_TRAN_CAND_CONST ? "constant" :
            k == CEC_TRAN_CAND_EXIST ? "existing" : "build",
            p->nStageKindGenerated[s][k], p->nStageKindSubmitted[s][k],
            p->nStageKindProved[s][k], p->nStageKindSelected[s][k],
            p->nStageKindMarginalAndGain[s][k],
            p->nStageKindMarginalRegGain[s][k] );
        SumSelected += p->nStageKindSelected[s][k];
        SumProved[s] += p->nStageKindProved[s][k];
        SumMarginal += p->nStageKindMarginalAndGain[s][k];
    }
    Abc_Print( 1, "stran-root proof-lane matrix: lane kind submitted proved selected\n" );
    for ( s = 0; s < 2; s++ )
    for ( k = 0; k < 3; k++ )
    {
        Abc_Print( 1, "  %s %s %d %d %d\n", pLane[s], pKind[k],
            p->nLaneKindSubmitted[s][k], p->nLaneKindProved[s][k],
            p->nLaneKindSelected[s][k] );
        Abc_Print( 1, "stran-root experiment-proof-lane profile: schema=5 lane=%s kind=%s submitted=%d proved=%d selected=%d\n",
            s ? "scorr" : "cbs", k == CEC_TRAN_CAND_CONST ? "constant" :
            k == CEC_TRAN_CAND_EXIST ? "existing" : "build",
            p->nLaneKindSubmitted[s][k], p->nLaneKindProved[s][k],
            p->nLaneKindSelected[s][k] );
        SumLaneProved[s] += p->nLaneKindProved[s][k];
        SumLaneSelected += p->nLaneKindSelected[s][k];
    }
    assert( SumTime <= p->timeTotal );
    assert( SumProved[0] + SumProved[1] ==
        p->nCombProved + p->nSeqProved );
    assert( SumLaneProved[0] == p->nCombProved );
    assert( SumLaneProved[1] == p->nSeqProved );
    assert( SumSelected == p->nRootBundleCommits );
    assert( SumLaneSelected == p->nRootBundleCommits );
    assert( SumMarginal <= p->nRootBundleAndGain );
    assert( p->nRootBundleAndGain == nAndBefore - nAndAfter );
    assert( p->nSeqSeeded >= p->nSeqCands );
    assert( p->nSeqCands ==
        p->nSeqProved + p->nSeqSplit + p->nSeqUnknown );
    assert( p->nRootResubIterInit == p->nRootResubIterExhausted +
        p->nRootResubIterCapped );
    assert( p->nRootResubIterDiscarded == 0 );
    assert( p->nRootResubIterLive == 0 );
    assert( p->nRootResubIterLiveMax <= 1 );
    Abc_Print( 1, "stran-root effect totals: selected-roots=%d marginal-AND=%lld cleanup-exact-AND=%lld AND=%d->%d.\n",
        SumSelected, SumMarginal, p->nRootBundleAndGain, nAndBefore, nAndAfter );
    Abc_Print( 1, "stran-root experiment-summary profile: schema=8 phase=%s scope=%s selected-roots=%d marginal-and=%lld final-and-gain=%lld final-reg-gain=%lld and-before=%d and-after=%d reg-before=%d reg-after=%d\n",
        iPhase ? "seq" : "comb", fClosure ? "closure" : "discovery",
        SumSelected, SumMarginal, p->nRootBundleAndGain,
        p->nRootBundleRegGain, nAndBefore, nAndAfter, nRegBefore, nRegAfter );
    // Preserve the proof-origin matrix above and separately attribute every
    // selected certificate to the phase in which it was actually committed.
    for ( k = 0; k < 3; k++ )
        Abc_Print( 1, "stran-root experiment-commit profile: schema=8 phase=%s kind=%s selected=%d marginal-and=%lld marginal-reg=%lld\n",
            iPhase ? "seq" : "comb", k == CEC_TRAN_CAND_CONST ? "constant" :
            k == CEC_TRAN_CAND_EXIST ? "existing" : "build",
            p->nStageKindSelected[0][k] + p->nStageKindSelected[1][k],
            p->nStageKindMarginalAndGain[0][k] + p->nStageKindMarginalAndGain[1][k],
            p->nStageKindMarginalRegGain[0][k] + p->nStageKindMarginalRegGain[1][k] );
    Abc_Print( 1, "stran-root sequential relations: candidates=%d seeded=%d helper-seeds=%d proved=%d split=%d unknown=%d roots=%d class-max=%d class-avg=%.2f fixed-point-rounds=%d.\n",
        p->nSeqCands, p->nSeqSeeded, p->nSeqSeeded - p->nSeqCands,
        p->nSeqProved, p->nSeqSplit, p->nSeqUnknown,
        p->nSeqRoots, p->nSeqClassMax, p->nSeqRoots ?
        1.0 * p->nSeqClassSum / p->nSeqRoots : 0.0,
        p->nSeqFixedRounds );
    Abc_Print( 1, "stran-root helper history: retained=%d injected-events=%d inactive-events=%d dedup=%d invalidated=%d classes=%d endpoints-max=%d materialized-gates=%d batch-relations-max=%d srm-nodes-max=%d new-proved=%d history-proved-selected=%d waves=%d continuations=%d.\n",
        p->nHelperRetained, p->nHelperInjected, p->nHelperInactive,
        p->nHelperDedup, p->nHelperInvalidated, p->nHelperClasses,
        p->nHelperEndpoints, p->nHelperMaterialGates,
        p->nRootBatchMax, p->nRootSrmNodesMax, p->nRootNewProved,
        p->nRootHistorySelected, p->nRootProofWaves,
        p->nRootWaveContinues );
    Abc_Print( 1, "stran-root scorr obligations: bmc=%lld/%lld/%lld induction=%lld/%lld/%lld (unsat/sat/unknown).\n",
        p->Corr.nBmcUnsat, p->Corr.nBmcSat, p->Corr.nBmcUnknown,
        p->Corr.nIndUnsat, p->Corr.nIndSat, p->Corr.nIndUnknown );
    Abc_Print( 1, "stran-root resub iterator: initialized=%d next=%d exhausted=%d q-wave-stops=%d snapshot-discarded=%d live-max=%d live-final=%d invalid=%d.\n",
        p->nRootResubIterInit, p->nRootResubIterNext,
        p->nRootResubIterExhausted, p->nRootResubIterCapped,
        p->nRootResubIterDiscarded, p->nRootResubIterLiveMax,
        p->nRootResubIterLive,
        p->nRootResubInvalid );
    Abc_Print( 1, "stran-root build-funnel profile: schema=7 phase=%s reservoir-calls=%lld reservoir-nodes=%lld reservoir-max=%d pool-nodes=%lld pool-max=%d pool-empty=%d mffc-sum=%lld mffc-max=%d mffc-one-skipped=%lld iterator-next=%d semantic-invalid=%d collapsed-direct=%lld reject-nonpositive=%lld reject-known=%lld reject-direct=%lld reject-page=%lld accepted=%lld\n",
        iPhase ? "seq" : "comb",
        p->nRootDivReservoirCalls, p->nRootDivReservoirNodes,
        p->nRootDivReservoirMax, p->nRootDivPoolNodes,
        p->nRootDivPoolMax, p->nRootDivPoolEmpty,
        p->nRootBuildMffcSum, p->nRootBuildMffcMax,
        p->nRootBuildMffcOneSkipped,
        p->nRootResubIterNext, p->nRootResubInvalid,
        p->nRootBuildCollapsedDirect, p->nRootBuildRejectNonPositive,
        p->nRootBuildRejectKnown, p->nRootBuildRejectDirect,
        p->nRootBuildRejectPage, p->nRootBuildAccepted );
    if ( p->pBuildSuppProf )
        Cec_TranSuppProfPrint( p->pBuildSuppProf, iPhase );
    for ( i = 0; i < 4; i++ )
    {
        int Stage = BuildStages[i];
        Abc_Print( 1, "stran-root build-stage profile: schema=7 phase=%s bucket=%s valid=%lld accepted=%lld generated=%lld proved=%lld selected=%lld selected-and-gain=%lld time-sec=%.6f\n",
            iPhase ? "seq" : "comb", pBuildStage[i],
            p->nRootBuildStageValid[Stage],
            p->nRootBuildStageAccepted[Stage],
            p->nRootBuildStageOutcome[Stage][0],
            p->nRootBuildStageOutcome[Stage][1],
            p->nRootBuildStageOutcome[Stage][2],
            p->nRootBuildStageSelectedAndGain[Stage],
            Cec_TranTimeSec(p->timeRootBuildStage[Stage]) );
    }
    for ( i = 0; i < CEC_TRAN_BUILD_RANK_BINS; i++ )
        Abc_Print( 1, "stran-root build-rank profile: schema=7 phase=%s bucket=%s generated=%lld proved=%lld selected=%lld selected-and-gain=%lld\n",
            iPhase ? "seq" : "comb", pRankBin[i],
            p->nRootBuildRankOutcome[i][0],
            p->nRootBuildRankOutcome[i][1],
            p->nRootBuildRankOutcome[i][2],
            p->nRootBuildRankSelectedAndGain[i] );
    for ( i = 0; i < CEC_TRAN_BUILD_GATE_BINS; i++ )
        Abc_Print( 1, "stran-root build-gates profile: schema=7 phase=%s bucket=%s generated=%lld proved=%lld selected=%lld selected-and-gain=%lld\n",
            iPhase ? "seq" : "comb", pGateBin[i],
            p->nRootBuildGateOutcome[i][0],
            p->nRootBuildGateOutcome[i][1],
            p->nRootBuildGateOutcome[i][2],
            p->nRootBuildGateSelectedAndGain[i] );
    for ( i = 0; i < CEC_TRAN_BUILD_GAIN_BINS; i++ )
        Abc_Print( 1, "stran-root build-gain profile: schema=7 phase=%s bucket=%s generated=%lld proved=%lld selected=%lld selected-and-gain=%lld\n",
            iPhase ? "seq" : "comb", pGainBin[i],
            p->nRootBuildGainOutcome[i][0],
            p->nRootBuildGainOutcome[i][1],
            p->nRootBuildGainOutcome[i][2],
            p->nRootBuildGainSelectedAndGain[i] );
    for ( i = 0; i < 2; i++ )
        Abc_Print( 1, "stran-root build-ci profile: schema=7 phase=%s bucket=%s generated=%lld proved=%lld selected=%lld selected-and-gain=%lld\n",
            iPhase ? "seq" : "comb", i ? "positive" : "zero",
            p->nRootBuildCiOutcome[i][0],
            p->nRootBuildCiOutcome[i][1], p->nRootBuildCiOutcome[i][2],
            p->nRootBuildCiSelectedAndGain[i] );
    for ( i = 0; i < CEC_TRAN_BUILD_DIVRANK_BINS; i++ )
        Abc_Print( 1, "stran-root build-divrank profile: schema=7 phase=%s bucket=%s generated=%lld proved=%lld selected=%lld selected-and-gain=%lld\n",
            iPhase ? "seq" : "comb", pDivRankBin[i],
            p->nRootBuildDivRankOutcome[i][0],
            p->nRootBuildDivRankOutcome[i][1],
            p->nRootBuildDivRankOutcome[i][2],
            p->nRootBuildDivRankSelectedAndGain[i] );
    for ( i = 0; i < CEC_TRAN_BUILD_MFFC_BINS; i++ )
        Abc_Print( 1, "stran-root build-mffc profile: schema=7 phase=%s bucket=%s calls=%lld next=%lld accepted=%lld time-sec=%.6f\n",
            iPhase ? "seq" : "comb", pMffcBin[i],
            p->nRootBuildMffcCalls[i],
            p->nRootBuildMffcNext[i], p->nRootBuildMffcAccepted[i],
            Cec_TranTimeSec(p->timeRootBuildMffc[i]) );
    Abc_Print( 1, "stran-root build-greedy-frontier profile: schema=7 phase=%s roots=%lld pivots=%lld unique-states=%lld duplicate-states=%lld zero-novel=%lld cover-sum=%lld novel-sum=%lld frontier-max=%d attempts=%lld found=%lld time-sec=%.6f schedule-frontiers=%lld schedule-scored-pivots=%lld schedule-complete=%lld schedule-time-sec=%.6f cache-lookups=%lld cache-hits=%lld cache-misses=%lld cache-same-page-hits=%lld cache-cross-page-hits=%lld cache-fail-hits=%lld cache-success-hits=%lld cache-saved-sec=%.6f cache-lookup-sec=%.6f cache-payload-bytes=%lld recursive-calls=%lld recursive-unique=%lld recursive-duplicates=%lld recursive-same-page=%lld recursive-cross-page=%lld recursive-fail-hits=%lld recursive-success-duplicates=%lld recursive-payload-bytes=%lld recursive-saved-sec=%.6f recursive-lookup-sec=%.6f recursive-dup-depth-0=%lld recursive-dup-depth-1=%lld recursive-dup-depth-2=%lld recursive-dup-depth-3plus=%lld\n",
        iPhase ? "seq" : "comb", p->nRootGreedyFrontierRoots,
        p->nRootGreedyFrontierPivots, p->nRootGreedyFrontierUnique,
        p->nRootGreedyFrontierPivots - p->nRootGreedyFrontierUnique,
        p->nRootGreedyFrontierZeroNovel, p->nRootGreedyFrontierCoverSum,
        p->nRootGreedyFrontierNovelSum, p->nRootGreedyFrontierMax,
        p->nRootGreedyPivotAttempts, p->nRootGreedyPivotFound,
        Cec_TranTimeSec(p->timeRootGreedyPivot),
        p->nRootGreedySchedFrontiers, p->nRootGreedySchedPivots,
        p->nRootGreedySchedComplete,
        Cec_TranTimeSec(p->timeRootGreedySched),
        p->nRootResidualCacheLookups, p->nRootResidualCacheHits,
        p->nRootResidualCacheMisses,
        p->nRootResidualCacheSamePageHits,
        p->nRootResidualCacheCrossPageHits,
        p->nRootResidualCacheFailHits,
        p->nRootResidualCacheSuccessHits,
        Cec_TranTimeSec(p->timeRootResidualCacheSaved),
        Cec_TranTimeSec(p->timeRootResidualCacheLookup),
        p->nRootResidualCachePayloadBytes,
        p->nRootResidualRecCalls, p->nRootResidualRecUnique,
        p->nRootResidualRecDuplicate, p->nRootResidualRecSamePage,
        p->nRootResidualRecCrossPage, p->nRootResidualRecFailHits,
        p->nRootResidualRecSuccessDuplicate,
        p->nRootResidualRecPayloadBytes,
        Cec_TranTimeSec(p->timeRootResidualRecSaved),
        Cec_TranTimeSec(p->timeRootResidualRecLookup),
        p->nRootResidualRecDuplicateDepth[0],
        p->nRootResidualRecDuplicateDepth[1],
        p->nRootResidualRecDuplicateDepth[2],
        p->nRootResidualRecDuplicateDepth[3] );
    Abc_Print( 1, "stran-root build-greedy-multipath-summary profile: schema=7 phase=%s cache-entries=%lld cache-lookups=%lld cache-hits=%lld cache-fail-hits=%lld cache-success-hits=%lld cache-payload-bytes=%lld duplicate-candidate-fingerprints=%lld extra-accepted=%lld extra-q-slots=%lld\n",
        iPhase ? "seq" : "comb",
        p->nRootMultiPathCacheEntries,
        p->nRootMultiPathCacheLookups,
        p->nRootMultiPathCacheHits,
        p->nRootMultiPathCacheFailHits,
        p->nRootMultiPathCacheSuccessHits,
        p->nRootMultiPathCachePayloadBytes,
        p->nRootMultiPathFingerprintDuplicates,
        p->nRootMultiPathAccepted,
        p->nRootMultiPathQSlots );
    for ( i = 0; i < CEC_TRAN_PIVOT_RANK_BINS; i++ )
        Abc_Print( 1, "stran-root build-greedy-pivot-rank profile: schema=7 phase=%s bucket=%s attempts=%lld found=%lld valid=%lld accepted=%lld generated=%lld proved=%lld selected=%lld selected-and-gain=%lld time-sec=%.6f\n",
            iPhase ? "seq" : "comb", pRankBin[i],
            p->GreedyPivotRank[i].nAttempts,
            p->GreedyPivotRank[i].nFound,
            p->GreedyPivotRank[i].nValid,
            p->GreedyPivotRank[i].nAccepted,
            p->GreedyPivotRank[i].nOutcome[0],
            p->GreedyPivotRank[i].nOutcome[1],
            p->GreedyPivotRank[i].nOutcome[2],
            p->GreedyPivotRank[i].nSelectedAndGain,
            Cec_TranTimeSec(p->GreedyPivotRank[i].Time) );
    for ( i = 0; i < CEC_TRAN_PIVOT_RATIO_BINS; i++ )
    {
        Abc_Print( 1, "stran-root build-greedy-pivot-novelty profile: schema=7 phase=%s bucket=%s attempts=%lld found=%lld valid=%lld accepted=%lld generated=%lld proved=%lld selected=%lld selected-and-gain=%lld time-sec=%.6f\n",
            iPhase ? "seq" : "comb", pPivotRatioBin[i],
            p->GreedyPivotNovel[i].nAttempts,
            p->GreedyPivotNovel[i].nFound,
            p->GreedyPivotNovel[i].nValid,
            p->GreedyPivotNovel[i].nAccepted,
            p->GreedyPivotNovel[i].nOutcome[0],
            p->GreedyPivotNovel[i].nOutcome[1],
            p->GreedyPivotNovel[i].nOutcome[2],
            p->GreedyPivotNovel[i].nSelectedAndGain,
            Cec_TranTimeSec(p->GreedyPivotNovel[i].Time) );
        Abc_Print( 1, "stran-root build-greedy-pivot-coverage profile: schema=7 phase=%s bucket=%s attempts=%lld found=%lld valid=%lld accepted=%lld generated=%lld proved=%lld selected=%lld selected-and-gain=%lld time-sec=%.6f\n",
            iPhase ? "seq" : "comb", pPivotRatioBin[i],
            p->GreedyPivotCover[i].nAttempts,
            p->GreedyPivotCover[i].nFound,
            p->GreedyPivotCover[i].nValid,
            p->GreedyPivotCover[i].nAccepted,
            p->GreedyPivotCover[i].nOutcome[0],
            p->GreedyPivotCover[i].nOutcome[1],
            p->GreedyPivotCover[i].nOutcome[2],
            p->GreedyPivotCover[i].nSelectedAndGain,
            Cec_TranTimeSec(p->GreedyPivotCover[i].Time) );
    }
    for ( i = 0; i < CEC_TRAN_PIVOT_KIND_BINS; i++ )
    {
        Abc_Print( 1, "stran-root build-greedy-pivot-kind profile: schema=7 phase=%s bucket=%s attempts=%lld found=%lld valid=%lld accepted=%lld generated=%lld proved=%lld selected=%lld selected-and-gain=%lld time-sec=%.6f\n",
            iPhase ? "seq" : "comb", pPivotKind[i],
            p->GreedyPivotKind[i].nAttempts,
            p->GreedyPivotKind[i].nFound,
            p->GreedyPivotKind[i].nValid,
            p->GreedyPivotKind[i].nAccepted,
            p->GreedyPivotKind[i].nOutcome[0],
            p->GreedyPivotKind[i].nOutcome[1],
            p->GreedyPivotKind[i].nOutcome[2],
            p->GreedyPivotKind[i].nSelectedAndGain,
            Cec_TranTimeSec(p->GreedyPivotKind[i].Time) );
        Abc_Print( 1, "stran-root build-greedy-pivot-state profile: schema=7 phase=%s bucket=%s attempts=%lld found=%lld valid=%lld accepted=%lld generated=%lld proved=%lld selected=%lld selected-and-gain=%lld time-sec=%.6f\n",
            iPhase ? "seq" : "comb", pPivotState[i],
            p->GreedyPivotState[i].nAttempts,
            p->GreedyPivotState[i].nFound,
            p->GreedyPivotState[i].nValid,
            p->GreedyPivotState[i].nAccepted,
            p->GreedyPivotState[i].nOutcome[0],
            p->GreedyPivotState[i].nOutcome[1],
            p->GreedyPivotState[i].nOutcome[2],
            p->GreedyPivotState[i].nSelectedAndGain,
            Cec_TranTimeSec(p->GreedyPivotState[i].Time) );
    }
    for ( i = 0; i < CEC_TRAN_MULTIPATH_RANK_BINS; i++ )
        for ( k = 0; k < CEC_TRAN_MULTIPATH_PATH_BINS; k++ )
        {
            Cec_TranPivotBucketProf_t * pBucket = &p->MultiPath[i][k];
            Abc_Print( 1, "stran-root build-greedy-path profile: schema=7 phase=%s top-rank=%s path-index=%d attempts=%lld found=%lld valid=%lld valid-gain=%lld accepted=%lld accepted-gain=%lld generated=%lld generated-gain=%lld proved=%lld proved-gain=%lld selected=%lld selected-gain=%lld selected-and-gain=%lld second-cover-sum=%lld diversity-new-sum=%lld diversity-sym-sum=%lld time-sec=%.6f\n",
                iPhase ? "seq" : "comb", pMultiRank[i], k + 1,
                pBucket->nAttempts, pBucket->nFound,
                pBucket->nValid, pBucket->nValidGain,
                pBucket->nAccepted, pBucket->nAcceptedGain,
                pBucket->nOutcome[0], pBucket->nOutcomeGain[0],
                pBucket->nOutcome[1], pBucket->nOutcomeGain[1],
                pBucket->nOutcome[2], pBucket->nOutcomeGain[2],
                pBucket->nSelectedAndGain,
                pBucket->nSecondCover, pBucket->nDiversityNew,
                pBucket->nDiversitySym, Cec_TranTimeSec(pBucket->Time) );
        }
    Abc_Print( 1, "stran-root waves:" );
    for ( i = 0; i < nRootWaves; i++ )
        Abc_Print( 1, " w%d=%d/%d/%d/%d/%d", i + 1,
            p->nRootWaveDepCalls[i], p->nRootWaveRecipes[i],
            p->nRootWaveSubmitted[i], p->nRootWaveProved[i],
            p->nRootWaveSelected[i] );
    Abc_Print( 1, ".\n" );
    Abc_Print( 1, "stran-root dirty: root-free=%d candidate-support-freed=%d root-MFFC-changed=%d.\n",
        p->nDirtyRootFreed, p->nDirtySupportFreed,
        p->nDirtyMffcChanged );
}
