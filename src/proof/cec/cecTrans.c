/**CFile****************************************************************

  FileName    [cecTrans.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential Direct root resubstitution.]

  Synopsis    [Candidate-and-prove sequential root replacement.]

  Description [The active algorithm replaces an AND root by a constant,
  earlier literal, or dependency recipe.  Root candidates are discovered and
  proved on an immutable GIA, selected under bundle interactions, and committed
  together.  Optional ODC processing proves preservation at the exits of a
  bounded fanout window.]

***********************************************************************/

#include "cecInt.h"
#include "aig/gia/giaAig.h"
#include "bool/bdc/bdc.h"
#include "bool/kit/kit.h"
#include "misc/util/utilTruth.h"
#include "sat/bmc/bmc.h"
#include "proof/pdr/pdr.h"
#include <stddef.h>

ABC_NAMESPACE_IMPL_START

#include "cecTranInt.h"

static int Cec_TranRelationalSelfTest();
static int Cec_TranRelationalBfsSelfTest();
static int Cec_TranOdcRelationalBoundarySelfTest();
static int Cec_TranConstHelperSelfTest();


int Cec_TranRootSelfTest()
{
    return Abc_ResubIteratorSelfTest() && Cec_TranCanonicalizeSelfTest() &&
        Cec_TranMffcSelfTest() && Cec_TranFrontierGainSelfTest() &&
        Cec_TranPipelineSelfTest() &&
        Cec_TranCommitWaveSelfTest() && Cec_TranProofMicroBatchSelfTest() &&
        Cec_TranObservationSelfTest() &&
        Cec_TranExactCoreSelfTest() && Cec_TranCareIsfSelfTest() &&
        Cec_TranCompleteFaninTfoSelfTest() &&
        Cec_TranFirstLevelCareSelfTest() && Cec_TranOdcRootCareSelfTest() &&
        Cec_TranOdcFanoutSelfTest() && Cec_TranWindowSelfTest() &&
        Cec_TranOdcDirectSelfTest() && Cec_TranSigGuideSelfTest() &&
        Cec_TranStrictCexSelfTest() && Cec_TranStrictCexActiveSelfTest() &&
        Cec_TranStrictGuideSelfTest() && Cec_TranRelObsSelfTest() &&
        Cec_TranTraceBuildSelfTest() && Cec_TranRelationalSelfTest() &&
        Cec_TranRelationalBfsSelfTest() && Cec_TranOdcRelationalBoundarySelfTest() &&
        Cec_TranConstHelperSelfTest();
}

void Cec_ManTranSetDefaultParams( Cec_ParTran_t * p )
{
    memset( p, 0, sizeof(Cec_ParTran_t) );
    p->nFrames     = 1;
    p->nBTLimit    = 100;
    p->nStepsMax   = -1;
    p->nStrictSteps = -2; p->nStrictWaves = -1;
    p->nInitialFrames = p->nInitialConflicts = -1;
    p->nWindowFrames = p->nWindowConflicts = -1;
    p->nWindowDivs = p->nWindowCandidates = -1;
    p->nWindowSteps = -2;
    p->nWindowCacheMiB = 256;
    p->nConstrMax  = 8;
    p->nConstrBaseMax = 16;
    p->nKitCoreMax = 0;
    p->fBdcPortfolio = 0;
    p->nDepNodesMax = 20;
    p->nSimWords   = 4;
    p->nSimFrames  = 8;
    p->nRootWaves  = 8;
    p->nRootConstrTop = 1;
    p->nRootProofBatch = 0;
    p->nStage5Paths = 0;
    p->nOdcProofMax = 64;
    p->nOdcFanoutRounds = 0;
    // Use the same per-obligation conflict budget for the combinational CBS
    // certificate lane and the sequential scorr oracle by default.  The two
    // budgets remain independently configurable through -b and -C.
    p->nCombBTLimit = 100;
    p->nFreeWords  = 2;
    p->nFreeCexMax = 64;
    p->nHardConfTotal = 1000000;
    p->fUseExisting = 1;
    p->fUseMffcDivs = 1;
    p->fUseTfoDivs = 0;
    p->fUseOdc = 0;
    p->fOdcStrict = 0;
    p->fOdcFanout = 0;
    p->fUseConstr  = 1;
    p->fUseCbsMultiLit = 1;
    // A round owns one immutable proof snapshot.  Every successful COMB/SEQ
    // selection is committed before the next snapshot is rediscovered.
    p->fUseFreeSim = 1;
    p->fUseHelpers = 1;
    p->fBuildOnly = 0;
}

// Reproduce the reviewed Guide1/CEX4 ordinary-COM route. This is a command
// preset, not a new search policy; later explicit options still override it.
void Cec_ManTranSetRoute1Params( Cec_ParTran_t * p, int fOdc )
{
    Cec_ManTranSetDefaultParams(p);
    p->fRoute1 = 1;
    p->nBTLimit = 1000;
    p->nInitialFrames = 1; p->nInitialConflicts = 200;
    p->nStrictSteps = 0; p->nStrictWaves = 3;
    p->nKitCoreMax = 8; p->fBdcPortfolio = 1;
    p->nRootConstrTop = 20; p->nRootProofBatch = 5;
    p->nExplore = 742531093;
    p->fUseTfoDivs = 1;
    p->nOdcProofMax = 0; p->nOdcFanoutRounds = 4;
    if ( fOdc )
    {
        p->fUseOdc = p->fOdcFanout = 1;
        p->nSignatureGuide = 2;
        p->nWindowFrames = 1; p->nWindowConflicts = 1000;
        p->fWindowCache = p->fWindowFactor = 1;
    }
}

#include "cecTranCex.h"
#include "cecTranCandidate.h"
#include "cecTranProof.h"
#include "cecTranGain.h"
#include "cecTranTfo.h"
#include "cecTranBuild.h"
#include "cecTranCommit.h"
#include "cecTranProfile.h"

static inline int Cec_TranRootCandBucket( int sz )
{
    if ( sz <= 4 )  return sz;
    if ( sz <= 8 )  return 5;
    if ( sz <= 16 ) return 6;
    if ( sz <= 32 ) return 7;
    if ( sz <= 64 ) return 8;
    return 9;
}

static Gia_Man_t * Cec_ManSequentialRootPass( Gia_Man_t * pGia,
    Cec_ParTran_t * pPars, int iRound, int fCombOnly,
    Cec_TranCandVec_t * pHistory, Cec_TranPatDb_t * pSharedDb,
    int fRootBatch, Cec_TranStrictCex_t * pStrictCex )
{
    Cec_ParTran_t QualityPars;
    Cec_TranProf_t Prof = {0};
    Cec_TranDiscStat_t Disc = {0};
    Cec_TranCandVec_t Known = {0}, RootCands = {0}, Page = {0};
    Cec_TranCandVec_t ProofCands = {0};
    Cec_TranCandVec_t BatchProved = {0}, Proved = {0}, Selected = {0};
    Cec_TranCandVec_t HistoryLive = {0}, Active = {0}, Carry = {0};
    Cec_TranRoot_t * pRoots;
    Cec_TranRootCursor_t * pCursors;
    Cec_TranSim_t * pSim, * pSource;
    Cec_TranPatDb_t * pDb;
    Cec_TranDepScratch_t Dep;
    Gia_Man_t * p = Gia_ManDup( pGia );
    Gia_Obj_t * pObj;
    Vec_Int_t * vMffc = Vec_IntAlloc( 128 );
    Vec_Int_t * vSupport = Vec_IntAlloc( 32 );
    char * pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pSolved = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pCovered = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pUsed = ABC_CALLOC( char, Gia_ManObjNum(p) );
    int nRoots = 0, r, i, nSelected = 0;
    int nWaves = 0, fSnapshotExhausted = 0;
    int fMicroBatch = pPars->nRootProofBatch > 0;
    int fCommitHorizonReached = 0;
    int nBuildAcceptedTotal = 0, nBuildAcceptedMax = 0;
    int nBuildHorizonRoots = 0;
    int nBuildEligibleRoots = 0, nBuildAtQRoots = 0;
    int nBuildExhaustedBeforeQRoots = 0, nBuildUnfinishedBelowQRoots = 0;
    int nBuildZeroAcceptedRoots = 0;
    int nFrontierRefreshes = 0, nFrontierRefreshReuses = 0;
    long long nFrontierCandidates = 0, nKnownCandidateScansAvoided = 0;
    int iPhase = fCombOnly ? 0 : 1;
    int nCandCalls = 0, nCandSum = 0, nCandMax = 0;
    int nCandHist[10] = {0};
    // Keep the arbitrary-state COMB pass on its TFI-only baseline.  The
    // complete-fanin shell is a SEQ-only divisor experiment, alongside the
    // Kit/BDC portfolio, so COMB cannot consume or reclassify its gains.
    int fUseTfoDivs = pPars->fUseTfoDivs && !fCombOnly;
    int nTfoMax = pPars->nConstrBaseMax;
    int fOwnDb = pSharedDb == NULL;
    int nAndBefore = Gia_ManAndNum( p ), nRegBefore = Gia_ManRegNum( p );
    abctime clkTotal = Abc_Clock(), clk;
    if ( Abc_ResubQualityNoTruncation() )
    {
        QualityPars = *pPars;
        QualityPars.nConstrMax = QualityPars.nConstrBaseMax = 0;
        // q is a total-search horizon; j only paginates the same stream.
        // Preserve the caller's j so proof can run before full enumeration.
        QualityPars.nRootConstrTop = 0;
        pPars = &QualityPars;
        nTfoMax = 0;
    }
    Prof.DiagPhase = iPhase;
    Prof.pStrictCex = !fCombOnly && pStrictCex && pStrictCex->Mode <= 3 ? pStrictCex : NULL;
    pDb = fOwnDb ? Cec_TranPatDbStart( p, 0 ) : pSharedDb;
    Gia_ManCreateRefs( p );
    if ( fUseTfoDivs )
        Gia_ManStaticFanoutStart( p );
    Gia_ManForEachAnd( p, pObj, i )
        nRoots++;
    pRoots = ABC_ALLOC( Cec_TranRoot_t, nRoots );
    nRoots = 0;
    Gia_ManForEachAnd( p, pObj, i )
        pRoots[nRoots].iObj = i,
        pRoots[nRoots].nMffc = Gia_NodeMffcSize( p, pObj ),
        nRoots++;
    qsort( pRoots, nRoots, sizeof(Cec_TranRoot_t), Cec_TranRootCompare );
    pCursors = ABC_CALLOC( Cec_TranRootCursor_t, Gia_ManObjNum(p) );
    if ( pPars->fProfile )
        Prof.pBuildSuppProf = Cec_TranSuppProfStart( Gia_ManObjNum(p) );
    clk = Abc_Clock();
    pSource = Cec_TranSimStart( p, pPars, pDb );
    if ( !fCombOnly && pStrictCex && pStrictCex->Mode >= 4 &&
         Cec_TranStrictCexActive(pStrictCex, p, pSource, pRoots, nRoots) )
    {
        Cec_TranPatDb_t * pTeach = Cec_TranStrictCexTeach(pStrictCex, p, pDb);
        if ( pTeach )
        {
            if ( fOwnDb ) Cec_TranPatDbStop(pDb);
            pDb = pTeach; fOwnDb = 1;
            fRootBatch = Vec_PtrSize(pDb->vCexes) > 64 * pPars->nSimWords;
            Cec_TranSimStop(pSource);
            pSource = Cec_TranSimStart(p, pPars, pDb);
        }
    }
    pSim = fRootBatch ? Cec_TranSimStartRootBatch( p,
        pPars->nSimWords, pPars->nSimFrames ) : pSource;
    // Keep the Q/W reset teacher unchanged. The separate Build table adds
    // conservative free-state observations before ranking or cursor creation.
    if ( !fCombOnly && Cec_TranStrictCexOption("ABC_STRICT_GUIDE", pPars->fRoute1, 1) )
    {
        if ( !fRootBatch )
            pSim = Cec_TranStrictGuide( pSource, pPars->fProfile );
        else if ( pPars->fProfile )
            Abc_Print(1, "stran-root strict-signature-guide: schema=1 snapshots=0 source-rows=0 auxiliary-rows=0 skipped-overflow=1 prep-sec=0\n");
    }
    Abc_ResubSetBothPolarities( !fCombOnly &&
        Cec_TranStrictCexOption("ABC_STRICT_BOTH_POLARITIES", 0, 1) );

    Prof.timeRootSimSig += Abc_Clock() - clk;
    Abc_ResubPrepareManager( pSim->nSlots );
    Cec_TranDepScratchStart( &Dep, pSim->nSlots,
        pPars->nConstrBaseMax ? pPars->nConstrBaseMax : 64, 1 );
    if ( Vec_PtrSize(pDb->vCexes) )
        Abc_Print( 1, "stran2 CEX trace signature: mode=%s source-words=%d build-words=%d frames=%d source-slots=%d build-slots=%d reachable-cex=%d cex-capacity=%d.\n",
            fRootBatch ? "root-batch" : "direct", pSource->nWords,
            pSim->nWords, pSource->nFrames, pSource->nSlots,
            pSim->nSlots, Vec_PtrSize(pDb->vCexes),
            64 * pPars->nSimWords );
    Abc_Print( 1, "stran-root: round=%d phase=%s snapshot=immutable scheduler=serial-root-iterator/all-candidates pivot-order=%s stage5-paths=%d stage5-path-order=eligible-primary/diagonal-extra/fallback-primary selection=%s candidates=%s q-build-per-root=%d proof-build-batch-per-root=%d helpers=%s divisor-route=%s existing=%s mffc-divisors=%s.\n",
        iRound + 1, fCombOnly ? "comb" : "seq",
        pPars->fUseSolvSched ? "residual-solvability" : "original",
        pPars->nStage5Paths <= 1 ? 1 : pPars->nStage5Paths,
        fMicroBatch ? "deferred-q-horizon-root-loss-gwmin" :
            "commit-wave-root-loss-gwmin",
        pPars->fBuildOnly ? "build-only" : "constant/existing/build",
        pPars->nRootConstrTop, pPars->nRootProofBatch,
        pPars->fUseHelpers ? "on" : "off",
        fUseTfoDivs ? "ranked-TFI+complete-fanin-TFO-shell" :
            "ranked-TFI-only",
        fUseTfoDivs ? "TFI+complete-fanin-TFO-pool" : "TFI-pool",
        pPars->fUseMffcDivs ? "on" : "off" );
    if ( fUseTfoDivs )
        Abc_Print( 1, "stran-root complete-fanin TFO: mode=shell added-cap=%s%d membership=complete-depth-K-TFI topology=fanin-id<root.\n",
            Abc_ResubQualityNoTruncation() ? "unlimited/" :
                (nTfoMax ? "" : "auto/"), nTfoMax );
    if ( pPars->nKitCoreMax )
        Abc_Print( 1, "stran-root Kit portfolio: core-max=%d proof-policy=unchanged exact-bundle-audit=on.\n",
            pPars->nKitCoreMax );
    if ( fMicroBatch )
        Abc_Print( 1, "stran-root proof micro-batching: enabled=yes build-per-root-per-proof=%d commit-build-horizon-per-root=%d horizon-zero=%s commit-policy=deferred-until-horizon.\n",
            pPars->nRootProofBatch, pPars->nRootConstrTop,
            pPars->nRootConstrTop ? "bounded" : "iterator-exhaustion" );

    // Reuse exact relations formally proved on an earlier snapshot.  They are
    // inserted into Known before discovery, so the iterator advances past the
    // duplicate and spends q on genuinely new Build candidates.  Failed and
    // UNKNOWN relations are absent from this cache and are intentionally
    // retried after a simplifying commit.
    for ( i = 0; i < pHistory->nSize; i++ )
    {
        Cec_TranCand_t Cand = pHistory->pArray[i];
        int Gain;
        if ( !Cec_TranProofHistoryTopoValid(p, &Cand) ||
             !Cec_TranRecipeStructurallyValid(pSource, &Cand) ||
             !Cec_TranRecipeMatchesRoot(pSource, &Cand, NULL) )
        {
            Prof.nHistoryTriedInvalidated++;
            continue;
        }
        Cand.nProofStage = pHistory->pArray[i].nProofStage;
        Cand.nStatus = Cand.nProofStage == 1 ?
            CEC_TRAN_STATE_PROVED_COMB : CEC_TRAN_STATE_PROVED_SEQ;
        Gain = Cec_TranQualityActualCost() ?
            Cec_TranQualityCostGainOne(p, &Cand, pCovered, pUsed, &Cand.nMffc) :
            Cec_TranCandDynamicGain( p, &Cand, pCovered, pUsed,
                pMffc, vMffc, vSupport );
        Cand.Gain = Gain;
        if ( !Cec_TranQualityActualCost() )
            Cand.nMffc = Vec_IntSize( vMffc );
        if ( !Cec_TranCandVecContains(&HistoryLive, &Cand) )
            Cec_TranCandVecPush( &HistoryLive, Cand );
        if ( !Cec_TranCandVecContains(&Known, &Cand) )
            Cec_TranCandVecPush( &Known, Cand );
        if ( !Cec_TranCandVecContains(&Proved, &Cand) )
            Cec_TranCandVecPush( &Proved, Cand );
        Prof.nQueueTriedSkipped++;
    }
    Prof.nHelperInvalidated = Prof.nHistoryTriedInvalidated;
    Prof.nHelperRetained = HistoryLive.nSize;

    // A positive retained certificate may become profitable after an earlier
    // commit.  It is eligible for commit without being re-proved.
    if ( Proved.nSize && !fMicroBatch )
    {
        clk = Abc_Clock();
        nSelected = Cec_TranRootConsumeProved( p, &Proved,
            pCovered, pUsed, pSolved, pMffc, vMffc,
            vSupport, &Selected, &Prof );
        Prof.timeRootPostSelect += Abc_Clock() - clk;
    }

    // Each page visits roots that still have discovery work.  A root owns its
    // heavyweight
    // iterator manager only for Cec_TranRootDiscoverOne(); a later no-commit
    // wave restores the root's scalar cursor onto the shared manager.
    // The all-root union is still submitted without any global truncation.
    while ( Selected.nSize == 0 )
    {
        int iWave = nWaves, iProfWave = Abc_MinInt(iWave, 63);
        int nLiveRoots = 0, nHorizonRoots = 0;
        Cec_TranCandVecClear( &Page );
        Cec_TranCandVecClear( &ProofCands );
        Cec_TranCandVecClear( &BatchProved );
        Cec_TranCandVecClear( &Active );
        for ( r = 0; r < nRoots; r++ )
        {
            int nGot;
            if ( pRoots[r].nMffc <= 0 )
                continue;
            nLiveRoots++;
            if ( Cec_TranRootDiscoveryFinished(pPars, pRoots + r,
                    pCursors + pRoots[r].iObj, iWave) )
            {
                nHorizonRoots++;
                if ( iWave > 0 && pPars->fUseConstr &&
                     !Cec_TranRootBuildEligible(pRoots + r) )
                    Prof.nRootPageMffcOneSkipped++;
                continue;
            }
            Cec_TranRootDiscoverOne( p, pSim, pSource, pDb, fRootBatch,
                pPars, pRoots + r,
                pCursors + pRoots[r].iObj, iWave,
                fUseTfoDivs, nTfoMax, 0,
                &Known, pSolved,
                pCovered, pUsed, pMffc, vMffc, &Dep, &Disc, &Prof,
                &RootCands, NULL );
            nGot = RootCands.nSize;
            for ( i = 0; i < RootCands.nSize; i++ )
                Cec_TranCandVecPush( &Page, RootCands.pArray[i] );
            nCandCalls++;
            nCandSum += nGot;
            nCandMax = Abc_MaxInt( nCandMax, nGot );
            nCandHist[Cec_TranRootCandBucket(nGot)]++;
        }
        if ( Page.nSize == 0 )
        {
            fCommitHorizonReached = fMicroBatch && nLiveRoots > 0 &&
                nHorizonRoots == nLiveRoots;
            fSnapshotExhausted = !fCommitHorizonReached;
            break;
        }
        nWaves++;
        Prof.nRootProofWaves++;
        Prof.nRootWaveContinues += nWaves > 1;
        for ( i = 0; i < Page.nSize; i++ )
        {
            Cec_TranCandVecPush( &Known, Page.pArray[i] );
            Prof.nStageKindGenerated[iPhase][Page.pArray[i].nKind]++;
            Cec_TranProfileBuildCandidate( &Prof, Page.pArray + i, 0 );
        }
        // In micro-batch mode only Page can contain fresh obligations.  Every
        // older Known entry is already PROVED or TRIED_SEQ, and scanning it
        // again cannot change the frontier on this immutable snapshot.  Keep
        // the legacy Known scan byte-for-byte when -j is disabled.
        {
            Cec_TranCandVec_t const * pFrontier =
                fMicroBatch ? &Page : &Known;
            // MFFCs and root order were computed at pass initialization.
            // Before selection the graph, covered and used sets never change.
            // A successful selection exits discovery, including in -j0 mode;
            // a new committed graph gets fresh initialization in the next pass.
            int fRefreshRoots = 0;
            nFrontierRefreshes += fRefreshRoots;
            nFrontierRefreshReuses += !fRefreshRoots;
            nFrontierCandidates += pFrontier->nSize;
            if ( fMicroBatch )
                nKnownCandidateScansAvoided += Known.nSize - Page.nSize;
            clk = Abc_Clock();
            Cec_TranRootPrepareSeqFrontier( p, pRoots, nRoots, pFrontier,
                pCovered, pUsed, pMffc, vMffc, vSupport,
                fRefreshRoots, &ProofCands, &Prof );
            Prof.timeRootRefresh += Abc_Clock() - clk;
        }
        for ( i = 0; i < ProofCands.nSize; i++ )
        {
            int iKnown = Cec_TranCandVecFind( &Known,
                ProofCands.pArray + i );
            assert( iKnown >= 0 );
            Known.pArray[iKnown].nStatus = CEC_TRAN_STATE_TRIED_SEQ;
        }
        Prof.nRootWaveSubmitted[iProfWave] += ProofCands.nSize;
        if ( !fCombOnly )
            Cec_TranPrepareHelpers( p, &HistoryLive, &ProofCands,
                pPars->fUseHelpers, 1, &Prof, &Active );
        if ( ProofCands.nSize )
        {
            int nNewProved = Cec_TranRootProvePortfolio( p, &Active,
                &ProofCands, pPars, &Prof, &BatchProved, fCombOnly,
                iPhase );
            Prof.nRootWaveProved[iProfWave] += nNewProved;
            Prof.nRootNewProved += nNewProved;
            for ( i = 0; i < BatchProved.nSize; i++ )
            {
                if ( !Cec_TranCandVecContains(&HistoryLive,
                        BatchProved.pArray + i) )
                    Cec_TranCandVecPush( &HistoryLive,
                        BatchProved.pArray[i] );
                if ( !Cec_TranCandVecContains(&Proved,
                        BatchProved.pArray + i) )
                    Cec_TranCandVecPush( &Proved,
                        BatchProved.pArray[i] );
            }
        }
        if ( Proved.nSize && !fMicroBatch )
        {
            clk = Abc_Clock();
            nSelected = Cec_TranRootConsumeProved( p, &Proved,
                pCovered, pUsed, pSolved, pMffc, vMffc,
                vSupport, &Selected, &Prof );
            Prof.timeRootPostSelect += Abc_Clock() - clk;
            Prof.nRootWaveSelected[iProfWave] += nSelected;
        }
        if ( fCombOnly && !fMicroBatch )
            break;
    }

    // In opt-in micro-batch mode every proof result remains metadata on the
    // immutable snapshot until the per-root q horizon (or iterator end) is
    // reached.  HistoryLive was already passed to every later SEQ proof as H,
    // so this is the first selection point, not a second proof phase.
    if ( fMicroBatch && Proved.nSize )
    {
        int iProfWave = Abc_MinInt(Abc_MaxInt(nWaves - 1, 0), 63);
        clk = Abc_Clock();
        nSelected = Cec_TranRootConsumeProved( p, &Proved,
            pCovered, pUsed, pSolved, pMffc, vMffc,
            vSupport, &Selected, &Prof );
        Prof.timeRootPostSelect += Abc_Clock() - clk;
        Prof.nRootWaveSelected[iProfWave] += nSelected;
    }

    for ( i = 0; i < Selected.nSize; i++ )
        Prof.nRootHistorySelected +=
            Cec_TranCandVecContains(pHistory, Selected.pArray + i);

    Prof.DiagRootAvailable = fMicroBatch;
    if ( fMicroBatch )
        for ( r = 0; r < nRoots; r++ )
            if ( pRoots[r].nMffc > 0 )
            {
                Cec_TranRootCursor_t const * pCursor =
                    pCursors + pRoots[r].iObj;
                nBuildAcceptedTotal += pCursor->nBuildAccepted;
                nBuildAcceptedMax = Abc_MaxInt( nBuildAcceptedMax,
                    pCursor->nBuildAccepted );
                nBuildHorizonRoots += pPars->fUseConstr &&
                    Cec_TranRootBuildHorizonReached(pPars, pCursor);
                if ( pPars->fUseConstr &&
                     Cec_TranRootBuildEligible(pRoots + r) )
                {
                    nBuildEligibleRoots++;
                    if ( pPars->fProfile )
                    {
                        // Raw includes canonical direct results; Valid is the
                        // historical nonzero-gate yield. Keep not-started
                        // separate from an iterator that searched unsuccessfully.
                        int c = pCursor->nBuildAccepted > 0 ?
                            (pPars->nRootConstrTop > 0 &&
                             pCursor->nBuildAccepted >= pPars->nRootConstrTop ? 7 : 6) :
                            pCursor->fExpConflict && (pPars->nExplore & 4) ? 0 :
                            !pCursor->nPages ? 1 :
                            !pCursor->nDiagRaw ? 2 :
                            !pCursor->nDiagPositive ? 3 :
                            pCursor->nBuildYield == pCursor->nDiagPositive &&
                            !pCursor->nDiagCollapsed && !pCursor->nDiagInvalid ? 4 : 5;
                        Cec_TranDiagBucket_t * d = &Prof.DiagRoots[c];
                        d->Roots++;
                        d->Started += pCursor->nPages > 0;
                        d->Exhausted += pCursor->fExhausted && pCursor->nPages > 0;
                        d->Next += pCursor->nDiagNext;
                        d->Raw += pCursor->nDiagRaw;
                        d->Valid += pCursor->nBuildYield;
                        d->Positive += pCursor->nDiagPositive;
                        d->Nonpositive += pCursor->nBuildYield - pCursor->nDiagPositive;
                        d->Duplicate += pCursor->nDiagPositive - pCursor->nBuildAccepted;
                        d->Collapsed += pCursor->nDiagCollapsed;
                        d->Invalid += pCursor->nDiagInvalid;
                        d->Accepted += pCursor->nBuildAccepted;
                        d->Pivots += pCursor->nDiagPivots;
                        d->EnumTime += pCursor->timeDiagEnum;
                        d->BuildTime += pCursor->timeExpBuild;
                    }
                    if ( pCursor->nBuildAccepted == 0 )
                    {
                        Prof.timeExpZeroBuild += pCursor->timeExpBuild;
                        Prof.timeExpZeroRank += pCursor->timeExpRank;
                    }
                    else
                    {
                        Prof.timeExpPositiveBuild += pCursor->timeExpBuild;
                        Prof.timeExpPositiveRank += pCursor->timeExpRank;
                    }
                    nBuildZeroAcceptedRoots +=
                        pCursor->nBuildAccepted == 0;
                    if ( pPars->nRootConstrTop > 0 &&
                         pCursor->nBuildAccepted >=
                            pPars->nRootConstrTop )
                        nBuildAtQRoots++;
                    else if ( pCursor->fExhausted )
                        nBuildExhaustedBeforeQRoots++;
                    else
                        nBuildUnfinishedBelowQRoots++;
                }
            }

    // Keep every still-live old certificate and every newly proved relation
    // that was not consumed by this commit.  Selected relations map to their
    // replacement and are deliberately removed from the carry set.
    for ( i = 0; i < HistoryLive.nSize; i++ )
        if ( !Cec_TranCandVecContains(&Selected, HistoryLive.pArray + i) )
            Cec_TranCandVecPush( &Carry, HistoryLive.pArray[i] );

    // All proof and discovery data refer to the one immutable snapshot.  Tear
    // them down before the sole bundle duplication stops that snapshot.
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        Cec_TranRootCursorStop( pCursors + i );
    Cec_TranDepScratchStop( &Dep );
    Abc_ResubPrepareManager( 0 );
    Abc_ResubSetBothPolarities( 0 );
    if ( pSim != pSource )
        Cec_TranSimStop( pSim );
    Cec_TranSimStop( pSource );
    if ( fOwnDb )
        Cec_TranPatDbStop( pDb );
    pSim = NULL;
    pSource = NULL;
    if ( fUseTfoDivs )
        Gia_ManStaticFanoutStop( p );
    p = Cec_TranCommitSelectedRootOnly( p, &Selected, pPars, &Prof,
        &Carry, pHistory );
    Prof.nHelperInvalidated = Prof.nHistoryTriedInvalidated;
    Prof.nHelperRetained = Abc_MaxInt(
        Prof.nHelperRetained, pHistory->nSize );
    Prof.timeRootDivCi = Prof.timeRootDivPool;
    Prof.timeRootResubInit = Prof.timeRootDepInit;
    Prof.timeRootResubEnumCanon = Prof.timeRootDepSearch;
    Prof.timeRootCbsSolve = Prof.timeCombSolve;
    Prof.timeTotal = Abc_Clock() - clkTotal;
    if ( pPars->fProfile )
        Cec_TranPrintRootOnlyProfile( &Prof, nAndBefore, Gia_ManAndNum(p),
            nRegBefore, Gia_ManRegNum(p), Abc_MinInt(nWaves, 64), iPhase, 0 );
    if ( fUseTfoDivs )
    {
        Abc_Print( 1, "stran-root TFO profile: schema=1 phase=%s mode=shell cap=%d calls=%lld seeds=%lld scanned=%lld fanout-edges=%lld added=%lld selected-pool=%lld limit-hits=%lld max-added=%d closure-sec=%.6f.\n",
            fCombOnly ? "comb" : "seq",
            nTfoMax, Prof.nRootTfoCalls, Prof.nRootTfoSeeds,
            Prof.nRootTfoScanned, Prof.nRootTfoEdges, Prof.nRootTfoAdded,
            Prof.nRootTfoSelected, Prof.nRootTfoLimitHits,
            Prof.nRootTfoAddedMax, Cec_TranTimeSec(Prof.timeRootDivTfo) );
        Abc_Print( 1, "stran-root TFO core-rescue profile: schema=3 phase=%s calls=%lld skipped-no-extra=%lld exact=%lld rescued-roots=%lld rescued-nodes=%lld value-trials=%lld value-exact=%lld value-changed=%lld value-unlocked=%lld value-sec=%.6f.\n",
            fCombOnly ? "comb" : "seq", Prof.nRootTfoCoreRescueCalls,
            Prof.nRootTfoCoreRescueNoExtra,
            Prof.nRootTfoCoreRescueExact, Prof.nRootTfoCoreRescueRoots,
            Prof.nRootTfoCoreRescueNodes,
            Prof.nRootTfoCoreValueTrials, Prof.nRootTfoCoreValueExact,
            Prof.nRootTfoCoreValueChanged, Prof.nRootTfoCoreValueUnlocked,
            Cec_TranTimeSec(Prof.timeRootTfoCoreValue) );
    }
    if ( pPars->nKitCoreMax )
        Abc_Print( 1, "stran-root Kit portfolio profile: schema=2 phase=%s core-max=%d calls=%lld separated=%lld synthesized=%lld accepted=%lld generated=%lld submitted=%lld proved=%lld selected=%lld selected-and-gain=%lld.\n",
            fCombOnly ? "comb" : "seq", pPars->nKitCoreMax,
            Prof.nRootKitCoreCalls, Prof.nRootKitCoreSeparated,
            Prof.nRootKitSynthesized, Prof.nRootKitAccepted,
            Prof.nRootKitOutcome[0], Prof.nRootKitSubmitted,
            Prof.nRootKitOutcome[1], Prof.nRootKitOutcome[2],
            Prof.nRootKitSelectedGain );
    if ( pPars->fBdcPortfolio )
        Abc_Print( 1, "stran-root BDC portfolio profile: schema=1 phase=%s core-max=%d calls=%lld separated=%lld synthesized=%lld accepted=%lld generated=%lld submitted=%lld proved=%lld selected=%lld selected-and-gain=%lld.\n",
            fCombOnly ? "comb" : "seq", pPars->nKitCoreMax,
            Prof.nRootBdcCoreCalls, Prof.nRootBdcCoreSeparated,
            Prof.nRootBdcSynthesized, Prof.nRootBdcAccepted,
            Prof.nRootBdcOutcome[0], Prof.nRootBdcSubmitted,
            Prof.nRootBdcOutcome[1], Prof.nRootBdcOutcome[2],
            Prof.nRootBdcSelectedGain );
    Cec_TranSuppProfStop( Prof.pBuildSuppProf );
    Prof.pBuildSuppProf = NULL;
    Abc_Print( 1, "stran-root summary: round=%d phase=%s roots=%d selected=%d comb-proved=%d seq-proved=%d unique-proved=%d AND=%d->%d exact-gain=%lld.\n",
        iRound + 1, fCombOnly ? "comb" : "seq", nRoots,
        Selected.nSize, Prof.nCombProved, Prof.nSeqProved,
        Proved.nSize, nAndBefore, Gia_ManAndNum(p),
        Prof.nRootBundleAndGain );
    Abc_Print( 1, "stran-root wave portfolio: waves=%d continuations=%d new-proved=%d history-proved-selected=%d unique-proved=%d proof-calls=%d exhausted=%s.\n",
        Prof.nRootProofWaves, Prof.nRootWaveContinues,
        Prof.nRootNewProved, Prof.nRootHistorySelected, Proved.nSize,
        Prof.nRootBatchCalls,
        fSnapshotExhausted ? "yes" : "no" );
    if ( fMicroBatch )
        Abc_Print( 1, "stran-root proof micro-batch summary: proof-waves=%d proof-calls=%d build-accepted-total=%d build-accepted-max-per-root=%d roots-at-horizon=%d stop=%s selected-after-stop=%d.\n",
            Prof.nRootProofWaves, Prof.nRootBatchCalls,
            nBuildAcceptedTotal, nBuildAcceptedMax, nBuildHorizonRoots,
            fCommitHorizonReached ? "commit-horizon" : "no-new-candidate",
            Selected.nSize );
    if ( fMicroBatch && pPars->fProfile )
        Abc_Print( 1, "stran-root build-horizon profile: schema=1 phase=%s q-limit=%d eligible-roots=%d q-slot-capacity=%lld q-slots-used=%d at-q-roots=%d exhausted-before-q-roots=%d unfinished-below-q-roots=%d zero-accepted-roots=%d accepted-total=%d accepted-max-per-root=%d.\n",
            fCombOnly ? "comb" : "seq", pPars->nRootConstrTop,
            nBuildEligibleRoots,
            (long long)pPars->nRootConstrTop * nBuildEligibleRoots,
            nBuildAcceptedTotal, nBuildAtQRoots,
            nBuildExhaustedBeforeQRoots, nBuildUnfinishedBelowQRoots,
            nBuildZeroAcceptedRoots, nBuildAcceptedTotal,
            nBuildAcceptedMax );
    if ( fMicroBatch )
        Abc_Print( 1, "stran-root immutable frontier reuse: refresh-calls=%d refresh-reuses=%d page-candidates=%lld known-candidate-scans-avoided=%lld.\n",
            nFrontierRefreshes, nFrontierRefreshReuses,
            nFrontierCandidates, nKnownCandidateScansAvoided );
    Abc_Print( 1, "stran-root cross-wave proof reuse: generation-skipped=%d remapped=%d invalidated=%d retained=%d.\n",
        Prof.nQueueTriedSkipped, Prof.nHistoryTriedRemapped,
        Prof.nHistoryTriedInvalidated, pHistory->nSize );
    if ( fRootBatch )
        Abc_Print( 1, "stran2 root-batch summary: root-signatures=%lld selector-calls=%lld roots-with-cex=%lld selected-cex-traces=%lld distinguishable-proxies=%lld covered-proxies=%lld selection-and-gather=%.6f sec.\n",
            Prof.nRootTeachCalls, Prof.nRootTeachSelections,
            Prof.nRootTeachWithCex,
            Prof.nRootTeachCexSelected, Prof.nRootTeachHypotheses,
            Prof.nRootTeachHypCovered, Cec_TranTimeSec(Prof.timeRootTeach) );
    Abc_Print( 1, "stran-root per-root candidates: discover-calls=%d total=%d max=%d avg=%.2f hist(0,1,2,3,4,5-8,9-16,17-32,33-64,65+)=%d,%d,%d,%d,%d,%d,%d,%d,%d,%d.\n",
        nCandCalls, nCandSum, nCandMax,
        nCandCalls ? (float)nCandSum / nCandCalls : 0.0f,
        nCandHist[0], nCandHist[1], nCandHist[2], nCandHist[3], nCandHist[4],
        nCandHist[5], nCandHist[6], nCandHist[7], nCandHist[8], nCandHist[9] );
    ABC_FREE( p->pRefs );
    Cec_TranCandVecStop( &Known );
    Cec_TranCandVecStop( &RootCands );
    Cec_TranCandVecStop( &Page );
    Cec_TranCandVecStop( &ProofCands );
    Cec_TranCandVecStop( &BatchProved );
    Cec_TranCandVecStop( &Proved );
    Cec_TranCandVecStop( &Selected );
    Cec_TranCandVecStop( &HistoryLive );
    Cec_TranCandVecStop( &Active );
    Cec_TranCandVecStop( &Carry );
    Vec_IntFree( vMffc );
    Vec_IntFree( vSupport );
    ABC_FREE( pMffc );
    ABC_FREE( pSolved );
    ABC_FREE( pCovered );
    ABC_FREE( pUsed );
    ABC_FREE( pRoots );
    ABC_FREE( pCursors );
    return p;
}

#include "cecTranOdc.h"
#include "cecTranConstHelperTest.h"
#include "cecTranRelObs.h"
#include "cecTranTraceBuild.h"

static Gia_Man_t * Cec_ManSequentialTransductionInt( Gia_Man_t * pGia,
    Cec_ParTran_t * pPars, Cec_TranPatDb_t * pDb, int fRootBatch )
{
    Cec_ParTran_t PassPars, StrictPars = *pPars, * pGlobalPars = pPars;
    Cec_TranCandVec_t ProofHistory = {0};
    Gia_Man_t * p = Gia_ManDup( pGia );
    Gia_Man_t * pNext;
    int iRound, nAndInitial = Gia_ManAndNum(p);
    int nCombPasses = 0, nCombCommits = 0;
    int nSeqPasses = 0, nSeqCommits = 0;
    Cec_TranStrictCex_t * pStrictCex = Cec_TranStrictCexStart( pGia, pPars );
    StrictPars.fOdcProofScope = 0;
    if ( StrictPars.nStrictSteps >= -1 ) StrictPars.nStepsMax = StrictPars.nStrictSteps;
    if ( StrictPars.nStrictWaves >= 0 ) StrictPars.nRootWaves = StrictPars.nStrictWaves;
    if ( Abc_ResubQualityNoTruncation() )
    {
        StrictPars.nConstrMax = StrictPars.nConstrBaseMax = 0;
        StrictPars.nRootConstrTop = 0;
        StrictPars.nRootWaves = 0;
    }
    pPars = &StrictPars;
    if ( Abc_ResubQualityNoTruncation() || Cec_TranQualityActualCost() )
        Abc_Print(1, "stran-quality options: no-truncation=%d actual-cost=%d N=%d T=%d D=%d j=%d; finite grammar, unchanged proof/commit.\n",
            Abc_ResubQualityNoTruncation(), Cec_TranQualityActualCost(),
            pPars->nDepNodesMax, pPars->nKitCoreMax, pPars->fBdcPortfolio,
            pPars->nRootProofBatch);
    Abc_Print(1,"stran-strict options: S=%d w=%d.\n",pPars->nStepsMax,pPars->nRootWaves);
    // Run arbitrary-state combinational proof exactly once on the initial
    // graph.  COM owns a fixed q=4 frontier, ignores the SEQ proof micro-batch
    // control, and therefore reaches selection after one proof batch.  It then
    // drains every profitable proved certificate through as many conflict-free
    // commit waves as needed.  Opportunities exposed later belong to SEQ.
    {
        int nBefore = Gia_ManAndNum( p );
        int nAfterFirst, nAfter, nClosureBatches = 0;
        PassPars = *pPars;
        PassPars.nRootWaves = 1;
        PassPars.nRootConstrTop = CEC_TRAN_COMB_BUILD_Q;
        PassPars.nRootProofBatch = Abc_ResubQualityNoTruncation() ?
                pPars->nRootProofBatch : 0;
        pNext = Cec_ManSequentialRootPass( p, &PassPars,
            0, 1, &ProofHistory, pDb, fRootBatch, NULL );
        Gia_ManStop( p );
        p = pNext;
        nAfterFirst = Gia_ManAndNum( p );
        p = Cec_TranDrainProvedCommits( p, pPars, &ProofHistory,
            0, 0, &nClosureBatches );
        nAfter = Gia_ManAndNum( p );
        nCombPasses = 1;
        nCombCommits = (nAfterFirst < nBefore) + nClosureBatches;
        Abc_Print( 1, "stran-root initial commit closure: phase=comb batches=%d AND=%d->%d gain=%d.\n",
            nCombCommits, nBefore, nAfter, nBefore - nAfter );
    }

    // Every later epoch is sequential.  It may consume several no-commit
    // q-waves on one immutable proof snapshot.  Once it proves a profitable
    // pool, the pool is drained to a commit fixed point before any candidate
    // generation/proof state is rebuilt.  With -w 0, strict AND-count descent
    // across proof epochs is the termination measure.
    for ( iRound = 0; pPars->nRootWaves == 0 ||
         iRound < pPars->nRootWaves; iRound++ )
    {
        int nBefore, nAfterFirst, nAfter, nClosureBatches = 0;
        nBefore = Gia_ManAndNum( p );
        PassPars = *pPars;
        PassPars.nRootWaves = 1;
        {
        Cec_TranPatDb_t * pTeach = Cec_TranStrictCexTeach( pStrictCex, p, pDb );
        pNext = Cec_ManSequentialRootPass( p, &PassPars,
            iRound, 0, &ProofHistory, pTeach ? pTeach : pDb,
            pTeach ? Vec_PtrSize(pTeach->vCexes) > 64 * pPars->nSimWords : fRootBatch,
            pStrictCex );
        if ( pTeach ) Cec_TranPatDbStop( pTeach );
        Cec_TranStrictCexPrint( pStrictCex, iRound + 1 );
        }
        Gia_ManStop( p );
        p = pNext;
        nAfterFirst = Gia_ManAndNum( p );
        p = Cec_TranDrainProvedCommits( p, pPars, &ProofHistory,
            iRound, 1, &nClosureBatches );
        nAfter = Gia_ManAndNum( p );
        nSeqPasses++;
        nSeqCommits += (nAfterFirst < nBefore) + nClosureBatches;
        Abc_Print( 1, "stran-root epoch commit closure: epoch=%d phase=seq batches=%d AND=%d->%d gain=%d.\n",
            iRound + 1, (nAfterFirst < nBefore) + nClosureBatches,
            nBefore, nAfter, nBefore - nAfter );
        if ( nAfter >= nBefore )
            break;
    }
    Abc_Print( 1, "stran-root epochs summary: configured=%d completed=%d comb-epochs=%d comb-batches=%d seq-epochs=%d seq-batches=%d AND=%d->%d gain=%d.\n",
        pPars->nRootWaves, nSeqPasses, nCombPasses, nCombCommits,
        nSeqPasses, nSeqCommits, nAndInitial, Gia_ManAndNum(p),
        nAndInitial - Gia_ManAndNum(p) );
    Cec_TranCandVecStop( &ProofHistory );
    Cec_TranStrictCexStop( pStrictCex );
    pPars = pGlobalPars;
    if ( pPars->fUseOdc )
        p = Cec_TranRunOdcSerial( p, pPars, pDb );
    assert(!pPars->nRelObs || pPars->fOutputProof);
    if ( pPars->nRelObs )
        Abc_Print(1,"stran-proof-boundary prefix=%s tail=%s reset=zero all-cycles=1 mode=%d feedback=%d extra-window=%d extra-state=%d\n",
            pPars->fUseOdc?"window":"root",pPars->fOutputProof?"output":"window",pPars->nRelObs,
            pPars->nRelObs==27,0,0);
    if ( pPars->nRelObs == 27 )
    {
        Cec_ParTran_t tail=*pPars;
        // This is the same frozen Direct-only algorithm, with no intervening
        // scorr or state cleanup. Attribute the subsequent Build separately.
        Abc_Print(1,"stran-direct-prefix boundary=output mode=6 next=trace mode-next=27\n");
        tail.nRelObs=6; tail.fOutputProof=1; p=Cec_TranRunRelObs(p,&tail);
        tail.nRelObs=27; tail.fOutputProof=1;
        p=Cec_TranRunTraceBuild(p,&tail);
    }
    else if ( pPars->nRelObs == 6 )
        p = Cec_TranRunRelObs( p, pPars );
    return p;
}

static int Cec_TranOdcRelationalBoundarySelfTest()
{
    char const * Env = "ABC_ODC_RELATIONAL_PROOF";
    char * SavedEnv = getenv(Env) ? Abc_UtilStrsav(getenv(Env)) : NULL;
    Cec_ParTran_t Pars, SavedPars;
    Cec_TranProf_t Prof;
    Cec_TranCand_t Cand, Helpers[2];
    Cec_TranCandVec_t Obs = {0}, Frontier = {0};
    Gia_Man_t * p, * pClean;
    Vec_Int_t * vStatus;
    Vec_Str_t * vStage;
    int a, b, q, r, g, z, Full, i, Factor, nTried, nSelected;
    int KindSelected[3], KindGain[3];
    long long nObligations, nProved, nBatches;
    abctime TimeProof;
    if ( setenv(Env,"1",1) ) abort();
    Cec_ManTranSetDefaultParams(&Pars);
    Pars.fOdcFanout=Pars.fOdcProofScope=1;
    Pars.nFrames=1; Pars.nBTLimit=Pars.nCombBTLimit=1000;
    Pars.nStepsMax=-1; Pars.nExplore=134217728;
    Pars.nDepNodesMax=20; Pars.nOdcProofMax=0;
    Pars.fUseFreeSim=0;
    SavedPars=Pars;

    // r=a&b is invariant under the original swap transition.  The factor
    // wrapper must propagate a complete certificate and distinguish S0.
    p=Gia_ManStart(16);
    a=Gia_ManAppendCi(p); b=Gia_ManAppendCi(p);
    r=Gia_ManAppendAnd(p,a,b);
    Gia_ManAppendCo(p,r); Gia_ManAppendCo(p,b); Gia_ManAppendCo(p,a);
    Gia_ManSetRegNum(p,2); Gia_ManStaticFanoutStart(p);
    Cand=Cec_TranCandCreateLiteral(Abc_Lit2Var(r),0,1,CEC_TRAN_CAND_CONST,0);
    memset(&Prof,0,sizeof(Prof));
    vStatus=Cec_TranProveWindowFactorBatch(p,NULL,0,&Cand,1,&Pars,&Prof,0,&vStage,&Full);
    assert(Vec_IntSize(vStatus)==1 && Vec_StrSize(vStage)==1);
    assert(Vec_IntEntry(vStatus,0)==1 && Vec_StrEntry(vStage,0)==2);
    Vec_IntFree(vStatus); Vec_StrFree(vStage);
    Pars.nStepsMax=0; memset(&Prof,0,sizeof(Prof));
    vStatus=Cec_TranProveWindowFactorBatch(p,NULL,0,&Cand,1,&Pars,&Prof,0,&vStage,&Full);
    assert(Vec_IntEntry(vStatus,0)==0 && Vec_StrEntry(vStage,0)==0);
    assert(Prof.nSeqUnknown>0);
    Vec_IntFree(vStatus); Vec_StrFree(vStage); Pars=SavedPars;
    Gia_ManStaticFanoutStop(p); Gia_ManStop(p);

    // For every free state, (a&b)&a equals b&a.  S0 cannot downgrade a
    // universal CBS certificate, regardless of the legal next-state logic.
    p=Gia_ManStart(16);
    a=Gia_ManAppendCi(p); b=Gia_ManAppendCi(p);
    r=Gia_ManAppendAnd(p,a,b); g=Gia_ManAppendAnd(p,r,a);
    Gia_ManAppendCo(p,g); Gia_ManAppendCo(p,b); Gia_ManAppendCo(p,a^1);
    Gia_ManSetRegNum(p,2); Gia_ManStaticFanoutStart(p);
    Cand=Cec_TranCandCreateLiteral(Abc_Lit2Var(r),b,1,CEC_TRAN_CAND_EXIST,0);
    Pars.nStepsMax=0; memset(&Prof,0,sizeof(Prof));
    vStatus=Cec_TranProveWindowFactorBatch(p,NULL,0,&Cand,1,&Pars,&Prof,0,&vStage,&Full);
    assert(Vec_IntEntry(vStatus,0)==1 && Vec_StrEntry(vStage,0)==1);
    assert(Prof.nSeqCands==0 && Prof.nSeqUnknown==0);
    Vec_IntFree(vStatus); Vec_StrFree(vStage);

    // Only the ODC proof scope reads the opt-in environment.  Keep the
    // fanout feature set while proving a simple universal root equality.
    Pars.fOdcProofScope=0;
    if ( setenv(Env,"invalid-outside-odc",1) ) abort();
    Cand=Cec_TranCandCreateLiteral(Abc_Lit2Var(g),r,1,CEC_TRAN_CAND_EXIST,1);
    memset(&Prof,0,sizeof(Prof));
    vStatus=Cec_TranProveRootBatch(p,NULL,0,&Cand,1,&Pars,&Prof,1,&vStage);
    assert(Vec_IntEntry(vStatus,0)==1 && Vec_StrEntry(vStage,0)==1);
    Vec_IntFree(vStatus); Vec_StrFree(vStage);
    if ( setenv(Env,"1",1) ) abort();
    Pars=SavedPars;
    Gia_ManStaticFanoutStop(p); Gia_ManStop(p);

    // A false first helper catches a missing nHelpers result offset.  The
    // surviving b=0 helper and a=0 obligation are mutually inductive; q=0
    // fails and is withdrawn before their complete fixed-point round.
    p=Gia_ManStart(16);
    a=Gia_ManAppendCi(p); b=Gia_ManAppendCi(p); q=Gia_ManAppendCi(p);
    Gia_ManAppendCo(p,a);
    Gia_ManAppendCo(p,b); Gia_ManAppendCo(p,a); Gia_ManAppendCo(p,1);
    Gia_ManSetRegNum(p,3);
    Helpers[0]=Cec_TranCandCreateLiteral(Abc_Lit2Var(q),0,0,CEC_TRAN_CAND_CONST,1);
    Helpers[1]=Cec_TranCandCreateLiteral(Abc_Lit2Var(b),0,0,CEC_TRAN_CAND_CONST,1);
    Cand=Cec_TranCandCreateLiteral(Abc_Lit2Var(a),0,0,CEC_TRAN_CAND_CONST,1);
    memset(&Prof,0,sizeof(Prof));
    vStatus=Cec_TranProveRootBatch(p,Helpers,2,&Cand,1,&Pars,&Prof,0,&vStage);
    assert(Vec_IntSize(vStatus)==1 && Vec_StrSize(vStage)==1);
    assert(Vec_IntEntry(vStatus,0)==1 && Vec_StrEntry(vStage,0)==2);
    assert(Prof.nSeqSeeded==3 && Prof.nSeqFixedRounds==2);
    Vec_IntFree(vStatus); Vec_StrFree(vStage);
    memset(&Prof,0,sizeof(Prof));
    vStatus=Cec_TranProveRootBatch(p,Helpers,1,&Cand,1,&Pars,&Prof,0,&vStage);
    assert(Vec_IntEntry(vStatus,0)==0 && Vec_StrEntry(vStage,0)==0);
    assert(Prof.nSeqSplit>0 && Prof.nSeqUnknown==0);
    Vec_IntFree(vStatus); Vec_StrFree(vStage); Gia_ManStop(p);

    // The first exit is universally preserved, but the second observes the
    // edit after reset: a'=0,b'=1 makes b&!a=1 while r&!a remains zero.
    // Test the actual all-exit acceptance gate with and without factoring.
    p=Gia_ManStart(16);
    a=Gia_ManAppendCi(p); b=Gia_ManAppendCi(p);
    r=Gia_ManAppendAnd(p,a,b); g=Gia_ManAppendAnd(p,r,a);
    z=Gia_ManAppendAnd(p,r,a^1);
    Gia_ManAppendCo(p,g); Gia_ManAppendCo(p,z);
    Gia_ManAppendCo(p,0); Gia_ManAppendCo(p,1);
    Gia_ManSetRegNum(p,2); Gia_ManCreateRefs(p);
    Cand=Cec_TranCandCreateLiteral(Abc_Lit2Var(r),b,1,CEC_TRAN_CAND_EXIST,0);
    Cand.Gain=1; Pars.nFrames=2;
    Gia_ManStaticFanoutStart(p);
    Cec_TranWindowObligations(p,&Cand,&Pars,&Obs);
    assert(Obs.nSize==2);
    memset(&Prof,0,sizeof(Prof));
    vStatus=Cec_TranProveRootBatch(p,NULL,0,Obs.pArray,Obs.nSize,&Pars,&Prof,0,&vStage);
    for ( i=0; i<Obs.nSize; i++ )
    {
        assert(Obs.pArray[i].iTarget==Abc_Lit2Var(g) ||
            Obs.pArray[i].iTarget==Abc_Lit2Var(z));
        if ( Obs.pArray[i].iTarget==Abc_Lit2Var(g) )
            assert(Vec_IntEntry(vStatus,i)==1 && Vec_StrEntry(vStage,i)==1);
        else
            assert(Vec_IntEntry(vStatus,i)==0 && Vec_StrEntry(vStage,i)==0);
    }
    assert(Prof.nSeqSplit>0 && Prof.nSeqUnknown==0);
    Vec_IntFree(vStatus); Vec_StrFree(vStage);
    Cec_TranCandVecStop(&Obs); Gia_ManStaticFanoutStop(p);
    Cec_TranCandVecPush(&Frontier,Cand);
    for ( Factor=0; Factor<2; Factor++ )
    {
        Pars.fWindowFactor=Factor; memset(&Prof,0,sizeof(Prof));
        memset(KindSelected,0,sizeof(KindSelected));
        memset(KindGain,0,sizeof(KindGain));
        nTried=nSelected=0; nObligations=nProved=nBatches=0;
        pClean=Cec_TranOdcFanoutRound(p,&Frontier,NULL,0,&Pars,&Prof,0,
            &nTried,&nSelected,&nObligations,&nProved,&nBatches,&TimeProof,
            KindSelected,KindGain);
        assert(nTried==1 && nSelected==0 && nProved==0 && !pClean);
        assert(nObligations==(Factor ? 1 : 2) && nBatches>0);
        assert(Prof.nSeqSplit>0 && Prof.nSeqUnknown==0);
    }
    Cec_TranCandVecStop(&Frontier); Gia_ManStop(p); Pars=SavedPars;
    if ( SavedEnv )
    {
        if ( setenv(Env,SavedEnv,1) ) abort();
        ABC_FREE(SavedEnv);
    }
    else if ( unsetenv(Env) ) abort();
    Abc_Print(1,"stran ODC relational scope/helper/UNKNOWN/CBS/all-exit boundary self-test: PASS\n");
    return 1;
}

Gia_Man_t * Cec_ManSequentialTransduction( Gia_Man_t * pGia,
    Cec_ParTran_t * pPars )
{
    return Cec_ManSequentialTransductionInt( pGia, pPars, NULL, 0 );
}

// Run the same no-option scorr prepass used by "&scorr", retain only its
// reset-reachable packed CEX lanes, project them through register reduction,
// and freeze the corpus.  CEX replace random lanes inside Q.  If the corpus
// exceeds 64*Q traces, a wider source is simulated once and each root receives
// an adaptive Q-word batch of complete traces across all W frames.
Gia_Man_t * Cec_ManSequentialTransduction2( Gia_Man_t * pGia,
    Cec_ParTran_t * pPars )
{
    Cec_ParCor_t Cor;
    Cec_ProfCor_t CorrProf;
    Cec_TranPatDb_t * pDb;
    Gia_Man_t * pScorr, * pNew;
    abctime TimeScorr;
    int nCexMax = pPars->nSimWords >= 16 ? 1024 :
        Abc_MaxInt( 256, 64 * pPars->nSimWords );
    int fRootBatch;
    pDb = Cec_TranPatDbStart( pGia, nCexMax );
    pDb->nFramesMax = pPars->nSimFrames;
    Cec_ManCorSetDefaultParams( &Cor );
    memset( &CorrProf, 0, sizeof(CorrProf) );
    // The integrated prepass is part of &stran2's proof policy.  Honor the
    // command's -F/-C settings here as well as in the later transaction
    // certificates, so deeper correspondence can remove Direct/Existing
    // opportunities before the Build search consumes its candidate budget.
    Cor.nFrames = pPars->nInitialFrames < 0 ? pPars->nFrames : pPars->nInitialFrames;
    Cor.nBTLimit = pPars->nInitialConflicts < 0 ? pPars->nBTLimit : pPars->nInitialConflicts;
    Cor.nProcs = 1;
    Cor.pProfile = pPars->fProfile ? &CorrProf : NULL;
    if ( Cec_TranStrictCexOption("ABC_STRICT_CEX_INITIAL", 1, 1) )
    {
        Cor.pCexFunc = Cec_TranPatDbObserveScorr;
        Cor.pCexData = pDb;
    }
    Cor.fCollectRegMap = 1;
    Abc_Print( 1, "stran2: running integrated scorr; reachable-CEX capacity=%d.\n",
        nCexMax );
    Abc_Print( 1, "stran2 initial scorr config: F=%d C=%d.\n", Cor.nFrames, Cor.nBTLimit );
    TimeScorr = Abc_Clock();
    pScorr = Cec_ManLSCorrespondence( pGia, &Cor );
    TimeScorr = Abc_Clock() - TimeScorr;
    if ( pPars->fProfile )
        Abc_Print( 1, "stran2 initial scorr profile: schema=1 frames=%d conflict-limit=%d source-and=%d result-and=%d source-reg=%d result-reg=%d completed=%d rounds=%d bmc-unsat=%lld bmc-sat=%lld bmc-unknown=%lld induction-unsat=%lld induction-sat=%lld induction-unknown=%lld conflicts=%lld total-sec=%.6f bmc-sec=%.6f induction-sec=%.6f reduce-sec=%.6f.\n",
            Cor.nFrames, Cor.nBTLimit, Gia_ManAndNum(pGia),
            Gia_ManAndNum(pScorr), Gia_ManRegNum(pGia), Gia_ManRegNum(pScorr),
            Cor.fCompleted, Cor.nRoundsDone,
            CorrProf.nBmcUnsat, CorrProf.nBmcSat, CorrProf.nBmcUnknown,
            CorrProf.nIndUnsat, CorrProf.nIndSat, CorrProf.nIndUnknown,
            CorrProf.nConfUsed, Cec_TranTimeSec(TimeScorr),
            1.0e-9 * CorrProf.timeBmc, 1.0e-9 * CorrProf.timeInd,
            1.0e-9 * CorrProf.timeReduce );
    Cec_TranPatDbRemapRegs( pDb, Gia_ManRegNum(pScorr), Cor.vRegMap );
    Vec_IntFreeP( &Cor.vRegMap );
    Cec_TranPatDbSeal( pDb );
    Abc_Print( 1, "stran2 CEX corpus: retained=%d/%d packed-lanes-seen=%d duplicates=%d ignored-induction=%d too-long=%d words=%d.\n",
        Vec_PtrSize(pDb->vCexes), pDb->nMax, pDb->nSeen, pDb->nDup,
        pDb->nIgnoredInd, pDb->nTooLong,
        Vec_IntSize(pDb->vBatchEnds) );
    if ( Gia_ManRegNum(pScorr) == 0 )
    {
        Cec_TranPatDbStop( pDb );
        return pScorr;
    }
    fRootBatch = Vec_PtrSize(pDb->vCexes) > 64 * pPars->nSimWords;
    Abc_Print( 1, "stran2 CEX placement: mode=%s trace-budget=%d retained=%d random-fill=%d overflow=%d.\n",
        fRootBatch ? "root-batch" : "direct",
        64 * pPars->nSimWords, Vec_PtrSize(pDb->vCexes),
        fRootBatch ? 0 : 64 * pPars->nSimWords -
            Vec_PtrSize(pDb->vCexes),
        fRootBatch ? Vec_PtrSize(pDb->vCexes) -
            64 * pPars->nSimWords : 0 );
    pNew = Cec_ManSequentialTransductionInt( pScorr, pPars, pDb,
        fRootBatch );
    Gia_ManStop( pScorr );
    Cec_TranPatDbStop( pDb );
    return pNew;
}

ABC_NAMESPACE_IMPL_END
