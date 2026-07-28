/**CFile****************************************************************

  FileName    [cecTrans.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential transduction using SODC proof obligations.]

  Synopsis    [Candidate-and-prove sequential redundancy addition.]

  Description [This command is intentionally independent of &sodc.  It uses
  the BMC/induction machinery behind signal correspondence only as a bounded
  sequential proof oracle.  Its search space is speculative transduction:
  find a costly victim fanin, derive an added divisor, prove that adding it
  is redundant, prove that it makes the victim removable, and commit only a
  proved positive-gain transaction.]

***********************************************************************/

#include "cecInt.h"
#include "aig/gia/giaAig.h"
#include "sat/bmc/bmc.h"

ABC_NAMESPACE_IMPL_START

extern void Abc_ResubPrepareManager( int nWords );
extern int Abc_ResubComputeFunction( void ** ppDivs, int nDivs,
    int nWords, int nLimit, int nDivsMax, int iChoice, int fUseXor,
    int fDebug, int fVerbose, int ** ppArray );

void Cec_ManTranSetDefaultParams( Cec_ParTran_t * p )
{
    memset( p, 0, sizeof(Cec_ParTran_t) );
    p->nFrames     = 1;
    p->nBTLimit    = 1000;
    p->nStepsMax   = -1;
    p->nCandMax    = 0;
    p->nDivsMax    = 16;
    p->nConstrMax  = 8;
    p->nConstrBaseMax = 64;
    p->nDepNodesMax = 20;
    p->nVictimsMax = 1;
    p->nProfileTop = 20;
    p->nChangesMax = 0;
    p->nGainMin    = 1;
    p->nSimWords   = 4;
    p->nSimFrames  = 8;
    p->nCexFrames  = 4;
    p->nCexMax     = 64;
    p->nCexBatch   = 1;
    p->nProofWindow = 0;
    p->nProofScope = CEC_TRAN_PROOF_ROOT;
    p->nStrictPct  = 25;
    // Keep the default conservative: a small value such as 2 can merely move
    // the contextual scheduler to more low-value roots until -T is full,
    // increasing care/candidate overhead without reducing proof calls.  Users
    // profiling a large design can still request that aggressive rotation
    // explicitly with -J 2 (normally together with a larger -G).
    p->nLowUnknownMax = 8;
    p->nUnknownMax = 8;
    p->nRootBatch  = 0;
    p->nRootWaves  = 2;
    p->nRootConstrTop = 8;
    p->nScoutBTLimit = 100;
    p->nScoutConfTotal = 20000;
    p->nHardConfTotal = 1000000;
    // Keep the expensive budget genuinely selective.  On the profiling
    // corpus, lower thresholds promoted almost every large-root candidate
    // (including level_48's long stream of non-winning obligations).
    p->nHardGain   = 256;
    p->nRootGainMin = 0;
    p->nHardMffc   = 1024;
    p->fUseDirect  = 1;
    p->fUseSodc    = 0;
    p->fUseExisting = 1;
    p->fUseConstr  = 1;
}

typedef struct Cec_TranTargetProf_t_ Cec_TranTargetProf_t;
struct Cec_TranTargetProf_t_
{
    abctime timeTotal;
    abctime timeCare;
    abctime timeSearch;
    abctime timeGain;
    abctime timeWindow;
    abctime timeCexBmc;
    abctime timeProof;
    int     iRound;
    int     iTarget;
    int     nSuperLeaves;
    int     nCareBits;
    int     nVictimSets;
    int     nExistingChecks;
    int     nExistingMatched;
    int     nExistingRetained;
    int     nConstructChecks;
    int     nConstructMatched;
    int     nConstructRetained;
    int     nDuplicates;
    int     nGainCalls;
    int     nGainPositive;
    int     nGainRejected;
    int     nProofs;
    int     nRetainUnproved;
    int     nFinalUnproved;
    int     nAccepted;
    int     nWindowCalls;
    int     nWindowProved;
    int     nWindowExpanded;
    int     nCexBmcCalls;
    int     nCexBmcSat;
};

typedef struct Cec_TranProf_t_ Cec_TranProf_t;
struct Cec_TranProf_t_
{
    abctime timeTotal;
    abctime timeSim;
    abctime timeCare;
    abctime timeSpec;
    abctime timeExisting;
    abctime timeConstruct;
    abctime timeGain;
    abctime timeWindowMiter;
    abctime timeWindowCorr;
    abctime timeRetainMiter;
    abctime timeRetainCorr;
    abctime timeFinalMiter;
    abctime timeFinalCorr;
    abctime timeShadow;
    abctime timeCexBmc;
    abctime timeProofUnsat;
    abctime timeProofSat;
    abctime timeProofUnknown;
    abctime timeRootBatch;
    abctime timeCombBuild;
    abctime timeCombSolve;
    abctime timeSeqSolve;
    abctime timeRootStageEval;
    abctime timeRootCommit;
    abctime timeRootRescue;
    abctime timeRootBudget[2]; // low/high root-batch proof time
    abctime timeScout;
    abctime timeHardRescue;
    abctime timeUnknownFirst;
    abctime timeUnknownRepeat;
    abctime timeDirectKind[3];
    abctime timeDirectLane[2];
    Cec_ProfCor_t Corr;
    long long nDirectAndGain[3];
    long long nDirectRegGain[3];
    long long nRootBundleAndGain;
    long long nRootBundleRegGain;
    long long nCombConfUsed;
    long long nStageAndBefore;
    long long nStageAndAfterComb;
    long long nStageAndAfterSeq;
    long long nStageRegBefore;
    long long nStageRegAfterComb;
    long long nStageRegAfterSeq;
    int       nRootBundleCommits;
    int     nSimCalls;
    int     nCareCalls;
    int     nSpecCalls;
    int     nGainCalls;
    int     nRetainCalls;
    int     nFinalCalls;
    int     nShadowCalls;
    int     nWindowCalls;
    int     nWindowProved;
    int     nWindowExpanded;
    int     nCexBmcCalls;
    int     nCexBmcSat;
    int     nCexBmcUnknown;
    int     nCegisRestarts;
    int     nCexStored;
    int     nTargets;
    int     nTargetVictimSets;
    int     nTargetExistingChecks;
    int     nTargetExistingMatched;
    int     nTargetExistingRetained;
    int     nTargetConstructChecks;
    int     nTargetConstructMatched;
    int     nTargetConstructRetained;
    int     nTargetDuplicates;
    int     nTargetGainCalls;
    int     nTargetGainPositive;
    int     nTargetGainRejected;
    int     nTargetProofs;
    int     nTargetRetainUnproved;
    int     nTargetFinalUnproved;
    int     nTargetAccepted;
    int     nTargetMaxChecks;
    int     nProofUnsat;        // candidate relations/transactions proved
    int     nProofSat;          // rejected candidate with a mapped reachable CEX
    int     nProofUnknown;      // rejected candidate without a mapped reachable CEX
    int     nRootFastCalls;     // legacy profile column; root pre-stage was removed
    int     nRootFastProved;    // legacy profile column; always zero
    int     nScopeFallbacks;    // legacy profile column; always zero
    int     nCexSigRefreshes;   // append-only CEX signature blocks simulated
    int     nCexSigFiltered;    // queued candidates rejected by appended CEX blocks
    int     nCommitRefreshes;   // new snapshots built before proving after a commit
    int     nHistoryTriedRemapped;   // tried entries retained across successful commits
    int     nHistoryUnknownRemapped; // nonzero root/lane cooldowns retained across commits
    int     nHistoryTriedInvalidated;// tried entries invalidated in committed TFO
    int     nHistoryUnknownInvalidated;// unknown cooldowns invalidated in committed TFO
    int     nQueueTriedSkipped;      // regenerated exact candidates skipped by history
    int     nUnknownFirst;           // first UNKNOWN for a root/lane
    int     nUnknownRepeat;          // later UNKNOWNs for the same root/lane
    int     nRootBatchCalls;    // two-stage proof batches in root scope
    int     nRootSnapshots;     // immutable circuit snapshots entering root closure
    int     nRootClosures;      // shared relation batches on immutable snapshots
    int     nRootBatchCands;    // candidate relations submitted across batches
    int     nRootBatchProved;   // obligations retained by base+inductive refinement
    int     nRootBatchMax;      // largest submitted relation batch
    int     nRootPhaseCalls[2]; // initial-combined/refill root closures
    int     nRootPhaseCands[2]; // queried candidates in each root phase
    int     nRootPhaseProved[2];// proved candidates in each root phase
    int     nRootScreened;      // MFFC-ranked unique roots inspected by all batches
    int     nRootGainEvals;     // cached local MFFC-delta gain evaluations
    int     nRootValueFiltered; // screened roots below both root value thresholds
    int     nRootExistingSkipped;// roots below the large-MFFC existing threshold
    int     nRootExistingKept;  // existing (nonconstant) candidates admitted
    int     nCombCands;         // candidates checked by candidate-directed CBS
    int     nCombProved;        // combinationally proved candidates
    int     nCombDisproved;     // candidates with a combinational counterexample
    int     nCombUnknown;       // candidates not decided by CBS
    int     nCombCubeCalls;     // direct literal-cube CBS calls
    int     nCombTwoCubeCands;  // generic two-implication candidates
    int     nCombThreeCubeCands;// one-AND candidates split into three cubes
    int     nSeqCands;          // unresolved candidates sent to scorr
    int     nSeqProved;         // candidates proved only by scorr
    int     nCombSelected;      // final root winners proved by CBS
    int     nSeqSelected;       // final root winners proved by scorr
    int     nRootRescueCalls;   // legacy profile column; isolated retry was removed
    int     nRootRescueProved;  // legacy profile column; always zero
    int     nRootBudgetCalls[2];// low/high shared scorr invocations
    int     nRootBudgetCands[2];// low/high root obligations
    int     nRootBudgetProved[2];// low/high proved root obligations
    int     nRootBudgetConfStops[2];// low/high total-conflict cap stops
    long long nRootBudgetConfUsed[2];// low/high exact conflicts/backtracks
    int     nScoutCalls;        // contextual candidates tried at scout budget
    int     nScoutProved;       // contextual candidates proved by the scout
    int     nScoutConfStops;    // scouts reaching their total conflict cap
    int     nHardEligible;      // high-gain contextual candidates reaching proof
    int     nHardRescueCalls;   // contextual candidates promoted to high budget
    int     nHardRescueProved;  // high-budget contextual rescues proving the edit
    int     nHardConfStops;     // high-budget calls reaching their total conflict cap
    int     nContextValueRootSkips;// MFFC upper bound below -G before discovery
    long long nScoutConfUsed;   // exact scout conflicts/backtracks
    long long nHardConfUsed;    // exact contextual-rescue conflicts/backtracks
};

static double Cec_TranTimeSec( abctime Time )
{
    return 1.0 * Time / CLOCKS_PER_SEC;
}

static double Cec_TranTimeHrSec( abctime Time )
{
    return 1.0e-9 * Time;
}

static void Cec_TranTargetProfAdd( Cec_TranProf_t * p, Cec_TranTargetProf_t * pTop,
    int * pnTop, int nTopMax, Cec_TranTargetProf_t * pTarget )
{
    int i, iMin = 0, nChecks = pTarget->nExistingChecks + pTarget->nConstructChecks;
    p->nTargets++;
    p->nTargetVictimSets       += pTarget->nVictimSets;
    p->nTargetExistingChecks   += pTarget->nExistingChecks;
    p->nTargetExistingMatched  += pTarget->nExistingMatched;
    p->nTargetExistingRetained += pTarget->nExistingRetained;
    p->nTargetConstructChecks  += pTarget->nConstructChecks;
    p->nTargetConstructMatched += pTarget->nConstructMatched;
    p->nTargetConstructRetained += pTarget->nConstructRetained;
    p->nTargetDuplicates       += pTarget->nDuplicates;
    p->nTargetGainCalls        += pTarget->nGainCalls;
    p->nTargetGainPositive     += pTarget->nGainPositive;
    p->nTargetGainRejected     += pTarget->nGainRejected;
    p->nTargetProofs           += pTarget->nProofs;
    p->nTargetRetainUnproved   += pTarget->nRetainUnproved;
    p->nTargetFinalUnproved    += pTarget->nFinalUnproved;
    p->nTargetAccepted         += pTarget->nAccepted;
    if ( p->nTargetMaxChecks < nChecks )
        p->nTargetMaxChecks = nChecks;
    if ( nTopMax == 0 )
        return;
    if ( *pnTop < nTopMax )
    {
        pTop[(*pnTop)++] = *pTarget;
        return;
    }
    for ( i = 1; i < *pnTop; i++ )
        if ( pTop[i].timeTotal < pTop[iMin].timeTotal )
            iMin = i;
    if ( pTop[iMin].timeTotal < pTarget->timeTotal )
        pTop[iMin] = *pTarget;
}

static int Cec_TranTargetProfCompare( const void * p0, const void * p1 )
{
    Cec_TranTargetProf_t const * pT0 = (Cec_TranTargetProf_t const *)p0;
    Cec_TranTargetProf_t const * pT1 = (Cec_TranTargetProf_t const *)p1;
    if ( pT0->timeTotal < pT1->timeTotal )
        return 1;
    if ( pT0->timeTotal > pT1->timeTotal )
        return -1;
    return 0;
}

static void Cec_TranPrintProfile( Cec_TranProf_t * p, Cec_TranTargetProf_t * pTop, int nTop )
{
    Cec_TranTargetProf_t * pT;
    int i;
    abctime Accounted = p->timeSim + p->timeCare + p->timeSpec +
        p->timeExisting + p->timeConstruct + p->timeGain +
        p->timeWindowMiter + p->timeWindowCorr +
        p->timeRetainMiter + p->timeRetainCorr +
        p->timeFinalMiter + p->timeFinalCorr + p->timeShadow + p->timeCexBmc;
    abctime Other = p->timeTotal > Accounted ? p->timeTotal - Accounted : 0;
    Abc_Print( 1, "Sequential transduction profile: total=%.3f sim=%.3f(%d) care=%.3f(%d) spec=%.3f(%d) existing=%.3f construct=%.3f gain=%.3f(%d) other=%.3f sec.\n",
        Cec_TranTimeSec(p->timeTotal), Cec_TranTimeSec(p->timeSim), p->nSimCalls,
        Cec_TranTimeSec(p->timeCare), p->nCareCalls,
        Cec_TranTimeSec(p->timeSpec), p->nSpecCalls,
        Cec_TranTimeSec(p->timeExisting), Cec_TranTimeSec(p->timeConstruct),
        Cec_TranTimeSec(p->timeGain), p->nGainCalls, Cec_TranTimeSec(Other) );
    Abc_Print( 1, "Sequential transduction proof profile: window=%d proved=%d expanded=%d miter=%.3f corr=%.3f retain=%d miter=%.3f corr=%.3f final=%d miter=%.3f corr=%.3f shadow=%d time=%.3f sec.\n",
        p->nWindowCalls, p->nWindowProved, p->nWindowExpanded,
        Cec_TranTimeSec(p->timeWindowMiter), Cec_TranTimeSec(p->timeWindowCorr),
        p->nRetainCalls, Cec_TranTimeSec(p->timeRetainMiter), Cec_TranTimeSec(p->timeRetainCorr),
        p->nFinalCalls, Cec_TranTimeSec(p->timeFinalMiter), Cec_TranTimeSec(p->timeFinalCorr),
        p->nShadowCalls, Cec_TranTimeSec(p->timeShadow) );
    Abc_Print( 1, "Sequential transduction CEGIS profile: stored-cex=%d restarts=%d bmc=%d sat=%d inconclusive=%d time=%.3f sec.\n",
        p->nCexStored, p->nCegisRestarts, p->nCexBmcCalls, p->nCexBmcSat,
        p->nCexBmcUnknown, Cec_TranTimeSec(p->timeCexBmc) );
    Abc_Print( 1, "Sequential transduction target aggregate: targets=%d victim-sets=%d existing=%d/%d/%d constructed=%d/%d/%d duplicates=%d gain=%d/%d/%d proofs=%d retain-unproved=%d final-unproved=%d accepted=%d avg-checks=%.1f max-checks=%d.\n",
        p->nTargets, p->nTargetVictimSets,
        p->nTargetExistingChecks, p->nTargetExistingMatched, p->nTargetExistingRetained,
        p->nTargetConstructChecks, p->nTargetConstructMatched, p->nTargetConstructRetained,
        p->nTargetDuplicates, p->nTargetGainCalls, p->nTargetGainPositive, p->nTargetGainRejected,
        p->nTargetProofs, p->nTargetRetainUnproved, p->nTargetFinalUnproved, p->nTargetAccepted,
        p->nTargets ? 1.0 * (p->nTargetExistingChecks + p->nTargetConstructChecks) / p->nTargets : 0.0,
        p->nTargetMaxChecks );
    if ( nTop > 1 )
        qsort( pTop, nTop, sizeof(Cec_TranTargetProf_t), Cec_TranTargetProfCompare );
    for ( i = 0; i < nTop; i++ )
    {
        abctime AccountedTarget, OtherTarget;
        pT = pTop + i;
        AccountedTarget = pT->timeCare + pT->timeSearch + pT->timeGain +
            pT->timeWindow + pT->timeCexBmc + pT->timeProof;
        OtherTarget = pT->timeTotal > AccountedTarget ? pT->timeTotal - AccountedTarget : 0;
        Abc_Print( 1, "Sequential transduction target profile: rank=%d round=%d obj=%d leaves=%d care-bits=%d victim-sets=%d existing=%d/%d/%d constructed=%d/%d/%d duplicates=%d gain=%d/%d/%d proofs=%d retain-unproved=%d final-unproved=%d accepted=%d window=%d/%d/%d cex-bmc=%d/%d total=%.3f care=%.3f search=%.3f gain-time=%.3f window-time=%.3f cex-time=%.3f proof=%.3f other=%.3f sec.\n",
            i + 1, pT->iRound, pT->iTarget, pT->nSuperLeaves, pT->nCareBits, pT->nVictimSets,
            pT->nExistingChecks, pT->nExistingMatched, pT->nExistingRetained,
            pT->nConstructChecks, pT->nConstructMatched, pT->nConstructRetained,
            pT->nDuplicates, pT->nGainCalls, pT->nGainPositive, pT->nGainRejected,
            pT->nProofs, pT->nRetainUnproved, pT->nFinalUnproved, pT->nAccepted,
            pT->nWindowCalls, pT->nWindowProved, pT->nWindowExpanded,
            pT->nCexBmcCalls, pT->nCexBmcSat,
            Cec_TranTimeSec(pT->timeTotal), Cec_TranTimeSec(pT->timeCare),
            Cec_TranTimeSec(pT->timeSearch), Cec_TranTimeSec(pT->timeGain),
            Cec_TranTimeSec(pT->timeWindow), Cec_TranTimeSec(pT->timeCexBmc),
            Cec_TranTimeSec(pT->timeProof), Cec_TranTimeSec(OtherTarget) );
    }
}

static void Cec_TranPrintDirectProfile( Cec_TranProf_t * p,
    int nStrictProofs, int nContextProofs,
    int nContextProofMax,
    int nConstantProofs, int nExistingProofs, int nConstructedProofs,
    int nConstantAccepted, int nExistingAccepted, int nConstructedAccepted )
{
    Cec_ProfCor_t * pC = &p->Corr;
    abctime Miter = p->timeWindowMiter + p->timeRetainMiter + p->timeFinalMiter;
    abctime Corr = p->timeWindowCorr + p->timeRetainCorr + p->timeFinalCorr;
    abctime Accounted = p->timeSim + p->timeCare + p->timeSpec +
        p->timeExisting + p->timeConstruct + p->timeGain + Miter + Corr +
        p->timeCombSolve + p->timeShadow + p->timeCexBmc;
    abctime Other = p->timeTotal > Accounted ? p->timeTotal - Accounted : 0;
    Abc_Print( 1, "Sequential direct phase profile: total=%.3f sim=%.3f snapshot-prep=%.3f prep-constant=%.3f care=%.3f existing-search=%.3f constructed-search=%.3f gain=%.3f miter=%.3f corr=%.3f cex=%.3f shadow=%.3f other=%.3f sec.\n",
        Cec_TranTimeSec(p->timeTotal), Cec_TranTimeSec(p->timeSim),
        Cec_TranTimeSec(p->timeSpec),
        Cec_TranTimeSec(p->timeSpec), Cec_TranTimeSec(p->timeCare),
        Cec_TranTimeSec(p->timeExisting), Cec_TranTimeSec(p->timeConstruct),
        Cec_TranTimeSec(p->timeGain), Cec_TranTimeSec(Miter),
        Cec_TranTimeSec(Corr), Cec_TranTimeSec(p->timeCexBmc),
        Cec_TranTimeSec(p->timeShadow), Cec_TranTimeSec(Other) );
    Abc_Print( 1, "Sequential direct outcome profile: unsat=%d time=%.3f avg-ms=%.3f sat=%d time=%.3f avg-ms=%.3f unknown=%d time=%.3f avg-ms=%.3f.\n",
        p->nProofUnsat, Cec_TranTimeSec(p->timeProofUnsat),
        p->nProofUnsat ? 1000.0 * Cec_TranTimeSec(p->timeProofUnsat) / p->nProofUnsat : 0.0,
        p->nProofSat, Cec_TranTimeSec(p->timeProofSat),
        p->nProofSat ? 1000.0 * Cec_TranTimeSec(p->timeProofSat) / p->nProofSat : 0.0,
        p->nProofUnknown, Cec_TranTimeSec(p->timeProofUnknown),
        p->nProofUnknown ? 1000.0 * Cec_TranTimeSec(p->timeProofUnknown) / p->nProofUnknown : 0.0 );
    Abc_Print( 1, "Sequential direct unknown profile: first=%d time=%.3f avg-ms=%.3f repeat-same-root-lane=%d time=%.3f avg-ms=%.3f exact-tried-skipped=%d.\n",
        p->nUnknownFirst, Cec_TranTimeSec(p->timeUnknownFirst),
        p->nUnknownFirst ? 1000.0 * Cec_TranTimeSec(p->timeUnknownFirst) / p->nUnknownFirst : 0.0,
        p->nUnknownRepeat, Cec_TranTimeSec(p->timeUnknownRepeat),
        p->nUnknownRepeat ? 1000.0 * Cec_TranTimeSec(p->timeUnknownRepeat) / p->nUnknownRepeat : 0.0,
        p->nQueueTriedSkipped );
    Abc_Print( 1, "Sequential direct scorr phase profile: calls=%d classes=%.3f init=%.3f bmc=%.3f [srm=%.3f sat=%.3f setup=%.3f solve=%.3f resim=%.3f] induction=%.3f [srm=%.3f sat=%.3f setup=%.3f solve=%.3f resim=%.3f] reduce=%.3f sec.\n",
        pC->nCalls, Cec_TranTimeHrSec(pC->timeClasses),
        Cec_TranTimeHrSec(pC->timeInit), Cec_TranTimeHrSec(pC->timeBmc),
        Cec_TranTimeHrSec(pC->timeBmcSrm), Cec_TranTimeHrSec(pC->timeBmcSat),
        Cec_TranTimeHrSec(pC->timeBmcSetup), Cec_TranTimeHrSec(pC->timeBmcSolve),
        Cec_TranTimeHrSec(pC->timeBmcSim), Cec_TranTimeHrSec(pC->timeInd),
        Cec_TranTimeHrSec(pC->timeIndSrm), Cec_TranTimeHrSec(pC->timeIndSat),
        Cec_TranTimeHrSec(pC->timeIndSetup), Cec_TranTimeHrSec(pC->timeIndSolve),
        Cec_TranTimeHrSec(pC->timeIndSim), Cec_TranTimeHrSec(pC->timeReduce) );
    Abc_Print( 1, "Sequential direct scorr obligation profile: bmc-rounds=%d unsat=%lld sat=%lld unknown=%lld induction-rounds=%d unsat=%lld sat=%lld unknown=%lld cex-real=%lld trivial=%lld fail=%lld conflicts=%lld total-cap-stops=%d.\n",
        pC->nBmcRounds, pC->nBmcUnsat, pC->nBmcSat, pC->nBmcUnknown,
        pC->nIndRounds, pC->nIndUnsat, pC->nIndSat, pC->nIndUnknown,
        pC->nCexReal, pC->nCexTrivial, pC->nCexFail,
        pC->nConfUsed, pC->nConfStops );
    Abc_Print( 1, "Sequential direct kind profile: constant=%d/%d and-gain=%lld reg-gain=%lld attempt=%.3f existing=%d/%d and-gain=%lld reg-gain=%lld attempt=%.3f constructed=%d/%d and-gain=%lld reg-gain=%lld attempt=%.3f sec.\n",
        nConstantAccepted, nConstantProofs,
        p->nDirectAndGain[0], p->nDirectRegGain[0], Cec_TranTimeSec(p->timeDirectKind[0]),
        nExistingAccepted, nExistingProofs,
        p->nDirectAndGain[1], p->nDirectRegGain[1], Cec_TranTimeSec(p->timeDirectKind[1]),
        nConstructedAccepted, nConstructedProofs,
        p->nDirectAndGain[2], p->nDirectRegGain[2], Cec_TranTimeSec(p->timeDirectKind[2]) );
    Abc_Print( 1, "Sequential direct lane profile: strict=%d attempt=%.3f context=%d attempt=%.3f sec.\n",
        nStrictProofs, Cec_TranTimeSec(p->timeDirectLane[1]),
        nContextProofs, Cec_TranTimeSec(p->timeDirectLane[0]) );
    Abc_Print( 1, "Sequential direct root-batch profile: snapshots=%d batches=%d calls=%d candidates=%d proved=%d max=%d initial=%d/%d/%d refill=%d/%d/%d screened=%d local-gain-evals=%d value-filtered=%d existing-large-skipped=%d existing-kept=%d committed-roots=%d and-gain=%lld reg-gain=%lld time=%.3f avg-candidates=%.1f avg-ms=%.3f rescue=%d/%d time=%.3f.\n",
        p->nRootSnapshots, p->nRootClosures, p->nRootBatchCalls,
        p->nRootBatchCands, p->nRootBatchProved,
        p->nRootBatchMax,
        p->nRootPhaseCalls[0], p->nRootPhaseCands[0], p->nRootPhaseProved[0],
        p->nRootPhaseCalls[1], p->nRootPhaseCands[1], p->nRootPhaseProved[1],
        p->nRootScreened, p->nRootGainEvals,
        p->nRootValueFiltered, p->nRootExistingSkipped,
        p->nRootExistingKept, p->nRootBundleCommits, p->nRootBundleAndGain,
        p->nRootBundleRegGain, Cec_TranTimeSec(p->timeRootBatch),
        p->nRootBatchCalls ? 1.0 * p->nRootBatchCands / p->nRootBatchCalls : 0.0,
        p->nRootBatchCalls ? 1000.0 * Cec_TranTimeSec(p->timeRootBatch) / p->nRootBatchCalls : 0.0,
        p->nRootRescueCalls, p->nRootRescueProved,
        Cec_TranTimeSec(p->timeRootRescue) );
    Abc_Print( 1, "Sequential direct two-stage proof profile: shared-build=%.6f; comb-candidates=%d proved=%d disproved=%d unknown=%d cubes=%d two-cube=%d three-cube=%d conflicts=%lld time=%.6f; scorr-candidates=%d proved=%d time=%.6f; selected=comb:%d/scorr:%d.\n",
        Cec_TranTimeSec(p->timeCombBuild),
        p->nCombCands, p->nCombProved, p->nCombDisproved, p->nCombUnknown,
        p->nCombCubeCalls, p->nCombTwoCubeCands, p->nCombThreeCubeCands,
        p->nCombConfUsed, Cec_TranTimeSec(p->timeCombSolve),
        p->nSeqCands, p->nSeqProved, Cec_TranTimeSec(p->timeSeqSolve),
        p->nCombSelected, p->nSeqSelected );
    Abc_Print( 1, "Sequential direct two-stage size profile: AND=%lld -> comb=%lld (gain=%lld) -> scorr=%lld (incremental-gain=%lld); Reg=%lld -> comb=%lld (gain=%lld) -> scorr=%lld (incremental-gain=%lld); size-eval=%.6f commit=%.6f sec.\n",
        p->nStageAndBefore, p->nStageAndAfterComb,
        p->nStageAndBefore - p->nStageAndAfterComb,
        p->nStageAndAfterSeq, p->nStageAndAfterComb - p->nStageAndAfterSeq,
        p->nStageRegBefore, p->nStageRegAfterComb,
        p->nStageRegBefore - p->nStageRegAfterComb,
        p->nStageRegAfterSeq, p->nStageRegAfterComb - p->nStageRegAfterSeq,
        Cec_TranTimeSec(p->timeRootStageEval),
        Cec_TranTimeSec(p->timeRootCommit) );
    Abc_Print( 1, "Sequential direct root budget profile: low=%d/%d/%d conflicts=%lld cap-stops=%d time=%.3f high=%d/%d/%d conflicts=%lld cap-stops=%d time=%.3f.\n",
        p->nRootBudgetCalls[0], p->nRootBudgetCands[0], p->nRootBudgetProved[0],
        p->nRootBudgetConfUsed[0], p->nRootBudgetConfStops[0],
        Cec_TranTimeSec(p->timeRootBudget[0]),
        p->nRootBudgetCalls[1], p->nRootBudgetCands[1], p->nRootBudgetProved[1],
        p->nRootBudgetConfUsed[1], p->nRootBudgetConfStops[1],
        Cec_TranTimeSec(p->timeRootBudget[1]) );
    Abc_Print( 1, "Sequential direct budget profile: low=%d/%d conflicts=%lld cap-stops=%d time=%.3f high-selected=%d high=%d/%d conflicts=%lld cap-stops=%d time=%.3f context-limit=%d context-used=%d value-roots-skipped=%d.\n",
        p->nScoutCalls, p->nScoutProved, p->nScoutConfUsed,
        p->nScoutConfStops, Cec_TranTimeSec(p->timeScout),
        p->nHardEligible, p->nHardRescueCalls, p->nHardRescueProved,
        p->nHardConfUsed, p->nHardConfStops,
        Cec_TranTimeSec(p->timeHardRescue), nContextProofMax,
        nContextProofs, p->nContextValueRootSkips );
}

// A signature is a collection of independent reset-reachable random traces.
// Every word carries 64 traces in parallel; consecutive frame groups carry
// the successive states of each trace.  These signatures only guide search:
// all accepted edits are still discharged by the sequential proof oracle.
typedef struct Cec_TranSim_t_ Cec_TranSim_t;
struct Cec_TranSim_t_
{
    Gia_Man_t *     pGia;
    int             nBaseWords;
    int             nWords;
    int             nFrames;
    int             nSlots;
    word *          pSims;          // [object ID][frame * nWords + word]
    word *          pState;         // current values of the ROs
};

// The pattern database owns concrete bounded counterexamples discovered while
// rejecting transactions.  It deliberately stores only PI/state traces, not
// object values: after a committed structural edit the next simulation batch
// evaluates the same traces on the new snapshot.  This makes the bank valid
// across transactions without retaining stale node IDs.
typedef struct Cec_TranPatDb_t_ Cec_TranPatDb_t;
struct Cec_TranPatDb_t_
{
    Vec_Ptr_t *      vCexes;
    Vec_Int_t *      vBatchEnds;    // sealed append-only CEX signature blocks
    int              nPis;
    int              nRegs;
    int              nMax;
};

static Cec_TranPatDb_t * Cec_TranPatDbStart( Gia_Man_t * p, int nMax )
{
    Cec_TranPatDb_t * pDb = ABC_CALLOC( Cec_TranPatDb_t, 1 );
    pDb->vCexes = Vec_PtrAlloc( nMax );
    pDb->vBatchEnds = Vec_IntAlloc( 8 );
    pDb->nPis = Gia_ManPiNum(p);
    pDb->nRegs = Gia_ManRegNum(p);
    pDb->nMax = nMax;
    return pDb;
}

static void Cec_TranPatDbStop( Cec_TranPatDb_t * pDb )
{
    Abc_Cex_t * pCex;
    int i;
    Vec_PtrForEachEntry( Abc_Cex_t *, pDb->vCexes, pCex, i )
        Abc_CexFree( pCex );
    Vec_PtrFree( pDb->vCexes );
    Vec_IntFree( pDb->vBatchEnds );
    ABC_FREE( pDb );
}

// Returns 1 only when a new trace was retained.  Product-machine and
// sequential-COI miters can have a different register count, but they retain
// the source PI order.  Their reset-reachable CEX is projected back to the
// source interface by preserving the PI sequence and restoring the source
// reset state.  This lets output-only product proofs refine Direct signatures
// without forcing the proof miter to retain unrelated registers.
static int Cec_TranPatDbAddCex( Cec_TranPatDb_t * pDb, Abc_Cex_t * pCex )
{
    Abc_Cex_t * pStore;
    if ( pDb->nMax == 0 || pCex == NULL || pCex->nPis != pDb->nPis ||
         Vec_PtrSize(pDb->vCexes) >= pDb->nMax )
        return 0;
    pStore = Abc_CexDup( pCex, pDb->nRegs );
    Vec_PtrPush( pDb->vCexes, pStore );
    return 1;
}

static int Cec_TranPatDbNumSealed( Cec_TranPatDb_t * pDb )
{
    return Vec_IntSize(pDb->vBatchEnds) ? Vec_IntEntryLast(pDb->vBatchEnds) : 0;
}

static int Cec_TranPatDbNumPending( Cec_TranPatDb_t * pDb )
{
    return Vec_PtrSize(pDb->vCexes) - Cec_TranPatDbNumSealed(pDb);
}

// Seal pending CEXes into immutable blocks of at most 64 traces.  A sealed
// block always gets its own simulation word and is never overwritten later;
// consequently every refresh only adds signature constraints.
static int Cec_TranPatDbSealPending( Cec_TranPatDb_t * pDb )
{
    int iEnd = Vec_PtrSize(pDb->vCexes);
    int iBeg = Cec_TranPatDbNumSealed(pDb);
    int nBlocks = 0;
    while ( iBeg < iEnd )
    {
        iBeg = Abc_MinInt( iBeg + 64, iEnd );
        Vec_IntPush( pDb->vBatchEnds, iBeg );
        nBlocks++;
    }
    return nBlocks;
}

static inline word Cec_TranSetLane( word Value, int iLane, int fValue )
{
    word Mask = ((word)1) << iLane;
    return fValue ? (Value | Mask) : (Value & ~Mask);
}

static void Cec_TranPatDbInjectInit( Cec_TranPatDb_t * pDb, Cec_TranSim_t * p )
{
    Abc_Cex_t * pCex;
    int b, c, r, w, iLane, iBeg = 0, iEnd;
    Vec_IntForEachEntry( pDb->vBatchEnds, iEnd, b )
    {
        w = p->nBaseWords + b;
        for ( c = iBeg; c < iEnd; c++ )
        {
            pCex = (Abc_Cex_t *)Vec_PtrEntry( pDb->vCexes, c );
            if ( pCex->nRegs != Gia_ManRegNum(p->pGia) )
                continue;
            iLane = c - iBeg;
            for ( r = 0; r < pCex->nRegs; r++ )
                p->pState[r * p->nWords + w] = Cec_TranSetLane(
                    p->pState[r * p->nWords + w], iLane,
                    Abc_InfoHasBit(pCex->pData, r) );
        }
        iBeg = iEnd;
    }
}

static word Cec_TranPatDbInjectPi( Cec_TranPatDb_t * pDb, int f, int iPi, int w, word Value )
{
    Abc_Cex_t * pCex;
    int b = w, c, iLane, iBeg, iEnd;
    if ( b < 0 || b >= Vec_IntSize(pDb->vBatchEnds) )
        return Value;
    iBeg = b ? Vec_IntEntry(pDb->vBatchEnds, b - 1) : 0;
    iEnd = Vec_IntEntry(pDb->vBatchEnds, b);
    for ( c = iBeg; c < iEnd; c++ )
    {
        pCex = (Abc_Cex_t *)Vec_PtrEntry( pDb->vCexes, c );
        if ( f > pCex->iFrame )
            continue;
        iLane = c - iBeg;
        Value = Cec_TranSetLane( Value, iLane,
            Abc_InfoHasBit(pCex->pData, pCex->nRegs + f * pCex->nPis + iPi) );
    }
    return Value;
}

static inline word * Cec_TranSimObj( Cec_TranSim_t * p, int iObj )
{
    return p->pSims + (size_t)iObj * p->nSlots;
}

static inline word Cec_TranSimLit( Cec_TranSim_t * p, int iLit, int iSlot )
{
    return Cec_TranSimObj(p, Abc_Lit2Var(iLit))[iSlot] ^
        (Abc_LitIsCompl(iLit) ? ~(word)0 : 0);
}

static int Cec_TranCountOnes( word * pData, int nWords )
{
    int i, Count = 0;
    for ( i = 0; i < nWords; i++ )
        Count += (int)__builtin_popcountll( pData[i] );
    return Count;
}

static Cec_TranSim_t * Cec_TranSimStart( Gia_Man_t * pGia, Cec_ParTran_t * pPars,
    Cec_TranPatDb_t * pDb )
{
    Cec_TranSim_t * p;
    Abc_Cex_t * pCex;
    Gia_Obj_t * pObj, * pObjRi, * pObjRo;
    int f, w, i, iSlot, iFan0, iFan1, nSealed;
    word v0, v1;
    p = ABC_CALLOC( Cec_TranSim_t, 1 );
    p->pGia = pGia;
    p->nBaseWords = pPars->nSimWords;
    p->nWords = p->nBaseWords + Vec_IntSize(pDb->vBatchEnds);
    p->nFrames = pPars->nSimFrames;
    // Never truncate a learned witness just because the random-signature
    // horizon was configured smaller than the CEX-recovery horizon.
    nSealed = Cec_TranPatDbNumSealed( pDb );
    for ( i = 0; i < nSealed; i++ )
    {
        pCex = (Abc_Cex_t *)Vec_PtrEntry( pDb->vCexes, i );
        p->nFrames = Abc_MaxInt( p->nFrames, pCex->iFrame + 1 );
    }
    p->nSlots = p->nWords * p->nFrames;
    p->pSims = ABC_CALLOC( word, (size_t)Gia_ManObjNum(pGia) * p->nSlots );
    p->pState = ABC_CALLOC( word, (size_t)Gia_ManRegNum(pGia) * p->nWords );
    Cec_TranPatDbInjectInit( pDb, p );
    Abc_RandomW( 1 );
    // Words are simulated outermost.  Appending a sealed CEX word therefore
    // cannot perturb the random stream or state trajectory of any older word.
    // This makes repeated Cec_TranSimStart() calls append-only in signature
    // space even though each call still performs a serial global simulation.
    for ( w = 0; w < p->nWords; w++ )
    {
        for ( f = 0; f < p->nFrames; f++ )
        {
            iSlot = f * p->nWords + w;
            Gia_ManForEachPi( pGia, pObj, i )
                Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot] =
                    w < p->nBaseWords ? Abc_RandomW(0) :
                    Cec_TranPatDbInjectPi( pDb, f, i, w - p->nBaseWords,
                        Abc_RandomW(0) );
            Gia_ManForEachRo( pGia, pObj, i )
                Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot] = p->pState[i * p->nWords + w];
            Gia_ManForEachAnd( pGia, pObj, i )
            {
                iFan0 = Gia_ObjFaninId0p( pGia, pObj );
                iFan1 = Gia_ObjFaninId1p( pGia, pObj );
                v0 = Cec_TranSimObj(p, iFan0)[iSlot] ^ (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0);
                v1 = Cec_TranSimObj(p, iFan1)[iSlot] ^ (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0);
                Cec_TranSimObj(p, i)[iSlot] = Gia_ObjIsXor(pObj) ? (v0 ^ v1) : (v0 & v1);
            }
            Gia_ManForEachCo( pGia, pObj, i )
                Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot] =
                    Cec_TranSimLit( p, Gia_ObjFaninLit0p(pGia, pObj), iSlot );
            Gia_ManForEachRiRo( pGia, pObjRi, pObjRo, i )
                p->pState[i * p->nWords + w] =
                    Cec_TranSimObj(p, Gia_ObjId(pGia, pObjRi))[iSlot];
        }
    }
    return p;
}

static void Cec_TranSimStop( Cec_TranSim_t * p )
{
    ABC_FREE( p->pSims );
    ABC_FREE( p->pState );
    ABC_FREE( p );
}

// Collect the positive-polarity AND supergate rooted at iTarget.  A
// complemented child is a literal rather than an AND factor because flattening
// through it would apply De Morgan's law.  XOR nodes are never supergate
// members.  The vector contains leaf literals, including their phases.
static void Cec_TranCollectSuper_rec( Gia_Man_t * p, int iLit, Vec_Int_t * vSuper )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, Abc_Lit2Var(iLit) );
    if ( Abc_LitIsCompl(iLit) || !Gia_ObjIsAnd(pObj) || Gia_ObjIsXor(pObj) )
    {
        Vec_IntPush( vSuper, iLit );
        return;
    }
    Cec_TranCollectSuper_rec( p, Gia_ObjFaninLit0p(p, pObj), vSuper );
    Cec_TranCollectSuper_rec( p, Gia_ObjFaninLit1p(p, pObj), vSuper );
}

static Vec_Int_t * Cec_TranCollectSuper( Gia_Man_t * p, int iTarget )
{
    Vec_Int_t * vSuper = Vec_IntAlloc( 8 );
    Cec_TranCollectSuper_rec( p, Abc_Var2Lit(iTarget, 0), vSuper );
    assert( Vec_IntSize(vSuper) >= 2 );
    return vSuper;
}

static inline word Cec_TranTempLit( word * pVals, int nWords, int iLit, int w )
{
    return pVals[(size_t)Abc_Lit2Var(iLit) * nWords + w] ^
        (Abc_LitIsCompl(iLit) ? ~(word)0 : 0);
}

// For each sampled trace/timepoint, flip the target exactly at that frame and
// resimulate the remaining suffix.  A changed PO proves observability.  A
// changed RI is conservatively treated as observable too: its future RO may
// affect a PO beyond the sampled suffix.  The result is a sampled sequential
// care mask C_i^seq, not a formal proof and never a commit criterion.
static word * Cec_TranSimComputeCare( Cec_TranSim_t * p, int iTarget )
{
    Gia_Man_t * pGia = p->pGia;
    Gia_Obj_t * pObj;
    word * pCare, * pVals, * pState, * pNext;
    int fStart, f, w, i, iSlot, iFan0, iFan1, iDriver;
    word v0, v1, v;
    pCare  = ABC_CALLOC( word, p->nSlots );
    pVals  = ABC_CALLOC( word, (size_t)Gia_ManObjNum(pGia) * p->nWords );
    pState = ABC_ALLOC( word, (size_t)Gia_ManRegNum(pGia) * p->nWords );
    pNext  = ABC_ALLOC( word, (size_t)Gia_ManRegNum(pGia) * p->nWords );
    for ( fStart = 0; fStart < p->nFrames; fStart++ )
    {
        Gia_ManForEachRo( pGia, pObj, i )
            for ( w = 0; w < p->nWords; w++ )
                pState[i * p->nWords + w] =
                    Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[fStart * p->nWords + w];
        for ( f = fStart; f < p->nFrames; f++ )
        {
            for ( w = 0; w < p->nWords; w++ )
            {
                iSlot = f * p->nWords + w;
                Gia_ManForEachPi( pGia, pObj, i )
                    pVals[(size_t)Gia_ObjId(pGia, pObj) * p->nWords + w] =
                        Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot];
                Gia_ManForEachRo( pGia, pObj, i )
                    pVals[(size_t)Gia_ObjId(pGia, pObj) * p->nWords + w] =
                        pState[i * p->nWords + w];
                Gia_ManForEachAnd( pGia, pObj, i )
                {
                    iFan0 = Gia_ObjFaninId0p( pGia, pObj );
                    iFan1 = Gia_ObjFaninId1p( pGia, pObj );
                    v0 = pVals[(size_t)iFan0 * p->nWords + w] ^ (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0);
                    v1 = pVals[(size_t)iFan1 * p->nWords + w] ^ (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0);
                    v = Gia_ObjIsXor(pObj) ? (v0 ^ v1) : (v0 & v1);
                    if ( i == iTarget && f == fStart )
                        v = ~Cec_TranSimObj(p, iTarget)[iSlot];
                    pVals[(size_t)i * p->nWords + w] = v;
                }
                Gia_ManForEachPo( pGia, pObj, i )
                {
                    iDriver = Gia_ObjFaninLit0p( pGia, pObj );
                    v = Cec_TranTempLit( pVals, p->nWords, iDriver, w );
                    pCare[fStart * p->nWords + w] |= v ^ Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot];
                }
                Gia_ManForEachRi( pGia, pObj, i )
                {
                    iDriver = Gia_ObjFaninLit0p( pGia, pObj );
                    v = Cec_TranTempLit( pVals, p->nWords, iDriver, w );
                    pVals[(size_t)Gia_ObjId(pGia, pObj) * p->nWords + w] = v;
                    pCare[fStart * p->nWords + w] |= v ^ Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot];
                    pNext[i * p->nWords + w] = v;
                }
            }
            for ( i = 0; i < Gia_ManRegNum(pGia) * p->nWords; i++ )
                pState[i] = pNext[i];
        }
    }
    ABC_FREE( pVals );
    ABC_FREE( pState );
    ABC_FREE( pNext );
    return pCare;
}

// This is the conservative first implementation of the specification from
// the design document.  It deliberately takes C_i=1, so it recognizes
// requirements at the target itself and never treats sampled ODC as proof.
// Phase C will replace this with exact sequential-TFO care masks.
typedef struct Cec_TranSpec_t_ Cec_TranSpec_t;
struct Cec_TranSpec_t_
{
    Cec_TranSim_t * pSim;
    word *          pMust1;
    word *          pMust0;
};

static Cec_TranSpec_t * Cec_TranSpecStart( Cec_TranSim_t * p, word * pCare,
    int iTarget, int iFanin0, int iFanin1 )
{
    Cec_TranSpec_t * pSpec = ABC_CALLOC( Cec_TranSpec_t, 1 );
    Vec_Int_t * vSuper = Cec_TranCollectSuper( p->pGia, iTarget );
    int s, i, iLeaf;
    word k, q;
    pSpec->pSim = p;
    pSpec->pMust1 = ABC_ALLOC( word, p->nSlots );
    pSpec->pMust0 = ABC_ALLOC( word, p->nSlots );
    for ( s = 0; s < p->nSlots; s++ )
    {
        k = Cec_TranSimLit( p, Vec_IntEntry(vSuper, iFanin0), s );
        if ( iFanin1 >= 0 )
            k &= Cec_TranSimLit( p, Vec_IntEntry(vSuper, iFanin1), s );
        q = ~(word)0;
        Vec_IntForEachEntry( vSuper, iLeaf, i )
            if ( i != iFanin0 && i != iFanin1 )
                q &= Cec_TranSimLit( p, iLeaf, s );
        pSpec->pMust1[s] = (pCare ? pCare[s] : ~(word)0) & k & q;
        pSpec->pMust0[s] = (pCare ? pCare[s] : ~(word)0) & ~k & q;
    }
    Vec_IntFree( vSuper );
    return pSpec;
}

static void Cec_TranSpecStop( Cec_TranSpec_t * p )
{
    ABC_FREE( p->pMust1 );
    ABC_FREE( p->pMust0 );
    ABC_FREE( p );
}

static int Cec_TranSpecMatches( Cec_TranSpec_t * p, int iDiv0, int iDiv1, int fDivCompl )
{
    int s;
    word h;
    for ( s = 0; s < p->pSim->nSlots; s++ )
    {
        h = Cec_TranSimLit( p->pSim, iDiv0, s );
        if ( iDiv1 != -1 )
            h &= Cec_TranSimLit( p->pSim, iDiv1, s );
        if ( fDivCompl )
            h = ~h;
        if ( (p->pMust1[s] & ~h) || (p->pMust0[s] & h) )
            return 0;
    }
    return 1;
}

static void Cec_TranSpecCompute( Cec_TranSpec_t * p, int iDiv0, int iDiv1,
    int fDivCompl, word * pSig )
{
    int s;
    for ( s = 0; s < p->pSim->nSlots; s++ )
    {
        pSig[s] = Cec_TranSimLit( p->pSim, iDiv0, s );
        if ( iDiv1 != -1 )
            pSig[s] &= Cec_TranSimLit( p->pSim, iDiv1, s );
        if ( fDivCompl )
            pSig[s] = ~pSig[s];
    }
}

// The check is exact over the current signature batch (not hash-based), so a
// duplicate cannot consume one of the expensive formal-proof slots.  Signature
// equality may merge different functions only on unsampled patterns, which
// can lose a search opportunity but can never compromise correctness.
static int Cec_TranSigIsNew( Vec_Wrd_t * vSigs, word * pSig, int nSlots )
{
    int i, k, nSigs = Vec_WrdSize(vSigs) / nSlots;
    for ( i = 0; i < nSigs; i++ )
    {
        for ( k = 0; k < nSlots; k++ )
            if ( Vec_WrdEntry(vSigs, i * nSlots + k) != pSig[k] )
                break;
        if ( k == nSlots )
            return 0;
    }
    for ( k = 0; k < nSlots; k++ )
        Vec_WrdPush( vSigs, pSig[k] );
    return 1;
}

// Convert an old-network literal into its literal in the network currently
// being duplicated.  All candidate divisors precede the target, so their
// copies are available when the target is rebuilt.
static inline int Cec_TranCopyLit( Gia_Man_t * p, int iLit )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, Abc_Lit2Var(iLit) );
    assert( ~pObj->Value );
    return Abc_LitNotCond( pObj->Value, Abc_LitIsCompl(iLit) );
}

// Build one explicit stage of an add-then-remove transaction.  In add mode,
// target = old_target & h.  In removal mode, target = other_fanin & h, which
// is the result of removing the selected victim fanin after h was added.
// div1 == -1 selects an existing literal; otherwise h = div0 & div1.
static Gia_Man_t * Cec_TranDupEdit( Gia_Man_t * p, int iTarget, int iFanin0, int iFanin1,
    int iDiv0, int iDiv1, int fDivCompl, int fAdd )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Int_t * vSuper = Cec_TranCollectSuper( p, iTarget );
    int i, k, iLit0, iLit1, iOld, iRep, iLeaf;
    assert( iFanin0 >= 0 && iFanin0 < Vec_IntSize(vSuper) );
    assert( iFanin1 == -1 || (iFanin1 > iFanin0 && iFanin1 < Vec_IntSize(vSuper)) );
    assert( fDivCompl == 0 || fDivCompl == 1 );
    assert( Abc_Lit2Var(iDiv0) < iTarget );
    assert( iDiv1 == -1 || Abc_Lit2Var(iDiv1) < iTarget );
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + 4 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Gia_ObjFanin0Copy( pObj );
        iLit1 = Gia_ObjFanin1Copy( pObj );
        if ( i == iTarget )
        {
            iRep = Cec_TranCopyLit( p, iDiv0 );
            if ( iDiv1 != -1 )
                iRep = Gia_ManHashAnd( pNew, iRep, Cec_TranCopyLit(p, iDiv1) );
            if ( fDivCompl )
                iRep = Abc_LitNot( iRep );
            if ( fAdd )
            {
                iOld = Gia_ManHashAnd( pNew, iLit0, iLit1 );
                pObj->Value = Gia_ManHashAnd( pNew, iOld, iRep );
            }
            else
            {
                Vec_IntForEachEntry( vSuper, iLeaf, k )
                    if ( k != iFanin0 && k != iFanin1 )
                        iRep = Gia_ManHashAnd( pNew, iRep, Cec_TranCopyLit(p, iLeaf) );
                pObj->Value = iRep;
            }
            continue;
        }
        pObj->Value = Gia_ManHashAnd( pNew, iLit0, iLit1 );
    }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Vec_IntFree( vSuper );
    return pNew;
}

// Cleanup is deliberately separated from the logical transaction.  Formal
// obligations are proved on the explicit add/remove structures; the cleaned
// copy is used only for exact cost and, after both proofs, for commit.
static void Cec_TranObjMapCompose( Vec_Int_t * vMap, Gia_Man_t * pFrom )
{
    Gia_Obj_t * pObj;
    int i, iLit, iMap;
    if ( vMap == NULL )
        return;
    Vec_IntForEachEntry( vMap, iLit, i )
    {
        if ( iLit < 0 || Abc_Lit2Var(iLit) >= Gia_ManObjNum(pFrom) )
        {
            Vec_IntWriteEntry( vMap, i, -1 );
            continue;
        }
        pObj = Gia_ManObj( pFrom, Abc_Lit2Var(iLit) );
        iMap = (int)pObj->Value;
        Vec_IntWriteEntry( vMap, i, iMap < 0 ? -1 :
            Abc_LitNotCond(iMap, Abc_LitIsCompl(iLit)) );
    }
}

static Vec_Int_t * Cec_TranObjMapCapture( Gia_Man_t * p )
{
    Vec_Int_t * vMap = Vec_IntAlloc( Gia_ManObjNum(p) );
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachObj( p, pObj, i )
        Vec_IntPush( vMap, (int)pObj->Value );
    return vMap;
}

static Gia_Man_t * Cec_TranCleanupMapped( Gia_Man_t * p, Vec_Int_t * vMap )
{
    Gia_Man_t * pNew, * pTemp;
    pTemp = Gia_ManDup( p );
    Cec_TranObjMapCompose( vMap, p );
    pNew = Gia_ManCleanup( pTemp );
    Cec_TranObjMapCompose( vMap, pTemp );
    Gia_ManStop( pTemp );
    pNew = Gia_ManDupNormalize( pTemp = pNew, 0 );
    Cec_TranObjMapCompose( vMap, pTemp );
    Gia_ManStop( pTemp );
    pNew = Gia_ManSeqCleanup( pTemp = pNew );
    Cec_TranObjMapCompose( vMap, pTemp );
    Gia_ManStop( pTemp );
    return pNew;
}

static Gia_Man_t * Cec_TranCleanup( Gia_Man_t * p )
{
    return Cec_TranCleanupMapped( p, NULL );
}

static int Cec_TranObjMapLit( Vec_Int_t * vMap, int iLit )
{
    int iMap;
    if ( iLit < 0 || Abc_Lit2Var(iLit) >= Vec_IntSize(vMap) )
        return -1;
    iMap = Vec_IntEntry( vMap, Abc_Lit2Var(iLit) );
    return iMap < 0 ? -1 : Abc_LitNotCond( iMap, Abc_LitIsCompl(iLit) );
}

static int Cec_TranGain( Gia_Man_t * p, Gia_Man_t * pCand )
{
    return Gia_ManAndNum(p) + Gia_ManRegNum(p)
         - Gia_ManAndNum(pCand) - Gia_ManRegNum(pCand);
}

static int Cec_TranAllPosAreZero( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachPo( p, pObj, i )
        if ( Gia_ObjFaninId0p(p, pObj) != 0 || Gia_ObjFaninC0(pObj) )
            return 0;
    return 1;
}

static inline int Cec_TranVecLit( Vec_Int_t * vLits, int iLit )
{
    int iCopy = Vec_IntEntry( vLits, Abc_Lit2Var(iLit) );
    assert( iCopy >= 0 );
    return Abc_LitNotCond( iCopy, Abc_LitIsCompl(iLit) );
}

static inline int Cec_TranHashGate( Gia_Man_t * pNew, Gia_Obj_t * pObj, int iLit0, int iLit1 )
{
    return Gia_ObjIsXor(pObj) ? Gia_ManHashXor(pNew, iLit0, iLit1) :
        Gia_ManHashAnd(pNew, iLit0, iLit1);
}

// Mark the complete combinational TFO of the edited target, including the
// PO/RI boundaries.  A marked RI is emitted as a difference PO by the local
// miter; its corresponding RO is then related inductively by the common
// source-state machine built below.
static char * Cec_TranMarkTfo( Gia_Man_t * p, int iTarget, int nDepth )
{
    Gia_Obj_t * pObj;
    Vec_Int_t * vQueue = Vec_IntAlloc( 100 );
    Vec_Int_t * vDepth = Vec_IntAlloc( 100 );
    char * pMark = ABC_CALLOC( char, Gia_ManObjNum(p) );
    int i, k, iFan;
    Gia_ManStaticFanoutStart( p );
    pMark[iTarget] = 1;
    Vec_IntPush( vQueue, iTarget );
    Vec_IntPush( vDepth, 0 );
    for ( i = 0; i < Vec_IntSize(vQueue); i++ )
    {
        int iObj = Vec_IntEntry( vQueue, i );
        int iDepth = Vec_IntEntry( vDepth, i );
        // A positive depth denotes the exact number of TFO gate levels
        // included after the target.  Nodes at the requested depth are the
        // cut boundary and must not pull one additional fanout level into
        // the window.
        if ( nDepth && iDepth >= nDepth )
            continue;
        for ( k = 0; k < Gia_ObjFanoutNumId(p, iObj); k++ )
        {
            iFan = Gia_ObjFanoutId( p, iObj, k );
            if ( pMark[iFan] )
                continue;
            pMark[iFan] = 1;
            pObj = Gia_ManObj( p, iFan );
            if ( !Gia_ObjIsCo(pObj) )
            {
                Vec_IntPush( vQueue, iFan );
                Vec_IntPush( vDepth, iDepth + 1 );
            }
        }
    }
    Gia_ManStaticFanoutStop( p );
    Vec_IntFree( vQueue );
    Vec_IntFree( vDepth );
    return pMark;
}

// Compute the sampled care used by the bounded-window proof.  Unlike output
// scope, the window obligation observes the exact TFO cut as well as every
// PO/RI reached before the cut.  Re-simulating the marked cone with the root
// flipped therefore makes a harvested window CEX a real new dependency
// constraint instead of relying only on the tried-recipe history to avoid
// proposing the same invalid function again.
static word * Cec_TranSimComputeWindowCare( Cec_TranSim_t * p,
    int iTarget, int nTfoDepth )
{
    Gia_Man_t * pGia = p->pGia;
    Gia_Obj_t * pObj;
    char * pMark = Cec_TranMarkTfo( pGia, iTarget, nTfoDepth );
    char * pCut = ABC_CALLOC( char, Gia_ManObjNum(pGia) );
    word * pCare = ABC_CALLOC( word, p->nSlots );
    word * pVals = ABC_ALLOC( word,
        (size_t)Gia_ManObjNum(pGia) * p->nWords );
    int f, w, i, k, iSlot, iFan0, iFan1, iDriver;
    word v0, v1, v;
    Gia_ManStaticFanoutStart( pGia );
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        if ( !pMark[i] )
            continue;
        for ( k = 0; k < Gia_ObjFanoutNumId(pGia, i); k++ )
            if ( !pMark[Gia_ObjFanoutId(pGia, i, k)] )
            {
                pCut[i] = 1;
                break;
            }
    }
    Gia_ManStaticFanoutStop( pGia );
    for ( f = 0; f < p->nFrames; f++ )
    {
        Gia_ManForEachCi( pGia, pObj, i )
            for ( w = 0; w < p->nWords; w++ )
                pVals[(size_t)Gia_ObjId(pGia, pObj) * p->nWords + w] =
                    Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[
                        f * p->nWords + w];
        Gia_ManForEachAnd( pGia, pObj, i )
        {
            for ( w = 0; w < p->nWords; w++ )
            {
                iSlot = f * p->nWords + w;
                if ( !pMark[i] )
                    v = Cec_TranSimObj(p, i)[iSlot];
                else if ( i == iTarget )
                    v = ~Cec_TranSimObj(p, i)[iSlot];
                else
                {
                    iFan0 = Gia_ObjFaninId0p( pGia, pObj );
                    iFan1 = Gia_ObjFaninId1p( pGia, pObj );
                    v0 = pVals[(size_t)iFan0 * p->nWords + w] ^
                        (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0);
                    v1 = pVals[(size_t)iFan1 * p->nWords + w] ^
                        (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0);
                    v = Gia_ObjIsXor(pObj) ? (v0 ^ v1) : (v0 & v1);
                }
                pVals[(size_t)i * p->nWords + w] = v;
                if ( pCut[i] )
                    pCare[iSlot] |= v ^ Cec_TranSimObj(p, i)[iSlot];
            }
        }
        Gia_ManForEachPo( pGia, pObj, i )
        {
            iDriver = Gia_ObjFaninLit0p( pGia, pObj );
            if ( !pMark[Abc_Lit2Var(iDriver)] )
                continue;
            for ( w = 0; w < p->nWords; w++ )
            {
                iSlot = f * p->nWords + w;
                pCare[iSlot] |= Cec_TranTempLit(pVals, p->nWords,
                    iDriver, w) ^ Cec_TranSimLit(p, iDriver, iSlot);
            }
        }
        Gia_ManForEachRi( pGia, pObj, i )
        {
            iDriver = Gia_ObjFaninLit0p( pGia, pObj );
            if ( !pMark[Abc_Lit2Var(iDriver)] )
                continue;
            for ( w = 0; w < p->nWords; w++ )
            {
                iSlot = f * p->nWords + w;
                pCare[iSlot] |= Cec_TranTempLit(pVals, p->nWords,
                    iDriver, w) ^ Cec_TranSimLit(p, iDriver, iSlot);
            }
        }
    }
    ABC_FREE( pMark );
    ABC_FREE( pCut );
    ABC_FREE( pVals );
    return pCare;
}

static word * Cec_TranSimComputeContextCare( Cec_TranSim_t * p,
    Cec_ParTran_t const * pPars, int iTarget )
{
    if ( pPars->nProofScope == CEC_TRAN_PROOF_WINDOW )
        return Cec_TranSimComputeWindowCare( p, iTarget,
            pPars->nProofWindow );
    return Cec_TranSimComputeCare( p, iTarget );
}

// Construct a single-state sequential difference machine.  It shares the
// original transition relation, duplicates only the target's combinational
// TFO for the edited variant, and emits differences at all affected PO/RI
// boundaries.  Equality of the affected RIs, together with unchanged
// unmarked RIs, inductively establishes a common state trajectory.  Thus this
// is an exact COI reduction for these pure combinational edits, not a bounded
// window approximation.
static Gia_Man_t * Cec_TranBuildLocalMiter( Gia_Man_t * p, int iTarget, int iFanin0, int iFanin1,
    int iDiv0, int iDiv1, int fDivCompl, int fRemove, int nTfoDepth )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vBase, * vEdit, * vSuper;
    char * pMark;
    int i, k, iLit0, iLit1, iOld, iRep, iEdit, iLeaf, nOuts = 0;
    assert( !Gia_ObjIsXor(Gia_ManObj(p, iTarget)) );
    vSuper = Cec_TranCollectSuper( p, iTarget );
    assert( iFanin0 >= 0 && iFanin0 < Vec_IntSize(vSuper) );
    assert( iFanin1 == -1 || (iFanin1 > iFanin0 && iFanin1 < Vec_IntSize(vSuper)) );
    pMark = Cec_TranMarkTfo( p, iTarget, nTfoDepth );
    vBase = Vec_IntStartFull( Gia_ManObjNum(p) );
    vEdit = Vec_IntStartFull( Gia_ManObjNum(p) );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + Gia_ManAndNum(p) / 4 + 100 );
    pNew->pName = Abc_UtilStrsav( "stran_local_miter" );
    Gia_ManHashAlloc( pNew );
    Vec_IntWriteEntry( vBase, 0, 0 );
    Vec_IntWriteEntry( vEdit, 0, 0 );
    Gia_ManForEachCi( p, pObj, i )
    {
        iEdit = Gia_ManAppendCi( pNew );
        Vec_IntWriteEntry( vBase, Gia_ObjId(p, pObj), iEdit );
        Vec_IntWriteEntry( vEdit, Gia_ObjId(p, pObj), iEdit );
    }
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Cec_TranVecLit( vBase, Gia_ObjFaninLit0p(p, pObj) );
        iLit1 = Cec_TranVecLit( vBase, Gia_ObjFaninLit1p(p, pObj) );
        iOld = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
        Vec_IntWriteEntry( vBase, i, iOld );
        if ( !pMark[i] )
        {
            Vec_IntWriteEntry( vEdit, i, iOld );
            continue;
        }
        if ( i == iTarget )
        {
            iRep = Cec_TranVecLit( vBase, iDiv0 );
            if ( iDiv1 != -1 )
                iRep = Gia_ManHashAnd( pNew, iRep, Cec_TranVecLit(vBase, iDiv1) );
            if ( fDivCompl )
                iRep = Abc_LitNot( iRep );
            if ( !fRemove )
                iEdit = Gia_ManHashAnd( pNew, iOld, iRep );
            else
            {
                Vec_IntForEachEntry( vSuper, iLeaf, k )
                    if ( k != iFanin0 && k != iFanin1 )
                        iRep = Gia_ManHashAnd( pNew, iRep, Cec_TranVecLit(vBase, iLeaf) );
                iEdit = iRep;
            }
        }
        else
        {
            iLit0 = Cec_TranVecLit( vEdit, Gia_ObjFaninLit0p(p, pObj) );
            iLit1 = Cec_TranVecLit( vEdit, Gia_ObjFaninLit1p(p, pObj) );
            iEdit = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
        }
        Vec_IntWriteEntry( vEdit, i, iEdit );
    }
    // For a bounded TFO, every marked AND with an unmarked fanout is a cut
    // boundary.  Proving equality at these boundaries is stronger than the
    // full-TFO query and therefore sound; a failing bounded proof merely
    // triggers expansion and never rejects the transaction.
    if ( nTfoDepth )
    {
        Gia_ManStaticFanoutStart( p );
        Gia_ManForEachAnd( p, pObj, i )
        {
            if ( !pMark[i] )
                continue;
            for ( k = 0; k < Gia_ObjFanoutNumId(p, i); k++ )
                if ( !pMark[Gia_ObjFanoutId(p, i, k)] )
                    break;
            if ( k == Gia_ObjFanoutNumId(p, i) )
                continue;
            Gia_ManAppendCo( pNew, Gia_ManHashXor(pNew,
                Cec_TranVecLit(vBase, Abc_Var2Lit(i, 0)),
                Cec_TranVecLit(vEdit, Abc_Var2Lit(i, 0))) );
            nOuts++;
        }
        Gia_ManStaticFanoutStop( p );
    }
    // PO and affected-RI difference outputs must precede all RIs in a Gia.
    Gia_ManForEachPo( p, pObj, i )
    {
        int iDriver = Gia_ObjFaninId0p( p, pObj );
        if ( !pMark[iDriver] )
            continue;
        Gia_ManAppendCo( pNew, Gia_ManHashXor(pNew,
            Cec_TranVecLit(vBase, Gia_ObjFaninLit0p(p, pObj)),
            Cec_TranVecLit(vEdit, Gia_ObjFaninLit0p(p, pObj))) );
        nOuts++;
    }
    Gia_ManForEachRi( p, pObj, i )
    {
        int iDriver = Gia_ObjFaninId0p( p, pObj );
        if ( !pMark[iDriver] )
            continue;
        Gia_ManAppendCo( pNew, Gia_ManHashXor(pNew,
            Cec_TranVecLit(vBase, Gia_ObjFaninLit0p(p, pObj)),
            Cec_TranVecLit(vEdit, Gia_ObjFaninLit0p(p, pObj))) );
        nOuts++;
    }
    assert( nOuts > 0 );
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManAppendCo( pNew, Cec_TranVecLit(vBase, Gia_ObjFaninLit0p(p, pObj)) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Vec_IntFree( vBase );
    Vec_IntFree( vEdit );
    Vec_IntFree( vSuper );
    ABC_FREE( pMark );
    // Normalization installs the object-copy/value metadata expected by the
    // scorr simulation manager and also removes any structurally-zero local
    // difference output.
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    pNew = Gia_ManDupNormalize( pTemp = pNew, 0 );
    Gia_ManStop( pTemp );
    return pNew;
}

// This is intentionally the same sequential proof engine used by &scorr:
// bounded reset-reachable BMC followed by its inductive correspondence
// refinement.  The difference is the query: &stran proves a proposed
// transduction transaction, rather than asking scorr to merge an equivalence
// class in the original network.
static int Cec_TranProveWhole( Gia_Man_t * p, Gia_Man_t * pCand,
    Cec_ParTran_t * pPars, Cec_TranProf_t * pProf )
{
    Cec_ParCor_t Cor;
    Gia_Man_t * pMiter, * pReduced;
    int fProved;
    pMiter = Gia_ManMiter( p, pCand, 0, 0, 1, 0, 0 );
    if ( pMiter == NULL )
        return 0;
    Cec_ManCorSetDefaultParams( &Cor );
    Cor.nFrames   = pPars->nFrames;
    Cor.nBTLimit  = pPars->nBTLimit;
    Cor.nConfTotal = pPars->nHardConfTotal;
    Cor.nStepsMax = pPars->nStepsMax;
    Cor.fVerbose  = 0;
    Cor.pProfile  = pPars->fProfile ? &pProf->Corr : NULL;
    pReduced = Cec_ManLSCorrespondence( pMiter, &Cor );
    // A total-budget stop leaves unrefined speculative classes in pReduced.
    // They must never be interpreted as a discharged transaction.
    fProved = !Cor.fConfStop && Cec_TranAllPosAreZero( pReduced );
    Gia_ManStop( pReduced );
    Gia_ManStop( pMiter );
    return fProved;
}

// Recover a concrete bounded counterexample only after the complete local
// proof has rejected a transaction.  The main &scorr oracle remains the
// acceptance proof; this BMC is solely a witness extractor for CEGIS.  A
// timeout/UNKNOWN cannot refine the pattern bank and is kept conservative.
static int Cec_TranHarvestCex( Gia_Man_t * pMiter, Cec_ParTran_t * pPars,
    Cec_TranPatDb_t * pDb, Cec_TranProf_t * pProf, int * piPo )
{
    Aig_Man_t * pAig;
    int RetValue, fAdded = 0;
    abctime clk;
    if ( piPo )
        *piPo = -1;
    if ( Gia_ManRegNum(pMiter) == 0 || pPars->nCexFrames == 0 || pDb->nMax == 0 ||
         Vec_PtrSize(pDb->vCexes) >= pDb->nMax )
        return 0;
    clk = Abc_Clock();
    pAig = Gia_ManToAigSimple( pMiter );
    RetValue = Saig_ManBmcSimple( pAig, pPars->nCexFrames, 0,
        pPars->nBTLimit, 0, 0, NULL, 0, 0 );
    pProf->timeCexBmc += Abc_Clock() - clk;
    pProf->nCexBmcCalls++;
    if ( RetValue == 0 && pAig->pSeqModel )
    {
        if ( piPo )
            *piPo = pAig->pSeqModel->iPo;
        fAdded = Cec_TranPatDbAddCex( pDb, pAig->pSeqModel );
        pProf->nCexBmcSat += fAdded;
    }
    else if ( RetValue == -1 )
        pProf->nCexBmcUnknown++;
    Aig_ManStop( pAig );
    return fAdded;
}

static int Cec_TranProveCombMiter( Gia_Man_t * pMiter,
    Cec_ParTran_t * pPars, int nBTLimit, int nConfTotal,
    int * pfConfStop, long long * pnConfUsed )
{
    Cec_ParSat_t ParsSat;
    Vec_Str_t * vStatus;
    Vec_Int_t * vCexStore;
    int i, fProved = 1;
    assert( Gia_ManRegNum(pMiter) == 0 );
    Cec_ManSatSetDefaultParams( &ParsSat );
    ParsSat.nBTLimit = nBTLimit;
    ParsSat.fVerbose = 0;
    Cec_ScorrConfLimit = nConfTotal;
    Cec_ScorrConfUsed  = 0;
    Cec_ScorrConfStop  = 0;
    vCexStore = Cec_ManSatSolveMiter( pMiter, &ParsSat, &vStatus );
    Cec_ScorrConfLimit = 0;
    for ( i = 0; i < Vec_StrSize(vStatus); i++ )
        if ( Vec_StrEntry(vStatus, i) != 1 )
        {
            fProved = 0;
            break;
        }
    fProved &= !Cec_ScorrConfStop;
    Vec_IntFree( vCexStore );
    Vec_StrFree( vStatus );
    if ( pfConfStop )
        *pfConfStop = Cec_ScorrConfStop;
    if ( pnConfUsed )
        *pnConfUsed = Cec_ScorrConfUsed;
    return fProved;
}

static int Cec_TranProveLocalMiter( Gia_Man_t * pMiter, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, int fRemove, int fWindow,
    int nBTLimit, int nConfTotal, int * pfConfStop, long long * pnConfUsed )
{
    Cec_ParCor_t Cor;
    Gia_Man_t * pReduced;
    int fProved;
    abctime clk = Abc_Clock();
    if ( Gia_ManRegNum(pMiter) == 0 )
    {
        fProved = Cec_TranProveCombMiter( pMiter, pPars, nBTLimit,
            nConfTotal, pfConfStop, pnConfUsed );
        pReduced = NULL;
    }
    else
    {
        Cec_ManCorSetDefaultParams( &Cor );
        Cor.nFrames   = pPars->nFrames;
        Cor.nBTLimit  = nBTLimit;
        Cor.nConfTotal = nConfTotal;
        Cor.nStepsMax = pPars->nStepsMax;
        Cor.fVerbose  = 0;
        Cor.pProfile  = pPars->fProfile ? &pProf->Corr : NULL;
        pReduced = Cec_ManLSCorrespondence( pMiter, &Cor );
        fProved = !Cor.fConfStop && Cec_TranAllPosAreZero( pReduced );
        if ( pfConfStop )
            *pfConfStop = Cor.fConfStop;
        if ( pnConfUsed )
            *pnConfUsed = Cor.nConfUsed;
    }
    if ( fWindow )
        pProf->timeWindowCorr += Abc_Clock() - clk;
    else if ( fRemove )
        pProf->timeFinalCorr += Abc_Clock() - clk;
    else
        pProf->timeRetainCorr += Abc_Clock() - clk;
    if ( pReduced )
        Gia_ManStop( pReduced );
    return fProved;
}

static int Cec_TranProveTransaction( Gia_Man_t * p, Gia_Man_t * pWhole0,
    Gia_Man_t * pWhole1, Cec_ParTran_t * pPars, int iTarget, int iFanin0, int iFanin1,
    int iDiv0, int iDiv1, int fDivCompl, int fRemove, Cec_TranPatDb_t * pDb,
    int * pfCexAdded, Cec_TranProf_t * pProf )
{
    Gia_Man_t * pMiter;
    int fProved;
    abctime clk = Abc_Clock();
    if ( pPars->nProofWindow )
    {
        pMiter = Cec_TranBuildLocalMiter( p, iTarget, iFanin0, iFanin1,
            iDiv0, iDiv1, fDivCompl, fRemove, pPars->nProofWindow );
        pProf->timeWindowMiter += Abc_Clock() - clk;
        pProf->nWindowCalls++;
        fProved = Cec_TranProveLocalMiter( pMiter, pPars, pProf, fRemove, 1,
            pPars->nBTLimit, pPars->nHardConfTotal, NULL, NULL );
        Gia_ManStop( pMiter );
        if ( fProved )
        {
            pProf->nWindowProved++;
            goto shadow;
        }
        pProf->nWindowExpanded++;
        clk = Abc_Clock();
    }
    pMiter = Cec_TranBuildLocalMiter( p, iTarget, iFanin0, iFanin1,
        iDiv0, iDiv1, fDivCompl, fRemove, 0 );
    if ( fRemove )
        pProf->timeFinalMiter += Abc_Clock() - clk, pProf->nFinalCalls++;
    else
        pProf->timeRetainMiter += Abc_Clock() - clk, pProf->nRetainCalls++;
    fProved = Cec_TranProveLocalMiter( pMiter, pPars, pProf, fRemove, 0,
        pPars->nBTLimit, pPars->nHardConfTotal, NULL, NULL );
    if ( !fProved )
        *pfCexAdded |= Cec_TranHarvestCex( pMiter, pPars, pDb, pProf, NULL );
    Gia_ManStop( pMiter );
shadow:
    if ( fProved && pPars->fShadow )
    {
        clk = Abc_Clock();
        fProved = Cec_TranProveWhole( pWhole0, pWhole1, pPars, pProf );
        pProf->timeShadow += Abc_Clock() - clk;
        pProf->nShadowCalls++;
    }
    return fProved;
}

// The candidate has already passed the exact structural-gain test.  This
// routine is the transactional boundary: no speculative wiring reaches p
// unless the sequential miter is discharged by scorr's proof infrastructure.
static int Cec_TranTryCommit( Gia_Man_t ** pp, Cec_ParTran_t * pPars,
    int iTarget, int iFanin0, int iFanin1, int iDiv0, int iDiv1, int fDivCompl, int * pnTried,
    int * pnPositive, int * pnGainRejected, int * pnRetainUnproved,
    int * pnFinalUnproved, int * pnAccepted, Cec_TranPatDb_t * pDb,
    int * pfCegisRestart, Cec_TranProf_t * pProf )
{
    Gia_Man_t * p = *pp, * pAdd, * pFinal, * pCand;
    int Gain, fRetain, fRemove, fCexAdded = 0;
    abctime clk = Abc_Clock();
    pAdd   = Cec_TranDupEdit( p, iTarget, iFanin0, iFanin1, iDiv0, iDiv1, fDivCompl, 1 );
    pFinal = Cec_TranDupEdit( p, iTarget, iFanin0, iFanin1, iDiv0, iDiv1, fDivCompl, 0 );
    pCand  = Cec_TranCleanup( pFinal );
    Gain = Cec_TranGain( p, pCand );
    pProf->timeGain += Abc_Clock() - clk;
    pProf->nGainCalls++;
    if ( Gain < pPars->nGainMin || Gia_ManRegNum(pCand) == 0 )
    {
        (*pnGainRejected)++;
        Gia_ManStop( pAdd );
        Gia_ManStop( pFinal );
        Gia_ManStop( pCand );
        return 0;
    }
    (*pnPositive)++;
    (*pnTried)++;
    if ( pPars->fVerbose )
    {
        if ( iDiv1 == -1 )
        {
            if ( iFanin1 < 0 )
                Abc_Print( 1, "  proof %d: n%d.f%d <- lit%d  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iDiv0, Gain );
            else
                Abc_Print( 1, "  proof %d: n%d.f%d+f%d <- lit%d  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iFanin1, iDiv0, Gain );
        }
        else if ( !fDivCompl )
        {
            if ( iFanin1 < 0 )
                Abc_Print( 1, "  proof %d: n%d.f%d <- (lit%d & lit%d)  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iDiv0, iDiv1, Gain );
            else
                Abc_Print( 1, "  proof %d: n%d.f%d+f%d <- (lit%d & lit%d)  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iFanin1, iDiv0, iDiv1, Gain );
        }
        else
        {
            if ( iFanin1 < 0 )
                Abc_Print( 1, "  proof %d: n%d.f%d <- !(lit%d & lit%d)  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iDiv0, iDiv1, Gain );
            else
                Abc_Print( 1, "  proof %d: n%d.f%d+f%d <- !(lit%d & lit%d)  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iFanin1, iDiv0, iDiv1, Gain );
        }
    }
    // Prove the explicit add stage, then prove the final removal network
    // against the same original source machine.  This second local query is
    // stronger than C_add == C_final; together with retention, transitivity
    // establishes the intended add-then-remove transaction.  When -f is on,
    // Cec_TranProveTransaction additionally shadows the direct whole miter.
    fRetain = Cec_TranProveTransaction(p, p, pAdd, pPars,
        iTarget, iFanin0, iFanin1, iDiv0, iDiv1, fDivCompl, 0, pDb, &fCexAdded, pProf);
    fRemove = fRetain && Cec_TranProveTransaction(p, pAdd, pFinal, pPars,
        iTarget, iFanin0, iFanin1, iDiv0, iDiv1, fDivCompl, 1, pDb, &fCexAdded, pProf);
    if ( !fRemove )
    {
        if ( !fRetain )
            (*pnRetainUnproved)++;
        else
            (*pnFinalUnproved)++;
        Gia_ManStop( pAdd );
        Gia_ManStop( pFinal );
        Gia_ManStop( pCand );
        if ( fCexAdded )
            *pfCegisRestart = 1;
        return 0;
    }
    if ( pPars->fVerbose )
    {
        if ( iFanin1 < 0 )
            Abc_Print( 1, "  accepted transaction: obj %d fanin %d, gain=%d.\n",
                iTarget, iFanin0, Gain );
        else
            Abc_Print( 1, "  accepted transaction: obj %d fanins %d+%d, gain=%d.\n",
                iTarget, iFanin0, iFanin1, Gain );
    }
    Gia_ManStop( p );
    Gia_ManStop( pAdd );
    Gia_ManStop( pFinal );
    *pp = pCand;
    (*pnAccepted)++;
    return 1;
}

enum
{
    CEC_TRAN_CAND_CONST = 0,
    CEC_TRAN_CAND_EXIST = 1,
    CEC_TRAN_CAND_CONSTR = 2
};

#define CEC_TRAN_RECIPE_NODES_MAX 20

// Recipe fanins use ordinary non-negative GIA literals for external signals.
// A negative value encodes a literal of an already-created recipe gate.  This
// keeps a candidate self-contained after the temporary divisor pool is freed
// and makes remapping across committed snapshots straightforward.
static inline int Cec_TranRecipeGateCode( int iGate, int fCompl )
{
    return -2 - Abc_Var2Lit( iGate, fCompl );
}
static inline int Cec_TranRecipeCodeIsGate( int Code )
{
    return Code < -1;
}
static inline int Cec_TranRecipeGateLit( int Code )
{
    assert( Cec_TranRecipeCodeIsGate(Code) );
    return -Code - 2;
}

typedef struct Cec_TranCand_t_ Cec_TranCand_t;
struct Cec_TranCand_t_
{
    int iTarget;
    int iDiv0;                  // display/compatibility: first external literal
    int iDiv1;                  // display/compatibility: second external literal
    int nMffc;
    int Gain;                   // local structural gain for scheduling
    int nGates;                 // dependency AIG nodes in Recipe[]
    int iOut;                   // external or recipe-gate literal code
    int Recipe[2 * CEC_TRAN_RECIPE_NODES_MAX];
    unsigned fDivOr    : 1;     // display/compatibility for one-gate recipes
    unsigned fStrict   : 1;
    unsigned nKind     : 2;
    unsigned nProofStage : 2;   // 0=unproved, 1=combinational, 2=sequential
};

static inline int Cec_TranRecipeCopyCode( Gia_Man_t * p, int Code,
    int const * pGates, int nBuilt )
{
    int iLit, iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return Cec_TranCopyLit( p, Code );
    iLit = Cec_TranRecipeGateLit( Code );
    iGate = Abc_Lit2Var( iLit );
    assert( iGate < nBuilt );
    return Abc_LitNotCond( pGates[iGate], Abc_LitIsCompl(iLit) );
}

static int Cec_TranRecipeBuild( Gia_Man_t * p, Gia_Man_t * pNew,
    Cec_TranCand_t const * pCand )
{
    int Gates[CEC_TRAN_RECIPE_NODES_MAX];
    int i, iLit0, iLit1;
    assert( pCand->nGates <= CEC_TRAN_RECIPE_NODES_MAX );
    for ( i = 0; i < pCand->nGates; i++ )
    {
        iLit0 = Cec_TranRecipeCopyCode( p, pCand->Recipe[2*i], Gates, i );
        iLit1 = Cec_TranRecipeCopyCode( p, pCand->Recipe[2*i+1], Gates, i );
        Gates[i] = Gia_ManHashAnd( pNew, iLit0, iLit1 );
    }
    return Cec_TranRecipeCopyCode( p, pCand->iOut, Gates, pCand->nGates );
}

static inline int Cec_TranRecipeVecCode( Gia_Man_t * pNew, Vec_Int_t * vBase,
    int Code, int const * pGates, int nBuilt )
{
    int iLit, iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return Cec_TranVecLit( vBase, Code );
    iLit = Cec_TranRecipeGateLit( Code );
    iGate = Abc_Lit2Var( iLit );
    assert( iGate < nBuilt );
    return Abc_LitNotCond( pGates[iGate], Abc_LitIsCompl(iLit) );
}

static int Cec_TranRecipeBuildVec( Gia_Man_t * pNew, Vec_Int_t * vBase,
    Cec_TranCand_t const * pCand )
{
    int Gates[CEC_TRAN_RECIPE_NODES_MAX];
    int i, iLit0, iLit1;
    for ( i = 0; i < pCand->nGates; i++ )
    {
        iLit0 = Cec_TranRecipeVecCode( pNew, vBase,
            pCand->Recipe[2*i], Gates, i );
        iLit1 = Cec_TranRecipeVecCode( pNew, vBase,
            pCand->Recipe[2*i+1], Gates, i );
        Gates[i] = Gia_ManHashAnd( pNew, iLit0, iLit1 );
    }
    return Cec_TranRecipeVecCode( pNew, vBase,
        pCand->iOut, Gates, pCand->nGates );
}

static inline word Cec_TranRecipeSimCode( Cec_TranSim_t * pSim, int Code,
    word const * pGates, int nBuilt, int iSlot )
{
    int iLit, iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return Cec_TranSimLit( pSim, Code, iSlot );
    iLit = Cec_TranRecipeGateLit( Code );
    iGate = Abc_Lit2Var( iLit );
    assert( iGate < nBuilt );
    return pGates[iGate] ^ (Abc_LitIsCompl(iLit) ? ~(word)0 : 0);
}

static int Cec_TranRecipeMatchesRoot( Cec_TranSim_t * pSim,
    Cec_TranCand_t const * pCand, word * pCare )
{
    word Gates[CEC_TRAN_RECIPE_NODES_MAX];
    word Value, v0, v1;
    int i, s;
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        for ( i = 0; i < pCand->nGates; i++ )
        {
            v0 = Cec_TranRecipeSimCode( pSim, pCand->Recipe[2*i], Gates, i, s );
            v1 = Cec_TranRecipeSimCode( pSim, pCand->Recipe[2*i+1], Gates, i, s );
            Gates[i] = v0 & v1;
        }
        Value = Cec_TranRecipeSimCode( pSim, pCand->iOut,
            Gates, pCand->nGates, s );
        if ( (Value ^ Cec_TranSimLit(pSim,
                Abc_Var2Lit(pCand->iTarget, 0), s)) &
             (pCare ? pCare[s] : ~(word)0) )
            return 0;
    }
    return 1;
}

// Direct resubstitution replaces the root itself, rather than one of the
// root's supergate leaves.  Root scope requires sampled equality everywhere;
// contextual scopes pass pCare and require it only where the sampled
// sequential TFO is observable.  Formal proof remains the sole commit
// criterion.
static int Cec_TranSigMatchesRoot( Cec_TranSim_t * pSim, int iTarget,
    int iDiv0, int iDiv1, int fDivOr, word * pCare )
{
    int s;
    word h;
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        h = Cec_TranSimLit( pSim, iDiv0, s );
        if ( iDiv1 != -1 )
            h = fDivOr ? h | Cec_TranSimLit(pSim, iDiv1, s) :
                         h & Cec_TranSimLit(pSim, iDiv1, s);
        if ( (h ^ Cec_TranSimLit(pSim, Abc_Var2Lit(iTarget, 0), s)) &
             (pCare ? pCare[s] : ~(word)0) )
            return 0;
    }
    return 1;
}

static Gia_Man_t * Cec_TranDupRoot( Gia_Man_t * p,
    Cec_TranCand_t const * pCand )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, iLit0, iLit1, iRep;
    assert( Gia_ObjIsAnd(Gia_ManObj(p, pCand->iTarget)) );
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + 4 );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Gia_ObjFanin0Copy( pObj );
        iLit1 = Gia_ObjFanin1Copy( pObj );
        if ( i == pCand->iTarget )
        {
            iRep = Cec_TranRecipeBuild( p, pNew, pCand );
            pObj->Value = iRep;
        }
        else
            pObj->Value = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
    }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

// Mark the unbounded sequential TFO of iTarget.  The traversal follows
// ordinary combinational fanout and crosses each affected RI to its
// corresponding RO.
static char * Cec_TranMarkSeqTfo( Gia_Man_t * p, int iTarget )
{
    Vec_Int_t * vQueue = Vec_IntAlloc( 128 );
    char * pMark = ABC_CALLOC( char, Gia_ManObjNum(p) );
    Gia_Obj_t * pObj;
    int iHead = 0, iObj, iFan, k;
    pMark[iTarget] = 1;
    Vec_IntPush( vQueue, iTarget );
    Gia_ManStaticFanoutStart( p );
    while ( iHead < Vec_IntSize(vQueue) )
    {
        iObj = Vec_IntEntry( vQueue, iHead++ );
        for ( k = 0; k < Gia_ObjFanoutNumId(p, iObj); k++ )
        {
            iFan = Gia_ObjFanoutId( p, iObj, k );
            if ( pMark[iFan] )
                continue;
            pMark[iFan] = 1;
            pObj = Gia_ManObj( p, iFan );
            if ( Gia_ObjIsRi(p, pObj) )
            {
                int iRo = Gia_ObjId( p, Gia_ObjRiToRo(p, pObj) );
                if ( !pMark[iRo] )
                {
                    pMark[iRo] = 1;
                    Vec_IntPush( vQueue, iRo );
                }
            }
            else if ( Gia_ObjIsAnd(pObj) )
            {
                Vec_IntPush( vQueue, iFan );
            }
            else
                assert( Gia_ObjIsPo(p, pObj) );
        }
    }
    Gia_ManStaticFanoutStop( p );
    Vec_IntFree( vQueue );
    return pMark;
}

// Collect the original POs in the unbounded sequential TFO of iTarget.  These
// are exactly the externally observable properties that can change after the
// Direct replacement; all other POs are structurally independent of the edit
// for every future frame.
static Vec_Int_t * Cec_TranCollectSeqTfoPos( Gia_Man_t * p, int iTarget )
{
    Vec_Int_t * vPos = Vec_IntAlloc( 16 );
    char * pMark = Cec_TranMarkSeqTfo( p, iTarget );
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachPo( p, pObj, i )
        if ( pMark[Gia_ObjId(p, pObj)] )
            Vec_IntPush( vPos, Gia_ObjCioId(pObj) );
    ABC_FREE( pMark );
    return vPos;
}

// Build the same two-state sequential product used by the ordinary &scorr
// equivalence flow: the source and edited machines have independent ROs and
// advance with their own RIs, while sharing primary inputs.  Only PO XORs in
// the edit's sequential TFO are retained.  Gia_ManDupCones then computes the
// exact sequential COI of these properties, so &scorr proves no unrelated
// pairs and RI equality is not imposed as an extra property.
static Gia_Man_t * Cec_TranBuildDirectOutputMiter( Gia_Man_t * p,
    Gia_Man_t * pFinal, int iTarget )
{
    Gia_Man_t * pFull, * pCoi, * pTemp;
    Vec_Int_t * vPos = Cec_TranCollectSeqTfoPos( p, iTarget );
    if ( Vec_IntSize(vPos) == 0 )
    {
        Vec_IntFree( vPos );
        return NULL;
    }
    pFull = Gia_ManMiter( p, pFinal, 0, 0, 1, 0, 0 );
    if ( pFull == NULL )
    {
        Vec_IntFree( vPos );
        return NULL;
    }
    pCoi = Gia_ManDupCones( pFull, Vec_IntArray(vPos), Vec_IntSize(vPos), 0 );
    pCoi = Gia_ManDupNormalize( pTemp = pCoi, 0 );
    Gia_ManStop( pTemp );
    ABC_FREE( pCoi->pName );
    pCoi->pName = Abc_UtilStrsav( "stran_direct_output_product_tfo" );
    Gia_ManStop( pFull );
    Vec_IntFree( vPos );
    return pCoi;
}

// Build a bounded-window Direct-replacement miter.  The edited copy is
// propagated only through the requested target TFO.  Equality is checked at
// the window cut and at every PO/RI reached before that cut.  An RI reached
// inside the window is a cut boundary, not a separate whole-machine
// RI-equality obligation.
static Gia_Man_t * Cec_TranBuildDirectContextMiter( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, int nTfoDepth )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vBase, * vEdit;
    char * pMark;
    int i, k, iLit0, iLit1, iOld, iRep, iEdit, nOuts = 0;
    assert( Gia_ObjIsAnd(Gia_ManObj(p, pCand->iTarget)) );
    pMark = Cec_TranMarkTfo( p, pCand->iTarget, nTfoDepth );
    vBase = Vec_IntStartFull( Gia_ManObjNum(p) );
    vEdit = Vec_IntStartFull( Gia_ManObjNum(p) );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + Gia_ManAndNum(p) / 4 + 100 );
    pNew->pName = Abc_UtilStrsav( nTfoDepth ?
        "stran_direct_window_miter" : "stran_direct_output_miter" );
    Gia_ManHashAlloc( pNew );
    Vec_IntWriteEntry( vBase, 0, 0 );
    Vec_IntWriteEntry( vEdit, 0, 0 );
    Gia_ManForEachCi( p, pObj, i )
    {
        iEdit = Gia_ManAppendCi( pNew );
        Vec_IntWriteEntry( vBase, Gia_ObjId(p, pObj), iEdit );
        Vec_IntWriteEntry( vEdit, Gia_ObjId(p, pObj), iEdit );
    }
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Cec_TranVecLit( vBase, Gia_ObjFaninLit0p(p, pObj) );
        iLit1 = Cec_TranVecLit( vBase, Gia_ObjFaninLit1p(p, pObj) );
        iOld = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
        Vec_IntWriteEntry( vBase, i, iOld );
        if ( !pMark[i] )
            iEdit = iOld;
        else if ( i == pCand->iTarget )
        {
            iRep = Cec_TranRecipeBuildVec( pNew, vBase, pCand );
            iEdit = iRep;
        }
        else
        {
            iLit0 = Cec_TranVecLit( vEdit, Gia_ObjFaninLit0p(p, pObj) );
            iLit1 = Cec_TranVecLit( vEdit, Gia_ObjFaninLit1p(p, pObj) );
            iEdit = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
        }
        Vec_IntWriteEntry( vEdit, i, iEdit );
    }
    if ( nTfoDepth )
    {
        Gia_ManStaticFanoutStart( p );
        Gia_ManForEachAnd( p, pObj, i )
        {
            if ( !pMark[i] )
                continue;
            for ( k = 0; k < Gia_ObjFanoutNumId(p, i); k++ )
                if ( !pMark[Gia_ObjFanoutId(p, i, k)] )
                    break;
            if ( k == Gia_ObjFanoutNumId(p, i) )
                continue;
            Gia_ManAppendCo( pNew, Gia_ManHashXor(pNew,
                Cec_TranVecLit(vBase, Abc_Var2Lit(i, 0)),
                Cec_TranVecLit(vEdit, Abc_Var2Lit(i, 0))) );
            nOuts++;
        }
        Gia_ManStaticFanoutStop( p );
    }
    Gia_ManForEachPo( p, pObj, i )
    {
        int iDriver = Gia_ObjFaninId0p( p, pObj );
        if ( !pMark[iDriver] )
            continue;
        Gia_ManAppendCo( pNew, Gia_ManHashXor(pNew,
            Cec_TranVecLit(vBase, Gia_ObjFaninLit0p(p, pObj)),
            Cec_TranVecLit(vEdit, Gia_ObjFaninLit0p(p, pObj))) );
        nOuts++;
    }
    Gia_ManForEachRi( p, pObj, i )
    {
        int iDriver = Gia_ObjFaninId0p( p, pObj );
        if ( !pMark[iDriver] )
            continue;
        Gia_ManAppendCo( pNew, Gia_ManHashXor(pNew,
            Cec_TranVecLit(vBase, Gia_ObjFaninLit0p(p, pObj)),
            Cec_TranVecLit(vEdit, Gia_ObjFaninLit0p(p, pObj))) );
        nOuts++;
    }
    // A dangling target has no observable boundary and is therefore safe to
    // remove; retain one explicit zero property so the proof engine still
    // receives a well-formed sequential miter.
    if ( nOuts == 0 )
        Gia_ManAppendCo( pNew, 0 );
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManAppendCo( pNew, Cec_TranVecLit(vBase, Gia_ObjFaninLit0p(p, pObj)) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Vec_IntFree( vBase );
    Vec_IntFree( vEdit );
    ABC_FREE( pMark );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    pNew = Gia_ManDupNormalize( pTemp = pNew, 0 );
    Gia_ManStop( pTemp );
    // The property outputs already stop at the requested window boundary.
    // Sequential cleanup removes all state/logic outside their exact COI.
    pNew = Gia_ManSeqCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

static int Cec_TranProveContext( Gia_Man_t * p, Gia_Man_t * pFinal,
    Cec_ParTran_t * pPars, int nProofScope, Cec_TranCand_t const * pCand,
    int nBTLimit, int nConfTotal, int fHarvest,
    Cec_TranPatDb_t * pDb, int * pfCexAdded, Cec_TranProf_t * pProf,
    int * pfConfStop, long long * pnConfUsed )
{
    Gia_Man_t * pMiter;
    int fProved;
    abctime clk = Abc_Clock();
    assert( nProofScope != CEC_TRAN_PROOF_ROOT );
    if ( nProofScope == CEC_TRAN_PROOF_WINDOW )
        pMiter = Cec_TranBuildDirectContextMiter( p, pCand,
            pPars->nProofWindow );
    else
        pMiter = Cec_TranBuildDirectOutputMiter( p, pFinal, pCand->iTarget );
    if ( nProofScope == CEC_TRAN_PROOF_WINDOW )
        pProf->timeWindowMiter += Abc_Clock() - clk, pProf->nWindowCalls++;
    else
        pProf->timeFinalMiter += Abc_Clock() - clk, pProf->nFinalCalls++;
    // No PO is reachable through the sequential TFO: the edit is externally
    // unobservable by construction and needs no formal property output.
    if ( pfConfStop )
        *pfConfStop = 0;
    if ( pnConfUsed )
        *pnConfUsed = 0;
    fProved = pMiter == NULL || Cec_TranProveLocalMiter( pMiter, pPars, pProf, 1,
        nProofScope == CEC_TRAN_PROOF_WINDOW, nBTLimit, nConfTotal,
        pfConfStop, pnConfUsed );
    if ( fProved && nProofScope == CEC_TRAN_PROOF_WINDOW )
        pProf->nWindowProved++;
    // A total-cap stop is already a deterministic UNKNOWN classification.
    // Do not spend another BMC budget trying to manufacture a CEX for it.
    if ( pMiter && !fProved && fHarvest &&
         (pfConfStop == NULL || !*pfConfStop) )
        *pfCexAdded |= Cec_TranHarvestCex( pMiter, pPars, pDb, pProf, NULL );
    if ( pMiter )
        Gia_ManStop( pMiter );
    if ( fProved && pPars->fShadow )
    {
        clk = Abc_Clock();
        fProved = Cec_TranProveWhole( p, pFinal, pPars, pProf );
        pProf->timeShadow += Abc_Clock() - clk;
        pProf->nShadowCalls++;
    }
    return fProved;
}

static int Cec_TranTryCommitContext( Gia_Man_t ** pp, Cec_ParTran_t * pPars,
    Cec_TranCand_t const * pCand, int * pnTried,
    int * pnPositive, int * pnGainRejected, int * pnUnproved, int * pnAccepted,
    Cec_TranPatDb_t * pDb, int * pfCexAdded, Cec_TranProf_t * pProf,
    Vec_Int_t ** pvObjMap, char ** ppAffected )
{
    Gia_Man_t * p = *pp, * pFinal, * pClean;
    Vec_Int_t * vObjMap;
    int Gain, fNewCex = 0, fProved, fConfStop = 0;
    long long nConfUsed = 0;
    abctime clk = Abc_Clock(), clkProof, clkTier, timeProof;
    *pfCexAdded = 0;
    *pvObjMap = NULL;
    *ppAffected = NULL;
    pFinal = Cec_TranDupRoot( p, pCand );
    // Cec_TranDupRoot leaves in each old object the literal of its copy in
    // pFinal.  Carry this map through cleanup so proof/cooldown history can be
    // retained for every surviving object after a successful transaction.
    vObjMap = Cec_TranObjMapCapture( p );
    pClean = Cec_TranCleanupMapped( pFinal, vObjMap );
    Gain = Cec_TranGain( p, pClean );
    pProf->timeGain += Abc_Clock() - clk;
    pProf->nGainCalls++;
    if ( Gain < pPars->nGainMin )
    {
        (*pnGainRejected)++;
        Gia_ManStop( pFinal );
        Gia_ManStop( pClean );
        Vec_IntFree( vObjMap );
        return 0;
    }
    (*pnPositive)++;
    (*pnTried)++;
    if ( pPars->fVerbose )
    {
        if ( pCand->nGates == 0 )
            Abc_Print( 1, "  direct proof %d: n%d <- lit%d  gain=%d\n",
                *pnTried, pCand->iTarget, pCand->iOut, Gain );
        else
            Abc_Print( 1, "  direct proof %d: n%d <- dependency[%d gates]  gain=%d\n",
                *pnTried, pCand->iTarget, pCand->nGates, Gain );
    }
    // Each contextual candidate receives exactly one deterministic proof call:
    // large-MFFC or large-exact-gain opportunities use C/Z, all others X/Y.
    // There is no scout-then-rescue retry.
    clkProof = pPars->fProfile ? Abc_Clock() : 0;
    assert( pPars->nProofScope != CEC_TRAN_PROOF_ROOT );
    {
        int fHigh = Gain >= pPars->nHardGain || pCand->nMffc >= pPars->nHardMffc;
        pProf->nHardEligible += fHigh;
        clkTier = pPars->fProfile ? Abc_Clock() : 0;
        if ( fHigh )
            pProf->nHardRescueCalls++;
        else
            pProf->nScoutCalls++;
        fProved = Cec_TranProveContext( p, pFinal, pPars, pPars->nProofScope,
            pCand,
            fHigh ? pPars->nBTLimit : pPars->nScoutBTLimit,
            fHigh ? pPars->nHardConfTotal : pPars->nScoutConfTotal,
            1, pDb,
            &fNewCex, pProf, &fConfStop, &nConfUsed );
        if ( fHigh )
        {
            if ( pPars->fProfile )
                pProf->timeHardRescue += Abc_Clock() - clkTier;
            pProf->nHardConfUsed += nConfUsed;
            pProf->nHardConfStops += fConfStop;
            if ( fProved )
                pProf->nHardRescueProved++;
        }
        else
        {
            if ( pPars->fProfile )
                pProf->timeScout += Abc_Clock() - clkTier;
            pProf->nScoutConfUsed += nConfUsed;
            pProf->nScoutConfStops += fConfStop;
            if ( fProved )
                pProf->nScoutProved++;
        }
    }
    if ( pPars->fProfile )
    {
        timeProof = Abc_Clock() - clkProof;
        if ( fProved )
            pProf->timeProofUnsat += timeProof;
        else if ( fNewCex )
            pProf->timeProofSat += timeProof;
        else
            pProf->timeProofUnknown += timeProof;
    }
    if ( !fProved )
    {
        (*pnUnproved)++;
        if ( fNewCex )
            pProf->nProofSat++;
        else
            pProf->nProofUnknown++;
        Gia_ManStop( pFinal );
        Gia_ManStop( pClean );
        Vec_IntFree( vObjMap );
        *pfCexAdded = fNewCex;
        return 0;
    }
    if ( pPars->fVerbose )
        Abc_Print( 1, "  accepted direct root substitution: obj %d, gain=%d.\n",
            pCand->iTarget, Gain );
    *ppAffected = Cec_TranMarkSeqTfo( p, pCand->iTarget );
    Gia_ManStop( p );
    Gia_ManStop( pFinal );
    *pp = pClean;
    *pvObjMap = vObjMap;
    (*pnAccepted)++;
    pProf->nProofUnsat++;
    return 1;
}

typedef struct Cec_TranRoot_t_ Cec_TranRoot_t;
struct Cec_TranRoot_t_
{
    int iObj;
    int nMffc;
};

typedef struct Cec_TranSigEnt_t_ Cec_TranSigEnt_t;
struct Cec_TranSigEnt_t_
{
    word Hash;
    int  iLit;
};

typedef struct Cec_TranCandVec_t_ Cec_TranCandVec_t;
struct Cec_TranCandVec_t_
{
    Cec_TranCand_t * pArray;
    int * pHash;                // open-addressed candidate index (entry + 1)
    int nSize;
    int nCap;
    int nHash;
    int iHead;
};

typedef struct Cec_TranDiscStat_t_ Cec_TranDiscStat_t;
struct Cec_TranDiscStat_t_
{
    long long nConstants;
    long long nExisting;
    long long nConstructed;
    long long nSigChecks;
    long long nSigRejected;
    long long nSigMatched;
    long long nRootMatches[2];    // strict/context signature matches by root
    int       nRootsProfiled[2];
    int       nRootMatchMax[2];
    int       nRootMatchHist[2][5]; // 0, 1, 2-4, 5-16, 17+
};

static void Cec_TranDiscFinishRoot( Cec_TranDiscStat_t * p, int fContext,
    int nMatches )
{
    int iBin = nMatches == 0 ? 0 : nMatches == 1 ? 1 :
        nMatches <= 4 ? 2 : nMatches <= 16 ? 3 : 4;
    p->nRootsProfiled[fContext]++;
    p->nRootMatches[fContext] += nMatches;
    p->nRootMatchMax[fContext] = Abc_MaxInt( p->nRootMatchMax[fContext], nMatches );
    p->nRootMatchHist[fContext][iBin]++;
}

static unsigned Cec_TranCandHash( Cec_TranCand_t const * pCand )
{
    unsigned Hash = 2166136261u;
    int i;
#define CEC_TRAN_CAND_HASH_ADD(Value) \
    Hash = (Hash ^ (unsigned)(Value)) * 16777619u
    CEC_TRAN_CAND_HASH_ADD( pCand->iTarget );
    CEC_TRAN_CAND_HASH_ADD( pCand->fStrict );
    CEC_TRAN_CAND_HASH_ADD( pCand->nGates );
    CEC_TRAN_CAND_HASH_ADD( pCand->iOut );
    for ( i = 0; i < 2 * pCand->nGates; i++ )
        CEC_TRAN_CAND_HASH_ADD( pCand->Recipe[i] );
#undef CEC_TRAN_CAND_HASH_ADD
    return Hash;
}

static void Cec_TranCandVecHashResize( Cec_TranCandVec_t * p, int nHashNew )
{
    int * pHashNew = ABC_CALLOC( int, nHashNew );
    int i, k;
    assert( nHashNew > 0 && !(nHashNew & (nHashNew - 1)) );
    for ( i = 0; i < p->nSize; i++ )
    {
        k = (int)(Cec_TranCandHash(p->pArray + i) & (unsigned)(nHashNew - 1));
        while ( pHashNew[k] )
            k = (k + 1) & (nHashNew - 1);
        pHashNew[k] = i + 1;
    }
    ABC_FREE( p->pHash );
    p->pHash = pHashNew;
    p->nHash = nHashNew;
}

static void Cec_TranCandVecPush( Cec_TranCandVec_t * p, Cec_TranCand_t Cand )
{
    int k;
    if ( p->nSize == p->nCap )
    {
        p->nCap = p->nCap ? 2 * p->nCap : 64;
        p->pArray = ABC_REALLOC( Cec_TranCand_t, p->pArray, p->nCap );
    }
    if ( p->nHash == 0 || 2 * (p->nSize + 1) >= p->nHash )
        Cec_TranCandVecHashResize( p, p->nHash ? 2 * p->nHash : 128 );
    p->pArray[p->nSize] = Cand;
    k = (int)(Cec_TranCandHash(&Cand) & (unsigned)(p->nHash - 1));
    while ( p->pHash[k] )
        k = (k + 1) & (p->nHash - 1);
    p->pHash[k] = ++p->nSize;
}

static void Cec_TranCandVecClear( Cec_TranCandVec_t * p )
{
    p->nSize = p->iHead = 0;
    if ( p->pHash )
        memset( p->pHash, 0, sizeof(int) * p->nHash );
}

static void Cec_TranCandVecStop( Cec_TranCandVec_t * p )
{
    ABC_FREE( p->pArray );
    ABC_FREE( p->pHash );
    memset( p, 0, sizeof(Cec_TranCandVec_t) );
}

static int Cec_TranCandEqual( Cec_TranCand_t const * p0, Cec_TranCand_t const * p1 )
{
    return p0->iTarget == p1->iTarget && p0->fStrict == p1->fStrict &&
        p0->nGates == p1->nGates && p0->iOut == p1->iOut &&
        !memcmp( p0->Recipe, p1->Recipe,
            sizeof(int) * 2 * p0->nGates );
}

static int Cec_TranCandVecContains( Cec_TranCandVec_t const * p, Cec_TranCand_t const * pCand )
{
    int k;
    if ( p->nHash == 0 )
        return 0;
    k = (int)(Cec_TranCandHash(pCand) & (unsigned)(p->nHash - 1));
    while ( p->pHash[k] )
    {
        if ( Cec_TranCandEqual(p->pArray + p->pHash[k] - 1, pCand) )
            return 1;
        k = (k + 1) & (p->nHash - 1);
    }
    return 0;
}

static int Cec_TranCandVecContainsRange( Cec_TranCandVec_t const * p,
    int iStart, Cec_TranCand_t const * pCand )
{
    int i;
    assert( iStart >= 0 && iStart <= p->nSize );
    for ( i = iStart; i < p->nSize; i++ )
        if ( Cec_TranCandEqual(p->pArray + i, pCand) )
            return 1;
    return 0;
}

static int Cec_TranCandVecRemap( Cec_TranCandVec_t * p,
    Vec_Int_t * vObjMap, char const * pAffected, Gia_Man_t * pNew )
{
    Cec_TranCandVec_t New = {0};
    Cec_TranCand_t Cand;
    int i, k, Code, iTargetLit, fDrop;
    for ( i = 0; i < p->nSize; i++ )
    {
        Cand = p->pArray[i];
        if ( pAffected[Cand.iTarget] )
            continue;
        fDrop = 0;
        for ( k = -1; k < 2 * Cand.nGates; k++ )
        {
            Code = k < 0 ? Cand.iOut : Cand.Recipe[k];
            if ( Cec_TranRecipeCodeIsGate(Code) )
                continue;
            if ( pAffected[Abc_Lit2Var(Code)] )
            {
                fDrop = 1;
                break;
            }
        }
        if ( fDrop )
            continue;
        iTargetLit = Cec_TranObjMapLit( vObjMap,
            Abc_Var2Lit(Cand.iTarget, 0) );
        if ( iTargetLit < 0 || Abc_LitIsCompl(iTargetLit) ||
             !Gia_ObjIsAnd(Gia_ManObj(pNew, Abc_Lit2Var(iTargetLit))) )
            continue;
        Cand.iTarget = Abc_Lit2Var( iTargetLit );
        for ( k = -1; k < 2 * Cand.nGates; k++ )
        {
            Code = k < 0 ? Cand.iOut : Cand.Recipe[k];
            if ( Cec_TranRecipeCodeIsGate(Code) )
                continue;
            Code = Cec_TranObjMapLit( vObjMap, Code );
            if ( Code < 0 )
            {
                fDrop = 1;
                break;
            }
            if ( k < 0 )
                Cand.iOut = Code;
            else
                Cand.Recipe[k] = Code;
        }
        if ( fDrop )
            continue;
        if ( Cand.iDiv0 >= 0 )
            Cand.iDiv0 = Cec_TranObjMapLit( vObjMap, Cand.iDiv0 );
        if ( Cand.iDiv1 >= 0 )
            Cand.iDiv1 = Cec_TranObjMapLit( vObjMap, Cand.iDiv1 );
        if ( !Cec_TranCandVecContains(&New, &Cand) )
            Cec_TranCandVecPush( &New, Cand );
    }
    ABC_FREE( p->pArray );
    ABC_FREE( p->pHash );
    *p = New;
    return New.nSize;
}

static int * Cec_TranRootHistoryRemap( int const * pOld,
    Vec_Int_t * vObjMap, char const * pAffected, Gia_Man_t * pNew,
    int * pnRetained )
{
    int * pNewHist = ABC_CALLOC( int, 2 * Gia_ManObjNum(pNew) );
    int i, k, iLit, iNew;
    for ( i = 0; i < Vec_IntSize(vObjMap); i++ )
    {
        if ( pAffected[i] )
            continue;
        iLit = Vec_IntEntry( vObjMap, i );
        if ( iLit < 0 )
            continue;
        iNew = Abc_Lit2Var( iLit );
        for ( k = 0; k < 2; k++ )
            if ( pNewHist[2*iNew+k] < pOld[2*i+k] )
                pNewHist[2*iNew+k] = pOld[2*i+k];
    }
    *pnRetained = 0;
    for ( i = 0; i < 2 * Gia_ManObjNum(pNew); i++ )
        *pnRetained += pNewHist[i] != 0;
    return pNewHist;
}

static Cec_TranCand_t Cec_TranCandCreate( int iTarget, int iDiv0, int iDiv1,
    int fDivOr, int nMffc, int nKind, int fStrict )
{
    Cec_TranCand_t Cand;
    memset( &Cand, 0, sizeof(Cand) );
    Cand.iTarget = iTarget;
    Cand.iDiv0 = iDiv0;
    Cand.iDiv1 = iDiv1;
    Cand.fDivOr = fDivOr;
    Cand.nMffc = nMffc;
    Cand.Gain = -1;
    Cand.nKind = nKind;
    Cand.fStrict = fStrict;
    if ( iDiv1 == -1 )
    {
        Cand.nGates = 0;
        Cand.iOut = iDiv0;
    }
    else
    {
        Cand.nGates = 1;
        Cand.Recipe[0] = Abc_LitNotCond( iDiv0, fDivOr );
        Cand.Recipe[1] = Abc_LitNotCond( iDiv1, fDivOr );
        Cand.iOut = Cec_TranRecipeGateCode( 0, fDivOr );
    }
    return Cand;
}

// The correspondence SRM can place constants, ROs, and internal ANDs into
// speculative classes, but a free PI cannot be a class node: unlike an RO it
// has no frame-to-frame definition for Gia_ManCorrSpecReal().  Preserve useful
// root=PI candidates by representing each PI literal with one unstrashed
// ordinary AND proxy (x&1=x) in this temporary proof network.  The query PO
// retains the proxy through cleanup, and sharing by PI phase avoids inflating a
// large batch with duplicate wrappers.
static int Cec_TranRootClassEndpoint( Gia_Man_t * pNew, int iLit,
    int nPis, int * pPiProxies )
{
    Gia_Obj_t * pObj = Gia_ManObj( pNew, Abc_Lit2Var(iLit) );
    int iIndex;
    if ( !Gia_ObjIsCi(pObj) || Gia_ObjCioId(pObj) >= nPis )
        return iLit;
    iIndex = 2 * Gia_ObjCioId(pObj) + Abc_LitIsCompl(iLit);
    if ( pPiProxies[iIndex] == -1 )
        pPiProxies[iIndex] = Gia_ManAppendAnd( pNew, iLit, 1 );
    return pPiProxies[iIndex];
}

// Build one signal-correspondence instance for a group of strict Direct
// candidates.  The source transition relation is copied only once.  Candidate
// endpoint pairs seed speculative equivalence classes.  Root-XOR-replacement
// POs are built only by the separate bounded reachable-CEX harvesting miter;
// correspondence status itself is read directly from the refined classes.
static Gia_Man_t * Cec_TranBuildRootBatch( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, int nCands,
    int fCreateQueries,
    Vec_Int_t ** pvPairs, Vec_Int_t ** pvQueries )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vPairs = Vec_IntAlloc( 2 * nCands );
    Vec_Int_t * vQueries = Vec_IntAlloc( nCands );
    int nPis = Gia_ManPiNum(p);
    int * pPiProxies = nPis ? ABC_FALLOC( int, 2 * nPis ) : NULL;
    int i, iLit0, iLit1, iRoot, iRep, iQuery;
    assert( nCands > 0 );
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + 4 * nCands + 16 );
    pNew->pName = Abc_UtilStrsav( "stran_direct_root_batch" );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Gia_ObjFanin0Copy( pObj );
        iLit1 = Gia_ObjFanin1Copy( pObj );
        pObj->Value = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
    }
    for ( i = 0; i < nCands; i++ )
    {
        iRoot = Cec_TranCopyLit( p, Abc_Var2Lit(pCands[i].iTarget, 0) );
        iRep = Cec_TranRecipeBuild( p, pNew, pCands + i );
        iRep = Cec_TranRootClassEndpoint( pNew, iRep, nPis, pPiProxies );
        Vec_IntPushTwo( vPairs, iRoot, iRep );
        if ( fCreateQueries )
        {
            iQuery = Gia_ManHashXor( pNew, iRoot, iRep );
            Vec_IntPush( vQueries, iQuery );
        }
    }
    Vec_IntForEachEntry( vQueries, iQuery, i )
        Gia_ManAppendCo( pNew, iQuery );
    // Endpoint COs only keep seeded class members alive through cleanup.  A
    // normal correspondence closure reads status from representatives and
    // needs no XOR property at all; the separate reachable-CEX miter requests
    // XOR queries and retains candidate endpoints through those queries.
    for ( i = 0; !fCreateQueries && i < Vec_IntSize(vPairs); i++ )
        Gia_ManAppendCo( pNew, Vec_IntEntry(vPairs, i) );
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    // Original POs are intentionally omitted, so remove their now-dangling
    // cones before Cec's reference-counted simulator is started.  Query POs
    // and every RI remain roots; remap the saved query literals through the
    // cleanup copy left in pTemp->Value.
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManDupRemapLiterals( vPairs, pTemp );
    Gia_ManDupRemapLiterals( vQueries, pTemp );
    Gia_ManStop( pTemp );
    ABC_FREE( pPiProxies );

    *pvPairs = vPairs;
    *pvQueries = vQueries;
    return pNew;
}

static int Cec_TranRootLitPhase( Gia_Man_t * p, int iLit )
{
    return Gia_ObjPhase(Gia_ManObj(p, Abc_Lit2Var(iLit))) ^
        Abc_LitIsCompl(iLit);
}

static int Cec_TranRootUfFind( int * pParent, int iObj )
{
    int iRoot = iObj;
    while ( pParent[iRoot] != iRoot )
        iRoot = pParent[iRoot];
    while ( pParent[iObj] != iObj )
    {
        int iNext = pParent[iObj];
        pParent[iObj] = iRoot;
        iObj = iNext;
    }
    return iRoot;
}

// Seed the transitive closure of candidate endpoint relations.  For example,
// a=b and a=c enter correspondence as one speculative class {a,b,c}; a CEX
// can split c without discarding a=b.  The smallest object ID is the class
// head, as required by Gia representatives.
static void Cec_TranSeedRootClasses( Gia_Man_t * p, Vec_Int_t * vPairs )
{
    int * pParent = ABC_ALLOC( int, Gia_ManObjNum(p) );
    int i, iLit0, iLit1, iObj0, iObj1, iRoot0, iRoot1;
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        pParent[i] = i;
    for ( i = 0; i < Vec_IntSize(vPairs); i += 2 )
    {
        iLit0 = Vec_IntEntry( vPairs, i );
        iLit1 = Vec_IntEntry( vPairs, i + 1 );
        if ( Cec_TranRootLitPhase(p, iLit0) !=
             Cec_TranRootLitPhase(p, iLit1) )
            continue;
        iObj0 = Abc_Lit2Var( iLit0 );
        iObj1 = Abc_Lit2Var( iLit1 );
        iRoot0 = Cec_TranRootUfFind( pParent, iObj0 );
        iRoot1 = Cec_TranRootUfFind( pParent, iObj1 );
        if ( iRoot0 == iRoot1 )
            continue;
        if ( iRoot0 < iRoot1 )
            pParent[iRoot1] = iRoot0;
        else
            pParent[iRoot0] = iRoot1;
    }
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
    {
        iRoot0 = Cec_TranRootUfFind( pParent, i );
        if ( iRoot0 != i )
            Gia_ObjSetRepr( p, i, iRoot0 );
    }
    ABC_FREE( pParent );
}

static int Cec_TranRootBatchPairProved( Gia_Man_t * p,
    int iLit0, int iLit1 )
{
    int iObj0 = Abc_Lit2Var( iLit0 );
    int iObj1 = Abc_Lit2Var( iLit1 );
    int iHead0, iHead1;
    if ( Cec_TranRootLitPhase(p, iLit0) != Cec_TranRootLitPhase(p, iLit1) )
        return 0;
    iHead0 = Gia_ObjRepr(p, iObj0) == GIA_VOID ?
        iObj0 : Gia_ObjRepr(p, iObj0);
    iHead1 = Gia_ObjRepr(p, iObj1) == GIA_VOID ?
        iObj1 : Gia_ObjRepr(p, iObj1);
    return iHead0 == iHead1;
}

// Solve one counterexample cube directly on the shared candidate graph.  CBS
// returns 1 for UNSAT, 0 for SAT, and -1 for UNKNOWN.
static int Cec_TranCombSolveCube( Cbs_Man_t * pCbs, int const * pLits,
    int nLits, Cec_TranProf_t * pProf )
{
    int Status = Cbs_ManSolveLits( pCbs, pLits, nLits );
    pProf->nCombCubeCalls++;
    pProf->nCombConfUsed += Cbs_ManReadConflicts( pCbs );
    return Status;
}

// Candidate-directed combinational equivalence.  Registers are treated as
// independent CIs, so every UNSAT result is valid in all states.  A generic
// a=h relation is two implication counterexample cubes.  If h is one
// AND/NAND node, split it into three still smaller cubes; the first SAT cube
// terminates the candidate immediately.
static Vec_Str_t * Cec_TranProveCombBatch( Gia_Man_t * pBatch,
    Cec_TranCand_t const * pCands, int nCands, Vec_Int_t * vPairs,
    Cec_ParTran_t * pPars, Cec_TranProf_t * pProf )
{
    Cbs_Man_t * pCbs = Cbs_ManAlloc( pBatch );
    Vec_Str_t * vStage = Vec_StrStart( nCands );
    Gia_Obj_t * pRep;
    int i, k, a, h, x, y, t, Status, fSat, fUnknown, Cubes[3][3], Sizes[3];
    abctime clk = Abc_Clock();
    Cbs_ManSetConflictNum( pCbs, pPars->nBTLimit );
    pProf->nCombCands += nCands;
    for ( i = 0; i < nCands; i++ )
    {
        a = Vec_IntEntry( vPairs, 2*i );
        h = Vec_IntEntry( vPairs, 2*i + 1 );
        if ( a == h )
        {
            Vec_StrWriteEntry( vStage, i, 1 );
            pProf->nCombProved++;
            continue;
        }
        fSat = fUnknown = 0;
        pRep = Gia_ManObj( pBatch, Abc_Lit2Var(h) );
        if ( pCands[i].nGates == 1 && Gia_ObjIsAnd(pRep) )
        {
            // t is the root polarity which must be true in the first two
            // counterexample cases.  h complemented means NAND.
            x = Gia_ObjFaninLit0p( pBatch, pRep );
            y = Gia_ObjFaninLit1p( pBatch, pRep );
            t = Abc_LitNotCond( a, Abc_LitIsCompl(h) );
            Cubes[0][0] = t;                 Cubes[0][1] = Abc_LitNot(x);
            Cubes[1][0] = t;                 Cubes[1][1] = Abc_LitNot(y);
            Cubes[2][0] = Abc_LitNot(t);     Cubes[2][1] = x; Cubes[2][2] = y;
            Sizes[0] = Sizes[1] = 2; Sizes[2] = 3;
            pProf->nCombThreeCubeCands++;
            for ( k = 0; k < 3; k++ )
            {
                Status = Cec_TranCombSolveCube( pCbs, Cubes[k], Sizes[k], pProf );
                if ( Status == 0 ) { fSat = 1; break; }
                fUnknown |= Status < 0;
            }
        }
        else
        {
            Cubes[0][0] = a;             Cubes[0][1] = Abc_LitNot(h);
            Cubes[1][0] = Abc_LitNot(a); Cubes[1][1] = h;
            pProf->nCombTwoCubeCands++;
            for ( k = 0; k < 2; k++ )
            {
                Status = Cec_TranCombSolveCube( pCbs, Cubes[k], 2, pProf );
                if ( Status == 0 ) { fSat = 1; break; }
                fUnknown |= Status < 0;
            }
        }
        if ( fSat )
            pProf->nCombDisproved++;
        else if ( fUnknown )
            pProf->nCombUnknown++;
        else
        {
            Vec_StrWriteEntry( vStage, i, 1 );
            pProf->nCombProved++;
        }
    }
    pProf->timeCombSolve += Abc_Clock() - clk;
    Cbs_ManStop( pCbs );
    return vStage;
}

// Return one status bit per candidate.  Seed candidate endpoints as ordinary
// equivalence classes and run one shared correspondence closure over exactly
// these relations.  This retains &scorr's standard BMC, SRM, CEX resimulation,
// class refinement, and induction fixed point without unrelated class search.
static Vec_Int_t * Cec_TranProveRootBatch( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, int nCands, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, Vec_Str_t ** pvStage )
{
    Cec_ParCor_t Cor;
    Gia_Man_t * pBatch;
    Gia_Obj_t * pObj;
    Vec_Int_t * vPairs, * vQueries;
    Vec_Int_t * vStatus = Vec_IntStart( nCands );
    Vec_Str_t * vStage;
    int i, RetValue = 1, nProved = 0, nSeq = 0, nSeqProved = 0;
    abctime clk, timeSeq = 0, clkBatch = Abc_Clock();
    memset( &Cor, 0, sizeof(Cor) );
    clk = Abc_Clock();
    pBatch = Cec_TranBuildRootBatch( p, pCands, nCands, 0,
        &vPairs, &vQueries );
    clk = Abc_Clock() - clk;
    pProf->timeFinalMiter += clk;
    pProf->timeCombBuild += clk;
    pProf->nFinalCalls++;
    vStage = Cec_TranProveCombBatch( pBatch, pCands, nCands, vPairs,
        pPars, pProf );
    for ( i = 0; i < nCands; i++ )
        if ( Vec_StrEntry(vStage, i) == 0 )
            nSeq++;
    pProf->nSeqCands += nSeq;
    if ( nSeq )
    {
        Gia_ManSetPhase( pBatch );
        pBatch->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(pBatch) );
        Gia_ManForEachObj( pBatch, pObj, i )
            Gia_ObjSetRepr( pBatch, i, GIA_VOID );
        Gia_ManCreateValueRefs( pBatch );
        // Keep universally proved combinational relations in the same class
        // hypothesis.  They are already discharged, but connecting them to
        // the unresolved relations can strengthen the shared scorr closure.
        Cec_TranSeedRootClasses( pBatch, vPairs );
        pBatch->pNexts = Gia_ManDeriveNexts( pBatch );
        Cec_ManCorSetDefaultParams( &Cor );
        Cor.nFrames   = pPars->nFrames;
        Cor.nBTLimit  = pPars->nBTLimit;
        Cor.nConfTotal = 0;
        Cor.nStepsMax = pPars->nStepsMax;
        Cor.fVerbose  = 0;
        Cor.pProfile  = pPars->fProfile ? &pProf->Corr : NULL;
        clk = Abc_Clock();
        RetValue = Cec_ManLSCorrespondenceClasses( pBatch, &Cor );
        timeSeq = Abc_Clock() - clk;
        pProf->timeFinalCorr += timeSeq;
        pProf->timeSeqSolve += timeSeq;
    }
    for ( i = 0; i < nCands; i++ )
    {
        int fProved = Vec_StrEntry(vStage, i) == 1;
        if ( !fProved && nSeq )
            fProved = RetValue && !Cor.fConfStop &&
                Cec_TranRootBatchPairProved( pBatch,
                    Vec_IntEntry(vPairs, 2*i), Vec_IntEntry(vPairs, 2*i+1) );
        if ( fProved && Vec_StrEntry(vStage, i) == 0 )
        {
            Vec_StrWriteEntry( vStage, i, 2 );
            pProf->nSeqProved++;
            nSeqProved++;
        }
        Vec_IntWriteEntry( vStatus, i, fProved );
        nProved += fProved;
    }
    pProf->timeRootBatch += Abc_Clock() - clkBatch;
    pProf->nRootBatchCalls++;
    pProf->nRootBatchCands += nCands;
    pProf->nRootBatchProved += nProved;
    if ( nSeq )
    {
        pProf->timeRootBudget[1] += timeSeq;
        pProf->nRootBudgetCalls[1]++;
        pProf->nRootBudgetCands[1] += nSeq;
        pProf->nRootBudgetProved[1] += nSeqProved;
        pProf->nRootBudgetConfUsed[1] += Cor.nConfUsed;
        pProf->nRootBudgetConfStops[1] += Cor.fConfStop;
    }
    Vec_IntFree( vPairs );
    Vec_IntFree( vQueries );
    Gia_ManStop( pBatch );
    *pvStage = vStage;
    return vStatus;
}

// A correspondence counterexample produced during induction is a local SRM
// assignment and need not be reachable from reset.  Between construct waves,
// therefore, ask one bounded reset-reachable question over all failed
// constructed recipes.  One real trace is enough to rebuild every signature
// and dependency problem in the next wave.
static int Cec_TranHarvestRootWaveCex( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, Vec_Int_t * vStatus, int nCands,
    char const * pSolved, Cec_ParTran_t * pPars,
    Cec_TranPatDb_t * pDb, Cec_TranProf_t * pProf, int * piCand )
{
    Cec_TranCandVec_t Retry = {0};
    Gia_Man_t * pMiter;
    Vec_Int_t * vPairs, * vQueries, * vOrig = Vec_IntAlloc( nCands );
    int i, iPo = -1, fAdded;
    *piCand = -1;
    for ( i = 0; i < nCands; i++ )
        if ( !Vec_IntEntry(vStatus, i) &&
             pCands[i].nKind == CEC_TRAN_CAND_CONSTR &&
             !pSolved[pCands[i].iTarget] )
        {
            Cec_TranCandVecPush( &Retry, pCands[i] );
            Vec_IntPush( vOrig, i );
        }
    if ( Retry.nSize == 0 )
    {
        Vec_IntFree( vOrig );
        Cec_TranCandVecStop( &Retry );
        return 0;
    }
    pMiter = Cec_TranBuildRootBatch( p, Retry.pArray, Retry.nSize,
        1,
        &vPairs, &vQueries );
    fAdded = Cec_TranHarvestCex( pMiter, pPars, pDb, pProf, &iPo );
    if ( iPo >= 0 && iPo < Vec_IntSize(vOrig) )
        *piCand = Vec_IntEntry( vOrig, iPo );
    Vec_IntFree( vPairs );
    Vec_IntFree( vQueries );
    Vec_IntFree( vOrig );
    Gia_ManStop( pMiter );
    Cec_TranCandVecStop( &Retry );
    return fAdded;
}

static int Cec_TranRootCandidateGainEval( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, Cec_TranProf_t * pProf )
{
    Gia_Obj_t * pRoot = Gia_ManObj( p, pCand->iTarget );
    int Used[2 * CEC_TRAN_RECIPE_NODES_MAX + 1];
    int Gain, i, k, Code, iObj, nUsed = 0, fSeen;
    abctime clk = Abc_Clock();

    // Root scheduling needs the local structural gain, not a rebuilt copy of
    // the complete sequential network.  Temporarily add the replacement's
    // fanin references, dereference the target MFFC, and restore the original
    // reference counts.  This is O(affected MFFC), changes no graph objects,
    // and correctly keeps a divisor that lies inside the removed cone alive.
    // A constructed AND/OR costs at most one new AIG node; structural hashing
    // can only improve the final gain.  The one real bundle commit below still
    // performs cleanup and checks the exact combined AND+register gain.
    assert( p->pRefs != NULL );
    assert( Gia_ObjIsAnd(pRoot) );
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) )
            continue;
        iObj = Abc_Lit2Var( Code );
        if ( iObj == 0 || !Gia_ObjIsAnd(Gia_ManObj(p, iObj)) )
            continue;
        fSeen = 0;
        for ( k = 0; k < nUsed; k++ )
            fSeen |= Used[k] == iObj;
        if ( fSeen )
            continue;
        Used[nUsed++] = iObj;
        Gia_ObjRefIncId( p, iObj );
    }
    Gain = Gia_NodeMffcSize( p, pRoot );
    for ( i = 0; i < nUsed; i++ )
        Gia_ObjRefDecId( p, Used[i] );
    Gain -= pCand->nGates;
    pProf->timeGain += Abc_Clock() - clk;
    pProf->nGainCalls++;
    return Gain;
}

static int Cec_TranCandGainCompare( const void * p0, const void * p1 )
{
    Cec_TranCand_t const * pC0 = (Cec_TranCand_t const *)p0;
    Cec_TranCand_t const * pC1 = (Cec_TranCand_t const *)p1;
    if ( pC0->Gain != pC1->Gain )
        return pC1->Gain - pC0->Gain;
    if ( pC0->nKind != pC1->nKind )
        return pC0->nKind - pC1->nKind;
    if ( pC0->nGates != pC1->nGates )
        return pC0->nGates - pC1->nGates;
    if ( pC0->iOut != pC1->iOut )
        return pC0->iOut - pC1->iOut;
    return memcmp( pC0->Recipe, pC1->Recipe,
        sizeof(int) * 2 * pC0->nGates );
}

static int Cec_TranCandPriorityCompare( const void * p0, const void * p1 )
{
    Cec_TranCand_t const * pC0 = (Cec_TranCand_t const *)p0;
    Cec_TranCand_t const * pC1 = (Cec_TranCand_t const *)p1;
    if ( pC0->Gain != pC1->Gain )
        return pC1->Gain - pC0->Gain;
    if ( pC0->nMffc != pC1->nMffc )
        return pC1->nMffc - pC0->nMffc;
    if ( pC0->iTarget != pC1->iTarget )
        return pC1->iTarget - pC0->iTarget;
    return Cec_TranCandGainCompare( p0, p1 );
}

// Group candidates by MFFC-ranked target before admitting all existing
// members and one constructed recipe per root.  The retained batch is sorted
// separately by proof priority.
static int Cec_TranCandRootCompare( const void * p0, const void * p1 )
{
    Cec_TranCand_t const * pC0 = (Cec_TranCand_t const *)p0;
    Cec_TranCand_t const * pC1 = (Cec_TranCand_t const *)p1;
    if ( pC0->nMffc != pC1->nMffc )
        return pC1->nMffc - pC0->nMffc;
    if ( pC0->iTarget != pC1->iTarget )
        return pC1->iTarget - pC0->iTarget;
    return Cec_TranCandGainCompare( p0, p1 );
}

static int Cec_TranCandVecEvalSortTail( Gia_Man_t * p,
    Cec_TranCandVec_t * pVec, int iStart, Cec_TranProf_t * pProf )
{
    int i, nEvals = 0;
    for ( i = iStart; i < pVec->nSize; i++ )
        if ( pVec->pArray[i].Gain < 0 )
        {
            pVec->pArray[i].Gain = Cec_TranRootCandidateGainEval(
                p, pVec->pArray + i, pProf );
            nEvals++;
        }
    if ( pVec->nSize - iStart > 1 )
        qsort( pVec->pArray + iStart, pVec->nSize - iStart,
            sizeof(Cec_TranCand_t), Cec_TranCandGainCompare );
    return nEvals;
}

// Apply one proved replacement per target in one topological duplication.
// Replacements only use earlier literals, so if an earlier selected target is
// itself rewritten, every later recipe automatically sees its equivalent new
// representative.  This is the root-scope analogue of reducing all proved
// signal-correspondence classes at once.
static Gia_Man_t * Cec_TranDupRootBundle( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, Vec_Int_t * vSelected )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int * pSelect = ABC_FALLOC( int, Gia_ManObjNum(p) );
    int i, k, iCand, iLit0, iLit1, iRep;
    Vec_IntForEachEntry( vSelected, iCand, k )
        pSelect[pCands[iCand].iTarget] = iCand;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + 4 * Vec_IntSize(vSelected) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Gia_ObjFanin0Copy( pObj );
        iLit1 = Gia_ObjFanin1Copy( pObj );
        iCand = pSelect[i];
        if ( iCand < 0 )
        {
            pObj->Value = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
            continue;
        }
        iRep = Cec_TranRecipeBuild( p, pNew, pCands + iCand );
        pObj->Value = iRep;
    }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    ABC_FREE( pSelect );
    return pNew;
}

static Vec_Int_t * Cec_TranSelectRootBatchBundle( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, Vec_Int_t * vStatus, int nCands,
    int nSelectMax )
{
    Vec_Int_t * vSelected = Vec_IntAlloc( nCands );
    int * pTargetPos = ABC_FALLOC( int, Gia_ManObjNum(p) );
    int i, iPos, iPrev;
    for ( i = 0; i < nCands; i++ )
    {
        if ( !Vec_IntEntry(vStatus, i) )
            continue;
        iPos = pTargetPos[pCands[i].iTarget];
        if ( iPos >= 0 )
        {
            iPrev = Vec_IntEntry( vSelected, iPos );
            if ( pCands[i].Gain > pCands[iPrev].Gain )
                Vec_IntWriteEntry( vSelected, iPos, i );
            continue;
        }
        if ( nSelectMax >= 0 && Vec_IntSize(vSelected) >= nSelectMax )
            continue;
        pTargetPos[pCands[i].iTarget] = Vec_IntSize(vSelected);
        Vec_IntPush( vSelected, i );
    }
    ABC_FREE( pTargetPos );
    return vSelected;
}

// Exact dry-run size for one proof-stage subset, using the same winner
// selection and cleanup as the unified commit.
static void Cec_TranRootBundleCost( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, Vec_Int_t * vStatus, int nCands,
    int nSelectMax, int * pnAnds, int * pnRegs )
{
    Vec_Int_t * vSelected = Cec_TranSelectRootBatchBundle( p, pCands,
        vStatus, nCands, nSelectMax );
    Gia_Man_t * pTemp, * pClean;
    if ( Vec_IntSize(vSelected) == 0 )
    {
        *pnAnds = Gia_ManAndNum( p );
        *pnRegs = Gia_ManRegNum( p );
        Vec_IntFree( vSelected );
        return;
    }
    pTemp = Cec_TranDupRootBundle( p, pCands, vSelected );
    pClean = Gia_ManCleanup( pTemp );
    *pnAnds = Gia_ManAndNum( pClean );
    *pnRegs = Gia_ManRegNum( pClean );
    Gia_ManStop( pTemp );
    Gia_ManStop( pClean );
    Vec_IntFree( vSelected );
}

// Select the best proved recipe for each target, then commit all selected
// targets together.  Different proved alternatives of one target form one
// equivalence class, so only the highest exact-gain representative is needed.
static int Cec_TranCommitRootBatchBundle( Gia_Man_t ** pp,
    Cec_TranCand_t const * pCands, Vec_Int_t * vStatus, int nCands,
    int nSelectMax, Cec_ParTran_t * pPars, Cec_TranProf_t * pProf,
    Vec_Int_t ** pvSelected )
{
    Gia_Man_t * p = *pp, * pFinal, * pClean;
    Vec_Int_t * vObjMap, * vSelected;
    int Gain, fProved = 1;
    abctime clk;
    *pvSelected = NULL;
    vSelected = Cec_TranSelectRootBatchBundle( p, pCands, vStatus,
        nCands, nSelectMax );
    if ( Vec_IntSize(vSelected) == 0 )
    {
        Vec_IntFree( vSelected );
        return 0;
    }
    pFinal = Cec_TranDupRootBundle( p, pCands, vSelected );
    vObjMap = Cec_TranObjMapCapture( p );
    pClean = Cec_TranCleanupMapped( pFinal, vObjMap );
    Gain = Cec_TranGain( p, pClean );
    if ( Gain < pPars->nGainMin )
    {
        Gia_ManStop( pFinal );
        Gia_ManStop( pClean );
        Vec_IntFree( vObjMap );
        Vec_IntFree( vSelected );
        return 0;
    }
    if ( pPars->fShadow )
    {
        clk = Abc_Clock();
        fProved = Cec_TranProveWhole( p, pFinal, pPars, pProf );
        pProf->timeShadow += Abc_Clock() - clk;
        pProf->nShadowCalls++;
    }
    if ( !fProved )
    {
        Gia_ManStop( pFinal );
        Gia_ManStop( pClean );
        Vec_IntFree( vObjMap );
        Vec_IntFree( vSelected );
        return 0;
    }
    if ( pPars->fVerbose )
        Abc_Print( 1, "  accepted root batch bundle: roots=%d, exact combined gain=%d.\n",
            Vec_IntSize(vSelected), Gain );
    Gia_ManStop( p );
    Gia_ManStop( pFinal );
    *pp = pClean;
    Vec_IntFree( vObjMap );
    *pvSelected = vSelected;
    return Vec_IntSize(vSelected);
}

static int Cec_TranCandVecPeek( Cec_TranCandVec_t * p, Cec_TranCand_t * pCand,
    Cec_TranCandVec_t const * pTried, int * pnTriedSkipped,
    int const * pUnknown, Cec_ParTran_t const * pPars,
    int * pnCooldownSkipped )
{
    while ( p->iHead < p->nSize )
    {
        Cec_TranCand_t * pEntry = p->pArray + p->iHead;
        int iHist = 2 * pEntry->iTarget + !pEntry->fStrict;
        int fHigh = pEntry->Gain >= pPars->nHardGain ||
                    pEntry->nMffc >= pPars->nHardMffc;
        int nUnknownMax = pEntry->fStrict || fHigh ?
            pPars->nUnknownMax : pPars->nLowUnknownMax;
        if ( Cec_TranCandVecContains(pTried, pEntry) )
        {
            (*pnTriedSkipped)++;
            p->iHead++;
        }
        else if ( nUnknownMax && pUnknown[iHist] >= nUnknownMax )
        {
            (*pnCooldownSkipped)++;
            p->iHead++;
        }
        else
        {
            *pCand = *pEntry;
            return 1;
        }
    }
    return 0;
}

static void Cec_TranCandVecDrop( Cec_TranCandVec_t * p )
{
    assert( p->iHead < p->nSize );
    p->iHead++;
}

static int Cec_TranRootCompare( const void * p0, const void * p1 )
{
    Cec_TranRoot_t const * pR0 = (Cec_TranRoot_t const *)p0;
    Cec_TranRoot_t const * pR1 = (Cec_TranRoot_t const *)p1;
    if ( pR0->nMffc != pR1->nMffc )
        return pR1->nMffc - pR0->nMffc;
    return pR1->iObj - pR0->iObj;
}

static word Cec_TranLitHash( Cec_TranSim_t * pSim, int iLit )
{
    word Hash = ABC_CONST(0xcbf29ce484222325);
    int s;
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        Hash ^= Cec_TranSimLit( pSim, iLit, s );
        Hash *= ABC_CONST(0x100000001b3);
        Hash ^= Hash >> 32;
    }
    return Hash;
}

static int Cec_TranSigEntCompare( const void * p0, const void * p1 )
{
    Cec_TranSigEnt_t const * pE0 = (Cec_TranSigEnt_t const *)p0;
    Cec_TranSigEnt_t const * pE1 = (Cec_TranSigEnt_t const *)p1;
    if ( pE0->Hash < pE1->Hash )
        return -1;
    if ( pE0->Hash > pE1->Hash )
        return 1;
    if ( Abc_Lit2Var(pE0->iLit) != Abc_Lit2Var(pE1->iLit) )
        return Abc_Lit2Var(pE1->iLit) - Abc_Lit2Var(pE0->iLit);
    return pE0->iLit - pE1->iLit;
}

static Cec_TranSigEnt_t * Cec_TranBuildSigIndex( Cec_TranSim_t * pSim,
    int * pnEntries )
{
    Gia_Man_t * p = pSim->pGia;
    Gia_Obj_t * pObj;
    Cec_TranSigEnt_t * pEntries;
    int i, f, nCands = 1, nEntries = 0;
    // The constant is a valid Direct divisor even though Gia_ObjIsCand()
    // intentionally excludes it.
    Gia_ManForEachObj( p, pObj, i )
        if ( Gia_ObjIsCand(pObj) )
            nCands++;
    pEntries = ABC_ALLOC( Cec_TranSigEnt_t, 2 * nCands );
    for ( f = 0; f < 2; f++ )
    {
        pEntries[nEntries].iLit = Abc_Var2Lit( 0, f );
        pEntries[nEntries].Hash = Cec_TranLitHash( pSim, pEntries[nEntries].iLit );
        nEntries++;
    }
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( !Gia_ObjIsCand(pObj) )
            continue;
        for ( f = 0; f < 2; f++ )
        {
            pEntries[nEntries].iLit = Abc_Var2Lit( i, f );
            pEntries[nEntries].Hash = Cec_TranLitHash( pSim, pEntries[nEntries].iLit );
            nEntries++;
        }
    }
    assert( nEntries == 2 * nCands );
    qsort( pEntries, nEntries, sizeof(Cec_TranSigEnt_t), Cec_TranSigEntCompare );
    *pnEntries = nEntries;
    return pEntries;
}

static int Cec_TranSigIndexLowerBound( Cec_TranSigEnt_t * pEntries,
    int nEntries, word Hash )
{
    int Left = 0, Right = nEntries;
    while ( Left < Right )
    {
        int Middle = Left + (Right - Left) / 2;
        if ( pEntries[Middle].Hash < Hash )
            Left = Middle + 1;
        else
            Right = Middle;
    }
    return Left;
}

static int Cec_TranSigIndexUpperBound( Cec_TranSigEnt_t * pEntries,
    int iStart, int nEntries, word Hash )
{
    int Left = iStart, Right = nEntries;
    while ( Left < Right )
    {
        int Middle = Left + (Right - Left) / 2;
        if ( pEntries[Middle].Hash <= Hash )
            Left = Middle + 1;
        else
            Right = Middle;
    }
    return Left;
}

// Entries with the same signature hash are ordered by decreasing object ID.
// Direct replacements must be topologically earlier than the target, so jump
// over the whole ineligible suffix prefix instead of retesting it per root.
static int Cec_TranSigIndexFirstEarlier( Cec_TranSigEnt_t * pEntries,
    int iStart, int iStop, int iTarget )
{
    int Left = iStart, Right = iStop;
    while ( Left < Right )
    {
        int Middle = Left + (Right - Left) / 2;
        if ( Abc_Lit2Var(pEntries[Middle].iLit) >= iTarget )
            Left = Middle + 1;
        else
            Right = Middle;
    }
    return Left;
}

static void Cec_TranMarkMffc_rec( Gia_Man_t * p, int iObj, char * pMark )
{
    Gia_Obj_t * pObj;
    int iFan;
    if ( pMark[iObj] )
        return;
    pMark[iObj] = 1;
    pObj = Gia_ManObj( p, iObj );
    if ( !Gia_ObjIsAnd(pObj) )
        return;
    iFan = Gia_ObjFaninId0p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         Gia_ObjRefNumId(p, iFan) == 1 )
        Cec_TranMarkMffc_rec( p, iFan, pMark );
    iFan = Gia_ObjFaninId1p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         Gia_ObjRefNumId(p, iFan) == 1 )
        Cec_TranMarkMffc_rec( p, iFan, pMark );
}

// Collect physical divisor nodes by increasing TFI distance.  MFFC nodes are
// traversed but never retained, which reaches the MFFC boundary and then its
// upstream support.  PI and RO objects are both legal CIs.  Complemented
// phases are explored by the dependency engine and therefore do not consume
// separate B slots.  Every collected divisor is in the target's TFI and has a
// smaller topological object ID, so a separate full-graph TFO mark is both
// redundant and needlessly quadratic across all roots.
static Vec_Int_t * Cec_TranCollectDivPool( Gia_Man_t * p, int iTarget,
    int nDepthMax, int nNodesMax, char ** ppMffc )
{
    Vec_Int_t * vPool = Vec_IntAlloc( nNodesMax ? nNodesMax : 64 );
    Vec_Int_t * vFront = Vec_IntAlloc( 32 );
    Vec_Int_t * vNext = Vec_IntAlloc( 32 );
    char * pSeen = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
    Gia_Obj_t * pObj, * pFan;
    int d, i, k, iObj, iFan, fFull = 0;
    Cec_TranMarkMffc_rec( p, iTarget, pMffc );
    pSeen[iTarget] = 1;
    Vec_IntPush( vFront, iTarget );
    for ( d = 1; Vec_IntSize(vFront) && (!nDepthMax || d <= nDepthMax); d++ )
    {
        Vec_IntClear( vNext );
        Vec_IntForEachEntry( vFront, iObj, i )
        {
            pObj = Gia_ManObj( p, iObj );
            if ( !Gia_ObjIsAnd(pObj) )
                continue;
            for ( k = 0; k < 2; k++ )
            {
                iFan = k ? Gia_ObjFaninId1p(p, pObj) :
                           Gia_ObjFaninId0p(p, pObj);
                if ( pSeen[iFan] )
                    continue;
                pSeen[iFan] = 1;
                pFan = Gia_ManObj( p, iFan );
                if ( iFan != 0 && iFan < iTarget && Gia_ObjIsCand(pFan) &&
                     !pMffc[iFan] && !fFull )
                {
                    Vec_IntPush( vPool, iFan );
                    fFull = nNodesMax && Vec_IntSize(vPool) >= nNodesMax;
                }
                if ( Gia_ObjIsAnd(pFan) )
                    Vec_IntPush( vNext, iFan );
            }
        }
        if ( fFull )
            break;
        ABC_SWAP( Vec_Int_t, *vFront, *vNext );
    }
    Vec_IntFree( vFront );
    Vec_IntFree( vNext );
    ABC_FREE( pSeen );
    *ppMffc = pMffc;
    return vPool;
}

static int Cec_TranRecipeCodeFromResub( int iLit, int nVars,
    Vec_Int_t * vPool )
{
    int iVar = Abc_Lit2Var( iLit );
    if ( iVar == 0 )
        return Abc_LitIsCompl( iLit );
    if ( iVar < nVars )
    {
        assert( iVar >= 2 && iVar - 2 < Vec_IntSize(vPool) );
        return Abc_Var2Lit( Vec_IntEntry(vPool, iVar - 2),
            Abc_LitIsCompl(iLit) );
    }
    return Cec_TranRecipeGateCode( iVar - nVars, Abc_LitIsCompl(iLit) );
}

static int Cec_TranComputeDependency( Cec_TranSim_t * pSim,
    Cec_ParTran_t * pPars, Cec_TranRoot_t const * pRoot,
    Vec_Int_t * vPool, word * pCare, int fStrict,
    Cec_TranCand_t * pCand )
{
    Vec_Ptr_t * vDivs = Vec_PtrAlloc( Vec_IntSize(vPool) + 2 );
    word * pOff = ABC_ALLOC( word, pSim->nSlots );
    word * pOn  = ABC_ALLOC( word, pSim->nSlots );
    int * pArray = NULL;
    int i, s, iObj, nArray, nVars, nLimit, Code;
    word Target, Care;
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        Target = Cec_TranSimLit( pSim, Abc_Var2Lit(pRoot->iObj, 0), s );
        Care = pCare ? pCare[s] : ~(word)0;
        pOff[s] = ~Target & Care;
        pOn[s]  =  Target & Care;
    }
    Vec_PtrPushTwo( vDivs, pOff, pOn );
    Vec_IntForEachEntry( vPool, iObj, i )
        Vec_PtrPush( vDivs, Cec_TranSimObj(pSim, iObj) );
    nLimit = pPars->fUseConstr ?
        Abc_MinInt( pPars->nDepNodesMax,
            Abc_MaxInt(0, pRoot->nMffc - pPars->nGainMin) ) : 0;
    nArray = Abc_ResubComputeFunction( Vec_PtrArray(vDivs),
        Vec_PtrSize(vDivs), pSim->nSlots, nLimit,
        Vec_IntSize(vPool), 0, 0, 0, pPars->fVerbose, &pArray );
    if ( nArray == 0 )
    {
        Vec_PtrFree( vDivs );
        ABC_FREE( pOff );
        ABC_FREE( pOn );
        return 0;
    }
    memset( pCand, 0, sizeof(*pCand) );
    pCand->iTarget = pRoot->iObj;
    pCand->nMffc = pRoot->nMffc;
    pCand->Gain = -1;
    pCand->fStrict = fStrict;
    pCand->nGates = nArray / 2;
    assert( pCand->nGates <= CEC_TRAN_RECIPE_NODES_MAX );
    nVars = Vec_PtrSize( vDivs );
    for ( i = 0; i < 2 * pCand->nGates; i++ )
        pCand->Recipe[i] = Cec_TranRecipeCodeFromResub(
            pArray[i], nVars, vPool );
    pCand->iOut = Cec_TranRecipeCodeFromResub(
        pArray[nArray-1], nVars, vPool );
    pCand->nKind = pCand->nGates ? CEC_TRAN_CAND_CONSTR :
        (Abc_Lit2Var(pCand->iOut) == 0 ?
            CEC_TRAN_CAND_CONST : CEC_TRAN_CAND_EXIST);
    pCand->iDiv0 = pCand->iDiv1 = -1;
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) || Abc_Lit2Var(Code) == 0 )
            continue;
        if ( pCand->iDiv0 == -1 )
            pCand->iDiv0 = Code;
        else if ( Abc_Lit2Var(pCand->iDiv0) != Abc_Lit2Var(Code) )
        {
            pCand->iDiv1 = Code;
            break;
        }
    }
    assert( Cec_TranRecipeMatchesRoot(pSim, pCand, pCare) );
    if ( !pPars->fUseExisting && pCand->nGates == 0 &&
         Abc_Lit2Var(pCand->iOut) != 0 )
        nArray = 0;
    Vec_PtrFree( vDivs );
    ABC_FREE( pOff );
    ABC_FREE( pOn );
    return nArray != 0;
}

static void Cec_TranCollectGlobalExact( Cec_TranSim_t * pSim,
    Cec_TranRoot_t const * pRoot, Cec_TranSigEnt_t * pSigIndex,
    int nSigEntries, char const * pMffc,
    int nKeepMax, int fIncludeConst,
    int fStrict, Cec_TranCandVec_t const * pTried,
    Cec_TranCandVec_t * pExist, Cec_TranDiscStat_t * pStat )
{
    word TargetHash = Cec_TranLitHash( pSim,
        Abc_Var2Lit(pRoot->iObj, 0) );
    int iBeg = Cec_TranSigIndexLowerBound( pSigIndex, nSigEntries,
        TargetHash );
    int iEnd = Cec_TranSigIndexUpperBound( pSigIndex, iBeg, nSigEntries,
        TargetHash );
    int i = Cec_TranSigIndexFirstEarlier( pSigIndex, iBeg, iEnd,
        pRoot->iObj );
    int nKept = 0, iLit, iObj;
    Cec_TranCand_t Cand;
    for ( ; i < iEnd; i++ )
    {
        iLit = pSigIndex[i].iLit;
        iObj = Abc_Lit2Var( iLit );
        assert( iObj < pRoot->iObj );
        if ( !fIncludeConst && iObj == 0 )
            continue;
        if ( pMffc[iObj] )
            continue;
        pStat->nExisting++;
        pStat->nSigChecks++;
        if ( !Cec_TranSigMatchesRoot(pSim, pRoot->iObj,
                iLit, -1, 0, NULL) )
        {
            pStat->nSigRejected++;
            continue;
        }
        pStat->nSigMatched++;
        Cand = Cec_TranCandCreate( pRoot->iObj, iLit, -1, 0,
            pRoot->nMffc, iObj ? CEC_TRAN_CAND_EXIST :
            CEC_TRAN_CAND_CONST, fStrict );
        // A zero-gate replacement by an earlier object outside this MFFC
        // removes exactly the target MFFC.  Avoid recomputing the same
        // recursive MFFC delta once per admitted existing relation.
        Cand.Gain = pRoot->nMffc;
        // The signature index contains each literal exactly once.  Candidates
        // from other roots have a different iTarget and cannot be duplicates,
        // so scanning the global current-wave vector here is both redundant
        // and quadratic in the number of admitted relations.
        if ( Cec_TranCandVecContains(pTried, &Cand) )
            continue;
        if ( nKeepMax && nKept >= nKeepMax )
            break;
        Cec_TranCandVecPush( pExist, Cand );
        nKept++;
    }
}

static void Cec_TranCollectStrictExisting( Gia_Man_t * p,
    Cec_TranSim_t * pSim, Cec_ParTran_t * pPars,
    Cec_TranRoot_t * pRoots, int nRoots, Cec_TranSigEnt_t * pSigIndex,
    int nSigEntries, Cec_TranCandVec_t const * pTried,
    char const * pSolved,
    Cec_TranCandVec_t * pExist,
    Cec_TranDiscStat_t * pStat, Cec_TranProf_t * pProf )
{
    int r, f, iExistStart, iExistingStart;
    char * pMffc = NULL;
    Cec_TranCand_t Cand;
    abctime clk;
    for ( r = 0; r < nRoots; r++ )
    {
        if ( pSolved && pSolved[pRoots[r].iObj] )
            continue;
        if ( pRoots[r].nMffc < pPars->nGainMin )
            continue;
        iExistStart = pExist->nSize;
        clk = Abc_Clock();
        // Constants are cheap and are always reconsidered.  Ordinary existing
        // nodes already had a global opportunity in the preceding &scorr, so
        // root &stran admits at most one of them and only for a large MFFC.
        for ( f = 0; f < 2; f++ )
        {
            pStat->nConstants++;
            pStat->nSigChecks++;
            if ( !Cec_TranSigMatchesRoot(pSim, pRoots[r].iObj,
                    Abc_Var2Lit(0, f), -1, 0, NULL) )
            {
                pStat->nSigRejected++;
                continue;
            }
            pStat->nSigMatched++;
            Cand = Cec_TranCandCreate( pRoots[r].iObj,
                Abc_Var2Lit(0, f), -1, 0, pRoots[r].nMffc,
                CEC_TRAN_CAND_CONST, 1 );
            Cand.Gain = pRoots[r].nMffc;
            if ( !Cec_TranCandVecContains(pTried, &Cand) )
                Cec_TranCandVecPush( pExist, Cand );
        }
        iExistingStart = pExist->nSize;
        if ( pPars->fUseExisting &&
             pRoots[r].nMffc >= pPars->nHardMffc )
        {
            pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
            Cec_TranMarkMffc_rec( p, pRoots[r].iObj, pMffc );
            Cec_TranCollectGlobalExact( pSim, pRoots + r,
                pSigIndex, nSigEntries, pMffc, 1, 0, 1, pTried,
                pExist, pStat );
            ABC_FREE( pMffc );
            pProf->nRootExistingKept += pExist->nSize - iExistingStart;
        }
        else if ( pPars->fUseExisting )
            pProf->nRootExistingSkipped++;
        pProf->timeExisting += Abc_Clock() - clk;
        pProf->nRootGainEvals += Cec_TranCandVecEvalSortTail( p,
            pExist, iExistStart, pProf );
        Cec_TranDiscFinishRoot( pStat, 0,
            pExist->nSize - iExistStart );
    }
}

static void Cec_TranCollectStrictConstructed( Gia_Man_t * p,
    Cec_TranSim_t * pSim, Cec_ParTran_t * pPars,
    Cec_TranRoot_t * pRoots, int nRoots,
    Cec_TranCandVec_t const * pTried, char const * pSolved,
    Cec_TranCandVec_t * pConstr, Cec_TranDiscStat_t * pStat,
    Cec_TranProf_t * pProf )
{
    int r, iConstrStart, i, k, f0, f1, fOr;
    char * pMffc;
    Vec_Int_t * vPool;
    Cec_TranCand_t Cand;
    Cec_TranCandVec_t Local;
    abctime clk;
    for ( r = 0; r < nRoots; r++ )
    {
        if ( pSolved && pSolved[pRoots[r].iObj] )
            continue;
        if ( pRoots[r].nMffc < pPars->nGainMin )
            continue;
        iConstrStart = pConstr->nSize;
        clk = Abc_Clock();
        vPool = Cec_TranCollectDivPool( p, pRoots[r].iObj,
            pPars->nConstrMax, pPars->nConstrBaseMax, &pMffc );
        if ( pPars->fVerbose )
        {
            Abc_Print( 1, "  dependency pool root=%d mffc=%d nodes=%d: ",
                pRoots[r].iObj, pRoots[r].nMffc, Vec_IntSize(vPool) );
            Vec_IntPrint( vPool );
        }
        pProf->timeSpec += Abc_Clock() - clk;
        memset( &Local, 0, sizeof(Local) );
        pStat->nConstructed++;
        pStat->nSigChecks++;
        clk = Abc_Clock();
        if ( Cec_TranComputeDependency(pSim, pPars, pRoots + r,
                vPool, NULL, 1, &Cand) )
        {
            // Constants and single existing literals are collected by the
            // initial lane, so this queue remains constructed-only.
            if ( Cand.nGates && !Cec_TranCandVecContains(pTried, &Cand) )
            {
                pStat->nSigMatched++;
                Cec_TranCandVecPush( &Local, Cand );
            }
            else
                pStat->nSigRejected++;
        }
        else
            pStat->nSigRejected++;

        // Resub returns only one dependency recipe.  Fill the same root class
        // with several cheap one-gate functions found by simulation.  They
        // never edit the source graph or create XOR queries; the shared proof
        // graph materializes the endpoint once for scorr, while CBS decomposes
        // its AND/NAND relation into three literal cubes.  Stop after top-K
        // distinct matches; all one-gate matches have the same gate cost and
        // are ranked with the dependency recipe by exact local gain below.
        for ( i = 0; i < Vec_IntSize(vPool) &&
                     Local.nSize < pPars->nRootConstrTop; i++ )
        for ( k = i + 1; k < Vec_IntSize(vPool) &&
                         Local.nSize < pPars->nRootConstrTop; k++ )
        for ( f0 = 0; f0 < 2 && Local.nSize < pPars->nRootConstrTop; f0++ )
        for ( f1 = 0; f1 < 2 && Local.nSize < pPars->nRootConstrTop; f1++ )
        for ( fOr = 0; fOr < 2 && Local.nSize < pPars->nRootConstrTop; fOr++ )
        {
            int iLit0 = Abc_Var2Lit( Vec_IntEntry(vPool, i), f0 );
            int iLit1 = Abc_Var2Lit( Vec_IntEntry(vPool, k), f1 );
            pStat->nConstructed++;
            pStat->nSigChecks++;
            if ( !Cec_TranSigMatchesRoot(pSim, pRoots[r].iObj,
                    iLit0, iLit1, fOr, NULL) )
            {
                pStat->nSigRejected++;
                continue;
            }
            pStat->nSigMatched++;
            Cand = Cec_TranCandCreate( pRoots[r].iObj, iLit0, iLit1,
                fOr, pRoots[r].nMffc, CEC_TRAN_CAND_CONSTR, 1 );
            if ( Cec_TranCandVecContains(pTried, &Cand) ||
                 Cec_TranCandVecContains(&Local, &Cand) )
                continue;
            Cec_TranCandVecPush( &Local, Cand );
        }
        pProf->timeConstruct += Abc_Clock() - clk;
        pProf->nRootGainEvals += Cec_TranCandVecEvalSortTail( p,
            &Local, 0, pProf );
        for ( i = 0; i < Local.nSize && i < pPars->nRootConstrTop; i++ )
            Cec_TranCandVecPush( pConstr, Local.pArray[i] );
        Cec_TranCandVecStop( &Local );
        Cec_TranDiscFinishRoot( pStat, 0,
            pConstr->nSize - iConstrStart );
        Vec_IntFree( vPool );
        ABC_FREE( pMffc );
    }
}

static void Cec_TranCollectRootPhase( Gia_Man_t * p,
    Cec_TranSim_t * pSim, Cec_ParTran_t * pPars,
    Cec_TranRoot_t * pRoots, int nRoots,
    Cec_TranSigEnt_t * pSigIndex, int nSigEntries,
    Cec_TranCandVec_t const * pTried, char const * pSolved,
    int fExistingPhase, Cec_TranCandVec_t * pExist,
    Cec_TranCandVec_t * pConstr, Cec_TranCandVec_t * pAll,
    Cec_TranDiscStat_t * pStat, Cec_TranProf_t * pProf )
{
    int i;
    Cec_TranCandVecClear( pExist );
    Cec_TranCandVecClear( pConstr );
    Cec_TranCandVecClear( pAll );
    if ( fExistingPhase )
        Cec_TranCollectStrictExisting( p, pSim, pPars, pRoots, nRoots,
            pSigIndex, nSigEntries, pTried, pSolved, pExist, pStat, pProf );
    if ( pPars->fUseConstr )
        Cec_TranCollectStrictConstructed( p, pSim, pPars, pRoots, nRoots,
            pTried, pSolved, pConstr, pStat, pProf );
    for ( i = 0; i < pExist->nSize; i++ )
        Cec_TranCandVecPush( pAll, pExist->pArray[i] );
    for ( i = 0; i < pConstr->nSize; i++ )
        Cec_TranCandVecPush( pAll, pConstr->pArray[i] );
    if ( pAll->nSize > 1 )
        qsort( pAll->pArray, pAll->nSize,
            sizeof(Cec_TranCand_t), Cec_TranCandRootCompare );
}

static void Cec_TranCollectContextRecipes( Gia_Man_t * p,
    Cec_TranSim_t * pSim, Cec_ParTran_t * pPars,
    Cec_TranRoot_t const * pRoot, Cec_TranSigEnt_t * pSigIndex,
    int nSigEntries, Cec_TranCandVec_t const * pTried,
    Cec_TranCandVec_t * pExist, Cec_TranCandVec_t * pConstr,
    Cec_TranDiscStat_t * pStat, Cec_TranProf_t * pProf )
{
    int iExistStart = pExist->nSize, iConstrStart = pConstr->nSize;
    char * pMffc;
    Vec_Int_t * vPool;
    Cec_TranCand_t Cand;
    word * pCare;
    abctime clk = Abc_Clock();
    vPool = Cec_TranCollectDivPool( p, pRoot->iObj,
        pPars->nConstrMax, pPars->nConstrBaseMax, &pMffc );
    pCare = Cec_TranSimComputeContextCare( pSim, pPars, pRoot->iObj );
    pProf->timeCare += Abc_Clock() - clk;
    pProf->nCareCalls++;
    clk = Abc_Clock();
    if ( pPars->fUseExisting )
        Cec_TranCollectGlobalExact( pSim, pRoot,
            pSigIndex, nSigEntries, pMffc, pPars->nDivsMax, 1, 0, pTried,
            pExist, pStat );
    pProf->timeExisting += Abc_Clock() - clk;
    pStat->nConstructed++;
    pStat->nSigChecks++;
    clk = Abc_Clock();
    if ( Cec_TranComputeDependency(pSim, pPars, pRoot,
            vPool, pCare, 0, &Cand) )
    {
        pStat->nSigMatched++;
        if ( !Cec_TranCandVecContains(pTried, &Cand) &&
             (Cand.nGates || !Cec_TranCandVecContainsRange(
                 pExist, iExistStart, &Cand)) )
            Cec_TranCandVecPush( Cand.nGates ? pConstr : pExist, Cand );
    }
    else
        pStat->nSigRejected++;
    pProf->timeConstruct += Abc_Clock() - clk;
    Cec_TranCandVecEvalSortTail( p, pExist, iExistStart, pProf );
    Cec_TranCandVecEvalSortTail( p, pConstr, iConstrStart, pProf );
    Cec_TranDiscFinishRoot( pStat, 1,
        pExist->nSize - iExistStart + pConstr->nSize - iConstrStart );
    ABC_FREE( pCare );
    Vec_IntFree( vPool );
    ABC_FREE( pMffc );
}

static Gia_Man_t * Cec_ManSequentialDirectResubstitution( Gia_Man_t * pGia,
    Cec_ParTran_t * pPars )
{
    Cec_TranProf_t Prof = {0};
    Cec_TranDiscStat_t Disc = {0};
    Cec_TranCandVec_t qStrictExist = {0}, qStrictConstr = {0};
    Cec_TranCandVec_t qStrictAll = {0};
    Cec_TranCandVec_t qRootProved = {0};
    Cec_TranCandVec_t qContextExist = {0}, qContextConstr = {0};
    Cec_TranCandVec_t vTried = {0};
    Cec_TranRoot_t * pRoots = NULL;
    Cec_TranSigEnt_t * pSigIndex = NULL;
    Cec_TranSim_t * pSim;
    Cec_TranPatDb_t * pDb;
    Gia_Man_t * p;
    Gia_Obj_t * pObj;
    int * pUnknown;
    char * pRootSolved;
    int nRoots = 0, nSigEntries = 0;
    int nPositive = 0, nGainRejected = 0, nUnproved = 0;
    int nTried = 0, nAccepted = 0, nRound = 0;
    int nStrictProofs = 0, nContextProofs = 0;
    int nConstantProofs = 0, nExistingProofs = 0, nConstructedProofs = 0;
    int nConstantAccepted = 0, nExistingAccepted = 0, nConstructedAccepted = 0;
    int nCooldownSkipped = 0, nBurstSkipped = 0;
    int fChanged = 0, fCegisRestart = 0, fRootExistingDone = 0;
    int nAndOld, nRegOld;
    abctime clk = Abc_Clock(), clkPhase, clkCand, timeCand;
    assert( Gia_ManRegNum(pGia) > 0 );
    Abc_Print( 1, "Sequential direct resubstitution: AND = %d, Reg = %d, random lanes = %d, sequential frames = %d, signature samples = %d, proof frames = %d, conf = %d, proof scope = %s%s, root batch = %s, root search width = %d, root waves = %d, constructed top-K = %d, contextual proof limit = %s, CEX batch = %d, TFI depth = %d, pool nodes = %d, dependency nodes = %d, unknown cooldown = low:%d/high:%d, global exact = %s, dependency synthesis = %s.\n",
        Gia_ManAndNum(pGia), Gia_ManRegNum(pGia), pPars->nSimWords * 64,
        pPars->nSimFrames, pPars->nSimWords * 64 * pPars->nSimFrames,
        pPars->nFrames, pPars->nBTLimit,
        pPars->nProofScope == CEC_TRAN_PROOF_ROOT ? "root" :
        pPars->nProofScope == CEC_TRAN_PROOF_WINDOW ? "window" : "output",
        pPars->nProofScope == CEC_TRAN_PROOF_WINDOW ? " (bounded TFO)" : "",
        pPars->nProofScope == CEC_TRAN_PROOF_ROOT ? "on" : "off",
        pPars->nRootBatch, pPars->nRootWaves, pPars->nRootConstrTop,
        pPars->nCandMax ? "bounded" : "unlimited",
        pPars->nCexBatch, pPars->nConstrMax, pPars->nConstrBaseMax,
        pPars->nDepNodesMax,
        pPars->nLowUnknownMax, pPars->nUnknownMax,
        pPars->fUseExisting ?
            (pPars->nProofScope == CEC_TRAN_PROOF_ROOT ?
                "large-MFFC-only" : "on") : "off",
        pPars->fUseConstr ? "on" : "off" );
    Abc_Print( 1, "Sequential direct proof budgets: root-conf=%d root-total=unlimited root-min-gain=%d root-existing-mffc=%d; context-low=%d/%d context-high=%d/%d context-high-gain=%d context-high-mffc=%d.\n",
        pPars->nBTLimit, pPars->nRootGainMin, pPars->nHardMffc,
        pPars->nScoutBTLimit, pPars->nScoutConfTotal, pPars->nBTLimit,
        pPars->nHardConfTotal, pPars->nHardGain, pPars->nHardMffc );
    p = Gia_ManDup( pGia );
    Prof.nStageAndBefore = Prof.nStageAndAfterComb =
        Prof.nStageAndAfterSeq = Gia_ManAndNum( p );
    Prof.nStageRegBefore = Prof.nStageRegAfterComb =
        Prof.nStageRegAfterSeq = Gia_ManRegNum( p );
    pDb = Cec_TranPatDbStart( p, pPars->nCexMax );
    pUnknown = ABC_CALLOC( int, 2 * Gia_ManObjNum(p) );
    pRootSolved = ABC_CALLOC( char, Gia_ManObjNum(p) );
    do
    {
        Cec_TranCand_t Cand, Temp;
        Cec_TranCandVec_t * pQueue = NULL;
        Vec_Int_t * vCommitMap = NULL;
        char * pCommitAffected = NULL;
        int rContext = 0, fHaveSE, fHaveCE, fHaveCC;
        int fRootExistingPhase = 0;
        int nTriedOld, nAcceptedOld, nUnknownOld, nSatOld, iHist, fWasUnknown;
        int i, fFound, fCandCex, fNeedSigIndex;
        abctime timeUnknownOld;
        // Contextual scopes iterate after commits or CEX refinement.  Root
        // scope iterates only on reachable-CEX construct waves; the source
        // graph itself stays immutable until one final bundle commit.
        if ( nRound )
        {
            assert( fChanged || fCegisRestart );
            if ( fChanged )
                Prof.nCommitRefreshes++;
        }
        fChanged = 0;
        fCegisRestart = 0;
        Cec_TranCandVecClear( &qStrictExist );
        Cec_TranCandVecClear( &qStrictConstr );
        Cec_TranCandVecClear( &qStrictAll );
        Cec_TranCandVecClear( &qContextExist );
        Cec_TranCandVecClear( &qContextConstr );
        clkPhase = Abc_Clock();
        pSim = Cec_TranSimStart( p, pPars, pDb );
        Prof.timeSim += Abc_Clock() - clkPhase;
        Prof.nSimCalls++;
        Abc_ResubPrepareManager( pSim->nSlots );

        Gia_ManCreateRefs( p );
        clkPhase = pPars->fProfile ? Abc_Clock() : 0;
        nRoots = 0;
        Gia_ManForEachAnd( p, pObj, i )
            nRoots++;
        pRoots = ABC_ALLOC( Cec_TranRoot_t, nRoots );
        nRoots = 0;
        Gia_ManForEachAnd( p, pObj, i )
        {
            pRoots[nRoots].iObj = i;
            pRoots[nRoots].nMffc = Gia_NodeMffcSize( p, pObj );
            nRoots++;
        }
        qsort( pRoots, nRoots, sizeof(Cec_TranRoot_t), Cec_TranRootCompare );
        // Keep the reference counts for local MFFC-delta gain evaluation.
        // They are read/mutated/restored by candidate scheduling and released
        // once this snapshot ends; no candidate gain computation rebuilds p.

        pSigIndex = NULL;
        nSigEntries = 0;
        fNeedSigIndex = pPars->fUseExisting &&
            pPars->nProofScope != CEC_TRAN_PROOF_ROOT;
        if ( pPars->fUseExisting &&
             pPars->nProofScope == CEC_TRAN_PROOF_ROOT &&
             !fRootExistingDone )
            for ( i = 0; i < nRoots &&
                 (!pPars->nRootBatch || i < pPars->nRootBatch); i++ )
                if ( !pRootSolved[pRoots[i].iObj] &&
                     pRoots[i].nMffc >= pPars->nHardMffc )
                {
                    fNeedSigIndex = 1;
                    break;
                }
        if ( fNeedSigIndex )
            pSigIndex = Cec_TranBuildSigIndex( pSim, &nSigEntries );
        if ( pPars->fProfile )
            Prof.timeSpec += Abc_Clock() - clkPhase, Prof.nSpecCalls++;
        // The initial root closure contains constants, the restricted existing
        // lane, and top-K constructed recipes together.  Later closures contain
        // only new constructed recipes after a reachable CEX refresh.
        if ( pPars->nProofScope == CEC_TRAN_PROOF_ROOT )
        {
            // -L is a generation cap, not merely a proof-queue cap: do not
            // build divisor pools or dependency recipes for lower-ranked roots
            // that cannot enter the current phase.
            fRootExistingPhase = !fRootExistingDone;
            Cec_TranCollectRootPhase( p, pSim, pPars, pRoots,
                pPars->nRootBatch ? Abc_MinInt(nRoots, pPars->nRootBatch) : nRoots,
                pSigIndex, nSigEntries, &vTried, pRootSolved,
                fRootExistingPhase, &qStrictExist, &qStrictConstr,
                &qStrictAll, &Disc, &Prof );
            if ( fRootExistingPhase )
                fRootExistingDone = 1;
            if ( qStrictAll.nSize )
                Prof.nRootSnapshots++;
        }

        while ( !pPars->nChangesMax || nAccepted < pPars->nChangesMax )
        {
            // Context queues are filled one root at a time.  This preserves
            // lazy discovery after a useful CEX while strict candidates from
            // every root are already globally visible to the scheduler.
            if ( pPars->nProofScope != CEC_TRAN_PROOF_ROOT &&
                 (!pPars->nCandMax || nContextProofs < pPars->nCandMax) )
            {
                while ( rContext < nRoots )
                {
                    fHaveCE = Cec_TranCandVecPeek( &qContextExist, &Temp,
                        &vTried, &Prof.nQueueTriedSkipped, pUnknown,
                        pPars, &nCooldownSkipped );
                    fHaveCC = Cec_TranCandVecPeek( &qContextConstr, &Temp,
                        &vTried, &Prof.nQueueTriedSkipped, pUnknown,
                        pPars, &nCooldownSkipped );
                    if ( fHaveCE || fHaveCC )
                        break;
                    // The roots are sorted by MFFC.  No constant/existing
                    // replacement can remove more local ANDs than the root
                    // MFFC (a constructed recipe removes at most MFFC-1).
                    // Once this upper bound falls below -G, all remaining
                    // roots can be rejected without care computation,
                    // divisor enumeration, or formal proof.
                    if ( pRoots[rContext].nMffc < pPars->nGainMin )
                    {
                        Prof.nContextValueRootSkips += nRoots - rContext;
                        rContext = nRoots;
                        break;
                    }
                    iHist = 2 * pRoots[rContext].iObj + 1;
                    if ( !pPars->nUnknownMax ||
                         pUnknown[iHist] < pPars->nUnknownMax )
                        Cec_TranCollectContextRecipes( p, pSim, pPars,
                            pRoots + rContext, pSigIndex, nSigEntries,
                            &vTried, &qContextExist, &qContextConstr,
                            &Disc, &Prof );
                    else
                        nCooldownSkipped++;
                    rContext++;
                }
            }

            fHaveSE = pPars->nProofScope == CEC_TRAN_PROOF_ROOT &&
                qStrictAll.iHead < qStrictAll.nSize;
            fHaveCE = pPars->nProofScope != CEC_TRAN_PROOF_ROOT &&
                (!pPars->nCandMax || nContextProofs < pPars->nCandMax) &&
                Cec_TranCandVecPeek( &qContextExist, &Temp, &vTried,
                    &Prof.nQueueTriedSkipped, pUnknown, pPars,
                    &nCooldownSkipped );
            fHaveCC = pPars->nProofScope != CEC_TRAN_PROOF_ROOT &&
                (!pPars->nCandMax || nContextProofs < pPars->nCandMax) &&
                Cec_TranCandVecPeek( &qContextConstr, &Temp, &vTried,
                    &Prof.nQueueTriedSkipped, pUnknown, pPars,
                    &nCooldownSkipped );
            if ( !(fHaveSE || fHaveCE || fHaveCC) )
                break;

            // Root scope keeps the source graph immutable across CEX-guided
            // waves.  Each closure first performs candidate-directed
            // combinational proof and sends only unresolved relations to one
            // shared &scorr closure.
            if ( fHaveSE )
            {
                Cec_TranCandVec_t Batch = {0};
                Vec_Int_t * vBatchStatus;
                Vec_Str_t * vBatchStage;
                int iBatch, iRootPhase = fRootExistingPhase ? 0 : 1;
                int Gain, fRootCex = 0, iRootCex = -1;
                int nRootScreenedNow = 0;
                abctime clkBatch, timeBatch, timeShare;
                // qStrictAll is grouped in MFFC order.  Retain every already
                // capped construction candidate so its relation participates
                // in the same stronger equivalence-class hypothesis.
                while ( qStrictAll.iHead < qStrictAll.nSize &&
                       (!pPars->nRootBatch || nRootScreenedNow < pPars->nRootBatch) )
                {
                    int iTarget = qStrictAll.pArray[qStrictAll.iHead].iTarget;
                    nRootScreenedNow++;
                    Prof.nRootScreened++;
                    while ( qStrictAll.iHead < qStrictAll.nSize &&
                            qStrictAll.pArray[qStrictAll.iHead].iTarget == iTarget )
                    {
                        int iCandPos = qStrictAll.iHead++;
                        Cand = qStrictAll.pArray[iCandPos];
                        if ( Cec_TranCandVecContains(&vTried, &Cand) )
                        {
                            Prof.nQueueTriedSkipped++;
                            continue;
                        }
                        Gain = Cand.Gain;
                        if ( Gain < 0 )
                        {
                            clkCand = pPars->fProfile ? Abc_Clock() : 0;
                            Gain = Cec_TranRootCandidateGainEval( p, &Cand,
                                &Prof );
                            qStrictAll.pArray[iCandPos].Gain = Gain;
                            Prof.nRootGainEvals++;
                            if ( pPars->fProfile )
                            {
                                timeCand = Abc_Clock() - clkCand;
                                Prof.timeDirectKind[Cand.nKind] += timeCand;
                                Prof.timeDirectLane[1] += timeCand;
                            }
                        }
                        if ( Gain < pPars->nGainMin )
                        {
                            nGainRejected++;
                            Cec_TranCandVecPush( &vTried, Cand );
                            continue;
                        }
                        nPositive++;
                        Cand.Gain = Gain;
                        if ( Cand.Gain < pPars->nRootGainMin &&
                             Cand.nMffc < pPars->nHardMffc )
                        {
                            Cec_TranCandVecPush( &vTried, Cand );
                            Prof.nRootValueFiltered++;
                            continue;
                        }
                        Cec_TranCandVecPush( &Batch, Cand );
                    }
                }
                if ( Batch.nSize == 0 )
                {
                    Cec_TranCandVecStop( &Batch );
                    break;
                }
                qsort( Batch.pArray, Batch.nSize, sizeof(Cec_TranCand_t),
                    Cec_TranCandPriorityCompare );
                for ( iBatch = 0; iBatch < Batch.nSize; iBatch++ )
                {
                    Cand = Batch.pArray[iBatch];
                    Cec_TranCandVecPush( &vTried, Cand );
                    nTried++;
                    nStrictProofs++;
                    if ( Cand.nKind == CEC_TRAN_CAND_CONST )
                        nConstantProofs++;
                    else if ( Cand.nKind == CEC_TRAN_CAND_EXIST )
                        nExistingProofs++;
                    else
                        nConstructedProofs++;
                    if ( pPars->fVerbose )
                        Abc_Print( 1, "  batched direct proof %d: n%d <- dependency[%d gates]  gain=%d\n",
                            nTried, Cand.iTarget, Cand.nGates, Cand.Gain );
                }

                // Root closure has no low-budget lane: it exists only for the
                // valuable misses selected by -O/-m.  The batch uses -C per
                // internal scorr obligation and deliberately has no total cap,
                // so one hard relation cannot invalidate already-proved roots.
                // Window/output candidates keep the independent X/Y vs C/Z
                // deterministic tiering below.
                Prof.nRootClosures++;
                Prof.nRootBatchMax = Abc_MaxInt( Prof.nRootBatchMax, Batch.nSize );
                Prof.nRootPhaseCalls[iRootPhase]++;
                Prof.nRootPhaseCands[iRootPhase] += Batch.nSize;
                clkBatch = Abc_Clock();
                vBatchStatus = Cec_TranProveRootBatch( p,
                    Batch.pArray, Batch.nSize, pPars, &Prof, &vBatchStage );
                timeBatch = Abc_Clock() - clkBatch;
                timeShare = timeBatch / Batch.nSize;
                if ( pPars->fProfile )
                {
                    for ( iBatch = 0; iBatch < Batch.nSize; iBatch++ )
                    {
                        Prof.timeDirectKind[Batch.pArray[iBatch].nKind] += timeShare;
                        Prof.timeDirectLane[1] += timeShare;
                    }
                }
                for ( iBatch = 0; iBatch < Batch.nSize; iBatch++ )
                    if ( Vec_IntEntry(vBatchStatus, iBatch) )
                    {
                        Batch.pArray[iBatch].nProofStage =
                            (unsigned)Vec_StrEntry( vBatchStage, iBatch );
                        Prof.nRootPhaseProved[iRootPhase]++;
                        pRootSolved[Batch.pArray[iBatch].iTarget] = 1;
                        if ( !Cec_TranCandVecContains(&qRootProved,
                                Batch.pArray + iBatch) )
                            Cec_TranCandVecPush( &qRootProved,
                                Batch.pArray[iBatch] );
                    }

                // Only a reset-reachable witness may guide another construct
                // wave.  There is no point harvesting after the configured
                // final wave, or for roots already solved by another class
                // member in this closure.
                if ( nRound + 1 < pPars->nRootWaves )
                    fRootCex = Cec_TranHarvestRootWaveCex( p,
                        Batch.pArray, vBatchStatus, Batch.nSize, pRootSolved,
                        pPars, pDb, &Prof, &iRootCex );
                for ( iBatch = 0; iBatch < Batch.nSize; iBatch++ )
                {
                    if ( Vec_IntEntry(vBatchStatus, iBatch) )
                    {
                        Prof.nProofUnsat++;
                        Prof.timeProofUnsat += timeShare;
                    }
                    else if ( iBatch == iRootCex )
                    {
                        Prof.nProofSat++;
                        Prof.timeProofSat += timeShare;
                        nUnproved++;
                    }
                    else
                    {
                        Prof.nProofUnknown++;
                        Prof.timeProofUnknown += timeShare;
                        nUnproved++;
                        Prof.nUnknownFirst++;
                        Prof.timeUnknownFirst += timeShare;
                    }
                }
                if ( fRootCex )
                {
                    Cec_TranPatDbSealPending( pDb );
                    Prof.nCegisRestarts++;
                    Prof.nCexSigRefreshes++;
                    fCegisRestart = 1;
                }
                Vec_IntFree( vBatchStatus );
                Vec_StrFree( vBatchStage );
                Cec_TranCandVecStop( &Batch );
                break;
            }

            if ( pPars->nProofScope == CEC_TRAN_PROOF_ROOT )
                break;
            assert( fHaveCE || fHaveCC );
            // Both tails belong to the same lazily generated root and are
            // local-structural-gain sorted.  Select the better head across kinds.
            if ( fHaveCE && fHaveCC )
                pQueue = qContextExist.pArray[qContextExist.iHead].Gain >=
                         qContextConstr.pArray[qContextConstr.iHead].Gain ?
                         &qContextExist : &qContextConstr;
            else
                pQueue = fHaveCE ? &qContextExist : &qContextConstr;
            fFound = Cec_TranCandVecPeek( pQueue, &Cand, &vTried,
                &Prof.nQueueTriedSkipped, pUnknown, pPars,
                &nCooldownSkipped );
            assert( fFound );
            if ( !fFound )
                break;
            Cec_TranCandVecDrop( pQueue );
            if ( pPars->fVerbose )
                Abc_Print( 1, "  scheduler: lane=%s-%s root=%d mffc=%d.\n",
                    Cand.fStrict ? "strict" : "context",
                    Cand.nKind == CEC_TRAN_CAND_CONSTR ? "constructed" :
                    Cand.nKind == CEC_TRAN_CAND_EXIST ? "existing" : "constant",
                    Cand.iTarget, Cand.nMffc );
            // Alternatives of this root are sorted by local structural gain.
            // Candidates below -G are discarded without formal budget; the
            // selected candidate's final AND+register gain is checked exactly
            // once by Cec_TranTryCommitContext.
            if ( Cand.Gain >= 0 && Cand.Gain < pPars->nGainMin )
            {
                nGainRejected++;
                Cec_TranCandVecPush( &vTried, Cand );
                continue;
            }
            nTriedOld = nTried;
            nAcceptedOld = nAccepted;
            nUnknownOld = Prof.nProofUnknown;
            nSatOld = Prof.nProofSat;
            iHist = 2 * Cand.iTarget + !Cand.fStrict;
            fWasUnknown = pUnknown[iHist] > 0;
            timeUnknownOld = Prof.timeProofUnknown;
            nAndOld = Gia_ManAndNum(p);
            nRegOld = Gia_ManRegNum(p);
            fCandCex = 0;
            clkCand = pPars->fProfile ? Abc_Clock() : 0;
            fChanged = Cec_TranTryCommitContext( &p, pPars, &Cand,
                &nTried, &nPositive, &nGainRejected, &nUnproved,
                &nAccepted, pDb, &fCandCex, &Prof,
                &vCommitMap, &pCommitAffected );
            if ( pPars->fProfile )
            {
                timeCand = Abc_Clock() - clkCand;
                Prof.timeDirectKind[Cand.nKind] += timeCand;
                Prof.timeDirectLane[Cand.fStrict] += timeCand;
                if ( nAccepted > nAcceptedOld )
                {
                    Prof.nDirectAndGain[Cand.nKind] += nAndOld - Gia_ManAndNum(p);
                    Prof.nDirectRegGain[Cand.nKind] += nRegOld - Gia_ManRegNum(p);
                }
            }
            Cec_TranCandVecPush( &vTried, Cand );
            if ( nTried == nTriedOld )
                continue;

            assert( !Cand.fStrict );
            nContextProofs++;
            if ( Cand.nKind == CEC_TRAN_CAND_CONST )
            {
                nConstantProofs++;
                nConstantAccepted += nAccepted - nAcceptedOld;
            }
            else if ( Cand.nKind == CEC_TRAN_CAND_EXIST )
            {
                nExistingProofs++;
                nExistingAccepted += nAccepted - nAcceptedOld;
            }
            else
            {
                nConstructedProofs++;
                nConstructedAccepted += nAccepted - nAcceptedOld;
            }
            if ( Prof.nProofUnknown > nUnknownOld )
            {
                pUnknown[iHist]++;
                if ( fWasUnknown )
                {
                    Prof.nUnknownRepeat++;
                    Prof.timeUnknownRepeat += Prof.timeProofUnknown - timeUnknownOld;
                }
                else
                {
                    Prof.nUnknownFirst++;
                    Prof.timeUnknownFirst += Prof.timeProofUnknown - timeUnknownOld;
                }
            }
            else if ( Prof.nProofSat > nSatOld || nAccepted > nAcceptedOld )
                pUnknown[iHist] = 0;

            if ( fChanged )
            {
                // No second accepted edit may consume this snapshot.  This is
                // required for output scope because internal TFO signatures
                // can change even when the affected POs remain equivalent.
                assert( vCommitMap != NULL && pCommitAffected != NULL );
                break;
            }
            // Once the batch threshold is reached, seal the CEXes as an
            // append-only signature block and rebuild simulation, scope care,
            // and dependency recipes.  Exact tried-recipe history survives the
            // restart, so a rejected function is never proved twice.
            if ( fCandCex && Cec_TranPatDbNumPending(pDb) >= pPars->nCexBatch )
            {
                Cec_TranPatDbSealPending( pDb );
                Prof.nCegisRestarts++;
                Prof.nCexSigRefreshes++;
                fCegisRestart = 1;
                break;
            }
        }

        ABC_FREE( pRoots );
        ABC_FREE( pSigIndex );
        Abc_ResubPrepareManager( 0 );
        Cec_TranSimStop( pSim );
        ABC_FREE( p->pRefs );

        // A root wave never edits p.  Once no further reachable-CEX wave is
        // requested, choose the best proved representative of each target and
        // apply the whole bundle in one topological duplication.  Thus later
        // candidates in the same run never observe a partially committed
        // circuit, matching correspondence's class-reduction semantics.
        if ( pPars->nProofScope == CEC_TRAN_PROOF_ROOT &&
             !fCegisRestart && qRootProved.nSize )
        {
            Vec_Int_t * vAllProved = Vec_IntStart( qRootProved.nSize );
            Vec_Int_t * vCombProved = Vec_IntStart( qRootProved.nSize );
            Vec_Int_t * vSelected = NULL;
            int iRootCand, iSelected, nCommitted;
            int nAndAfterComb, nRegAfterComb;
            int nSelectMax = pPars->nChangesMax ?
                pPars->nChangesMax - nAccepted : -1;
            for ( iRootCand = 0; iRootCand < qRootProved.nSize; iRootCand++ )
            {
                Vec_IntWriteEntry( vAllProved, iRootCand, 1 );
                Vec_IntWriteEntry( vCombProved, iRootCand,
                    qRootProved.pArray[iRootCand].nProofStage == 1 );
            }
            nAndOld = Gia_ManAndNum( p );
            nRegOld = Gia_ManRegNum( p );
            clkCand = Abc_Clock();
            Cec_TranRootBundleCost( p, qRootProved.pArray, vCombProved,
                qRootProved.nSize, nSelectMax, &nAndAfterComb,
                &nRegAfterComb );
            Prof.timeRootStageEval += Abc_Clock() - clkCand;
            clkCand = Abc_Clock();
            nCommitted = Cec_TranCommitRootBatchBundle( &p,
                qRootProved.pArray, vAllProved, qRootProved.nSize,
                nSelectMax,
                pPars, &Prof, &vSelected );
            Prof.timeRootCommit += Abc_Clock() - clkCand;
            if ( nCommitted )
            {
                fChanged = 1;
                nAccepted += nCommitted;
                Vec_IntForEachEntry( vSelected, iSelected, iRootCand )
                {
                    if ( qRootProved.pArray[iSelected].nProofStage == 1 )
                        Prof.nCombSelected++;
                    else
                        Prof.nSeqSelected++;
                    if ( qRootProved.pArray[iSelected].nKind ==
                         CEC_TRAN_CAND_CONST )
                        nConstantAccepted++;
                    else if ( qRootProved.pArray[iSelected].nKind ==
                              CEC_TRAN_CAND_EXIST )
                        nExistingAccepted++;
                    else
                        nConstructedAccepted++;
                }
                Prof.nRootBundleAndGain += nAndOld - Gia_ManAndNum(p);
                Prof.nRootBundleRegGain += nRegOld - Gia_ManRegNum(p);
                Prof.nRootBundleCommits += nCommitted;
                Prof.nStageAndBefore = nAndOld;
                Prof.nStageAndAfterComb = nAndAfterComb;
                Prof.nStageAndAfterSeq = Gia_ManAndNum( p );
                Prof.nStageRegBefore = nRegOld;
                Prof.nStageRegAfterComb = nRegAfterComb;
                Prof.nStageRegAfterSeq = Gia_ManRegNum( p );
            }
            Vec_IntFreeP( &vSelected );
            Vec_IntFree( vCombProved );
            Vec_IntFree( vAllProved );
        }
        nRound++;
        if ( fChanged && pPars->nProofScope != CEC_TRAN_PROOF_ROOT )
        {
            int * pUnknownNew, nUnknownRetained, nUnknownBefore = 0;
            int nTriedBefore = vTried.nSize, nTriedRetained, iUnknown;
            // A committed network needs a new simulation snapshot anyway, so
            // include a partial pending CEX batch in that refresh.
            if ( Cec_TranPatDbNumPending(pDb) )
                Cec_TranPatDbSealPending( pDb );
            // Reuse exact candidate and root-cooldown history only outside the
            // committed replacement's sequential TFO.  Records inside that
            // TFO are invalidated because their functions may have changed.
            nTriedRetained = Cec_TranCandVecRemap( &vTried, vCommitMap,
                pCommitAffected, p );
            Prof.nHistoryTriedRemapped += nTriedRetained;
            Prof.nHistoryTriedInvalidated += nTriedBefore - nTriedRetained;
            for ( iUnknown = 0; iUnknown < 2 * Vec_IntSize(vCommitMap); iUnknown++ )
                nUnknownBefore += pUnknown[iUnknown] != 0;
            pUnknownNew = Cec_TranRootHistoryRemap( pUnknown, vCommitMap,
                pCommitAffected, p, &nUnknownRetained );
            Prof.nHistoryUnknownRemapped += nUnknownRetained;
            Prof.nHistoryUnknownInvalidated += nUnknownBefore - nUnknownRetained;
            ABC_FREE( pUnknown );
            pUnknown = pUnknownNew;
            Vec_IntFree( vCommitMap );
            ABC_FREE( pCommitAffected );
        }
    }
    while ( (pPars->nProofScope == CEC_TRAN_PROOF_ROOT ?
             (fCegisRestart && nRound < pPars->nRootWaves) :
             (fChanged || fCegisRestart)) &&
        (!pPars->nChangesMax || nAccepted < pPars->nChangesMax) &&
        Gia_ManRegNum(p) > 0 );

    Prof.timeTotal = Abc_Clock() - clk;
    Prof.nCexStored = Vec_PtrSize(pDb->vCexes);
    Abc_Print( 1, "Sequential direct resubstitution: rounds=%d roots=%d proofs=%d strict-proofs=%d context-proofs=%d constants=%lld existing=%lld constructed=%lld constant-proofs=%d existing-proofs=%d constructed-proofs=%d constant-accepted=%d existing-accepted=%d constructed-accepted=%d root-fast-proofs=%d root-fast-accepted=%d scope-fallbacks=%d cooldown-skipped=%d burst-skipped=%d sig-checks=%lld sig-rejected=%lld sig-matched=%lld sig-duplicates=0 gain-positive=%d gain-rejected=%d unsat=%d sat=%d unknown=%d unproved=%d accepted=%d, AND=%d -> %d, time=%.2f sec.\n",
        nRound, nRoots, nTried, nStrictProofs, nContextProofs,
        Disc.nConstants, Disc.nExisting, Disc.nConstructed,
        nConstantProofs, nExistingProofs, nConstructedProofs,
        nConstantAccepted, nExistingAccepted, nConstructedAccepted,
        Prof.nRootFastCalls, Prof.nRootFastProved, Prof.nScopeFallbacks,
        nCooldownSkipped, nBurstSkipped, Disc.nSigChecks,
        Disc.nSigRejected, Disc.nSigMatched, nPositive, nGainRejected,
        Prof.nProofUnsat, Prof.nProofSat, Prof.nProofUnknown, nUnproved,
        nAccepted, Gia_ManAndNum(pGia), Gia_ManAndNum(p),
        Cec_TranTimeSec(Prof.timeTotal) );
    if ( pPars->fProfile )
    {
        Abc_Print( 1, "Sequential direct root-match profile: strict-roots=%d matches=%lld avg=%.2f max=%d hist=0:%d,1:%d,2-4:%d,5-16:%d,17+:%d context-roots=%d matches=%lld avg=%.2f max=%d hist=0:%d,1:%d,2-4:%d,5-16:%d,17+:%d.\n",
            Disc.nRootsProfiled[0], Disc.nRootMatches[0],
            Disc.nRootsProfiled[0] ? 1.0 * Disc.nRootMatches[0] / Disc.nRootsProfiled[0] : 0.0,
            Disc.nRootMatchMax[0], Disc.nRootMatchHist[0][0],
            Disc.nRootMatchHist[0][1], Disc.nRootMatchHist[0][2],
            Disc.nRootMatchHist[0][3], Disc.nRootMatchHist[0][4],
            Disc.nRootsProfiled[1], Disc.nRootMatches[1],
            Disc.nRootsProfiled[1] ? 1.0 * Disc.nRootMatches[1] / Disc.nRootsProfiled[1] : 0.0,
            Disc.nRootMatchMax[1], Disc.nRootMatchHist[1][0],
            Disc.nRootMatchHist[1][1], Disc.nRootMatchHist[1][2],
            Disc.nRootMatchHist[1][3], Disc.nRootMatchHist[1][4] );
        Abc_Print( 1, "Sequential direct proof profile: random-lanes=%d signature-samples=%d window=%d proved=%d expanded=%d final=%d shadow=%d root-snapshots=%d root-closures=%d root-batches=%d root-batch-candidates=%d root-batch-proved=%d root-batch-max=%d root-rescue=%d/%d cex=%d/%d cex-refresh=%d cex-filtered=%d cex-blocks=%d commit-refresh=%d history-tried-remapped=%d history-tried-invalidated=%d history-unknown-remapped=%d history-unknown-invalidated=%d.\n",
            pPars->nSimWords * 64, pPars->nSimFrames * pPars->nSimWords * 64,
            Prof.nWindowCalls, Prof.nWindowProved, Prof.nWindowExpanded,
            Prof.nFinalCalls, Prof.nShadowCalls,
            Prof.nRootSnapshots, Prof.nRootClosures, Prof.nRootBatchCalls,
            Prof.nRootBatchCands,
            Prof.nRootBatchProved, Prof.nRootBatchMax,
            Prof.nRootRescueCalls, Prof.nRootRescueProved, Prof.nCexStored,
            Prof.nCegisRestarts, Prof.nCexSigRefreshes,
            Prof.nCexSigFiltered, Vec_IntSize(pDb->vBatchEnds),
            Prof.nCommitRefreshes,
            Prof.nHistoryTriedRemapped, Prof.nHistoryTriedInvalidated,
            Prof.nHistoryUnknownRemapped, Prof.nHistoryUnknownInvalidated );
        Cec_TranPrintDirectProfile( &Prof, nStrictProofs, nContextProofs,
            pPars->nCandMax,
            nConstantProofs, nExistingProofs, nConstructedProofs,
            nConstantAccepted, nExistingAccepted, nConstructedAccepted );
    }
    Cec_TranCandVecStop( &qStrictExist );
    Cec_TranCandVecStop( &qStrictConstr );
    Cec_TranCandVecStop( &qStrictAll );
    Cec_TranCandVecStop( &qRootProved );
    Cec_TranCandVecStop( &qContextExist );
    Cec_TranCandVecStop( &qContextConstr );
    Cec_TranCandVecStop( &vTried );
    ABC_FREE( pUnknown );
    ABC_FREE( pRootSolved );
    Cec_TranPatDbStop( pDb );
    return p;
}

static Gia_Man_t * Cec_ManSequentialSodcTransduction( Gia_Man_t * pGia, Cec_ParTran_t * pPars )
{
    Cec_TranProf_t Prof = {0};
    Cec_TranTargetProf_t Target, Snap, * pTop;
    Gia_Man_t * p;
    Gia_Obj_t * pObj, * pDiv;
    Cec_TranSim_t * pSim;
    Cec_TranPatDb_t * pDb;
    Cec_TranSpec_t * pSpec;
    word * pCare;
    Vec_Int_t * vMatches, * vBases, * vConstr, * vSuper;
    Vec_Wrd_t * vConstrSigs;
    word * pConstrSig;
    int i, f, f2, d, e, j, iDiv0, iDiv1, fDivCompl, iEntry;
    int nExisting = 0, nExistingMatched = 0, nExistingRetained = 0;
    int nConstructed = 0, nConstructMatched = 0, nConstructRetained = 0;
    int nPositive = 0, nGainRejected = 0;
    int nRetainUnproved = 0, nFinalUnproved = 0, nTried = 0, nAccepted = 0;
    int nSigChecks = 0, nSigRejected = 0, nSigMatched = 0, nSigDuplicate = 0;
    int nCareBits = 0, nThisCareBits, nTop = 0, nRound = 0;
    int nVictim, nVictim2, iFanin1, nBaseLimit, nConstrLimit, nVictimSets = 0;
    int fChanged, fCegisRestart;
    abctime clk = Abc_Clock(), clkPhase, clkTarget;
    assert( Gia_ManRegNum(pGia) > 0 );
    Abc_Print( 1, "Sequential transduction: AND = %d, Reg = %d, frames = %d, conf = %d.\n",
        Gia_ManAndNum(pGia), Gia_ManRegNum(pGia), pPars->nFrames, pPars->nBTLimit );
    p = Gia_ManDup( pGia );
    pDb = Cec_TranPatDbStart( p, pPars->nCexMax );
    pTop = pPars->fProfile && pPars->nProfileTop ?
        ABC_ALLOC( Cec_TranTargetProf_t, pPars->nProfileTop ) : NULL;
    do
    {
        fChanged = 0;
        fCegisRestart = 0;
        // Signatures are rebuilt after every committed transaction.  This is
        // intentionally conservative while structural edit caches do not yet
        // exist; no candidate is ever proved against a stale snapshot.
        clkPhase = Abc_Clock();
        pSim = Cec_TranSimStart( p, pPars, pDb );
        Prof.timeSim += Abc_Clock() - clkPhase;
        Prof.nSimCalls++;
        // Structural filtering is free: a topologically earlier object cannot
        // be in the target's TFO, so it cannot create a combinational cycle.
        Gia_ManForEachAnd( p, pObj, i )
        {
            if ( Gia_ObjIsXor(pObj) )
                continue;
            if ( pPars->fProfile )
            {
                memset( &Target, 0, sizeof(Target) );
                memset( &Snap, 0, sizeof(Snap) );
                clkTarget = Abc_Clock();
                Target.iRound = nRound;
                Target.iTarget = i;
                Snap.nVictimSets = nVictimSets;
                Snap.nExistingChecks = nExisting;
                Snap.nExistingMatched = nExistingMatched;
                Snap.nExistingRetained = nExistingRetained;
                Snap.nConstructChecks = nConstructed;
                Snap.nConstructMatched = nConstructMatched;
                Snap.nConstructRetained = nConstructRetained;
                Snap.nDuplicates = nSigDuplicate;
                Snap.nGainCalls = Prof.nGainCalls;
                Snap.nGainPositive = nPositive;
                Snap.nGainRejected = nGainRejected;
                Snap.nProofs = nTried;
                Snap.nRetainUnproved = nRetainUnproved;
                Snap.nFinalUnproved = nFinalUnproved;
                Snap.nAccepted = nAccepted;
                Snap.timeCare = Prof.timeCare;
                Snap.timeSearch = Prof.timeSpec + Prof.timeExisting + Prof.timeConstruct;
                Snap.timeGain = Prof.timeGain;
                Snap.timeWindow = Prof.timeWindowMiter + Prof.timeWindowCorr;
                Snap.timeCexBmc = Prof.timeCexBmc;
                Snap.timeProof = Prof.timeRetainMiter + Prof.timeRetainCorr +
                    Prof.timeFinalMiter + Prof.timeFinalCorr + Prof.timeShadow;
                Snap.nWindowCalls = Prof.nWindowCalls;
                Snap.nWindowProved = Prof.nWindowProved;
                Snap.nWindowExpanded = Prof.nWindowExpanded;
                Snap.nCexBmcCalls = Prof.nCexBmcCalls;
                Snap.nCexBmcSat = Prof.nCexBmcSat;
            }
            vSuper = Cec_TranCollectSuper( p, i );
            if ( pPars->fProfile )
                Target.nSuperLeaves = Vec_IntSize(vSuper);
            clkPhase = Abc_Clock();
            pCare = Cec_TranSimComputeCare( pSim, i );
            Prof.timeCare += Abc_Clock() - clkPhase;
            Prof.nCareCalls++;
            nThisCareBits = Cec_TranCountOnes( pCare, pSim->nSlots );
            nCareBits += nThisCareBits;
            if ( pPars->fProfile )
                Target.nCareBits = nThisCareBits;
            for ( f = 0; f < Vec_IntSize(vSuper) && !fChanged && !fCegisRestart; f++ )
            {
                // A transaction may replace either one leaf or a pair of
                // leaves in the same positive AND supergate.  The latter is
                // the smallest multi-victim extension: h is required to
                // equal the conjunction of the removed leaves wherever the
                // remaining product is sequentially observable.
                for ( f2 = f; f2 < Vec_IntSize(vSuper) && !fChanged && !fCegisRestart; f2++ )
                {
                if ( pPars->nVictimsMax == 1 && f2 != f )
                    break;
                if ( pPars->nVictimsMax == 2 && f2 == f )
                    continue;
                iFanin1 = f2 == f ? -1 : f2;
                nVictim = Vec_IntEntry( vSuper, f );
                nVictim2 = iFanin1 < 0 ? -1 : Vec_IntEntry( vSuper, iFanin1 );
                nVictimSets++;
                // Compute the specification once.  Every existing divisor
                // and every one-gate construction below shares these masks.
                clkPhase = Abc_Clock();
                pSpec = Cec_TranSpecStart( pSim, pCare, i, f, iFanin1 );
                Prof.timeSpec += Abc_Clock() - clkPhase;
                Prof.nSpecCalls++;
                vMatches = Vec_IntAlloc( pPars->nDivsMax );
                // Test the full topologically-safe pool with bit-parallel
                // Must1/Must0 masks, but retain only the nearest matching
                // literals for expensive formal proof attempts.
                clkPhase = Abc_Clock();
                for ( d = i - 1; d > 0; d-- )
                {
                    pDiv = Gia_ManObj( p, d );
                    if ( !Gia_ObjIsCand(pDiv) )
                        continue;
                    for ( fDivCompl = 0; fDivCompl < 2; fDivCompl++ )
                    {
                        iDiv0 = Abc_Var2Lit( d, fDivCompl );
                        if ( iDiv0 == nVictim || iDiv0 == nVictim2 )
                            continue;
                        nExisting++;
                        nSigChecks++;
                        if ( !Cec_TranSpecMatches(pSpec, iDiv0, -1, 0) )
                        {
                            nSigRejected++;
                            continue;
                        }
                        nSigMatched++;
                        nExistingMatched++;
                        if ( pPars->nDivsMax == 0 || Vec_IntSize(vMatches) < pPars->nDivsMax )
                            Vec_IntPush( vMatches, iDiv0 );
                    }
                }
                Prof.timeExisting += Abc_Clock() - clkPhase;
                nExistingRetained += Vec_IntSize(vMatches);
                Vec_IntForEachEntry( vMatches, iDiv0, j )
                {
                    if ( nTried >= pPars->nCandMax )
                        break;
                    fChanged = Cec_TranTryCommit( &p, pPars, i, f, iFanin1, iDiv0, -1, 0,
                        &nTried, &nPositive, &nGainRejected, &nRetainUnproved,
                        &nFinalUnproved, &nAccepted, pDb, &fCegisRestart, &Prof );
                    if ( fChanged || fCegisRestart )
                        break;
                }
                Vec_IntFree( vMatches );
                if ( !pPars->fUseConstr || fChanged || fCegisRestart || pPars->nConstrMax == 0 )
                {
                    Cec_TranSpecStop( pSpec );
                    continue;
                }

                // A bounded base pool makes the O(D^2 W) construction pass
                // predictable.  Its literals include both phases, so AND and
                // complemented-AND cover AND/OR/AND-NOT forms.
                clkPhase = Abc_Clock();
                nBaseLimit = pPars->nConstrBaseMax;
                nConstrLimit = pPars->nConstrMax;
                vBases = Vec_IntAlloc( nBaseLimit ? nBaseLimit : 100 );
                for ( d = i - 1; d > 0 && (nBaseLimit == 0 || Vec_IntSize(vBases) < nBaseLimit); d-- )
                {
                    pDiv = Gia_ManObj( p, d );
                    if ( !Gia_ObjIsCand(pDiv) )
                        continue;
                    Vec_IntPush( vBases, Abc_Var2Lit(d, 0) );
                    if ( nBaseLimit == 0 || Vec_IntSize(vBases) < nBaseLimit )
                        Vec_IntPush( vBases, Abc_Var2Lit(d, 1) );
                }
                vConstr = Vec_IntAlloc( 3 * nConstrLimit );
                vConstrSigs = Vec_WrdAlloc( nConstrLimit * pSim->nSlots );
                pConstrSig = ABC_ALLOC( word, pSim->nSlots );
                Vec_IntForEachEntry( vBases, iDiv0, d )
                {
                    Vec_IntForEachEntryStart( vBases, iDiv1, e, d + 1 )
                    {
                        for ( fDivCompl = 0; fDivCompl < 2; fDivCompl++ )
                        {
                            nConstructed++;
                            nSigChecks++;
                            if ( !Cec_TranSpecMatches(pSpec, iDiv0, iDiv1, fDivCompl) )
                            {
                                nSigRejected++;
                                continue;
                            }
                            nSigMatched++;
                            nConstructMatched++;
                            if ( Vec_IntSize(vConstr) < 3 * nConstrLimit )
                            {
                                Cec_TranSpecCompute( pSpec, iDiv0, iDiv1, fDivCompl, pConstrSig );
                                if ( !Cec_TranSigIsNew(vConstrSigs, pConstrSig, pSim->nSlots) )
                                {
                                    nSigDuplicate++;
                                    continue;
                                }
                                Vec_IntPush( vConstr, iDiv0 );
                                Vec_IntPush( vConstr, iDiv1 );
                                Vec_IntPush( vConstr, fDivCompl );
                            }
                        }
                    }
                }
                Prof.timeConstruct += Abc_Clock() - clkPhase;
                nConstructRetained += Vec_IntSize(vConstr) / 3;
                for ( j = 0; j < Vec_IntSize(vConstr) && !fChanged && !fCegisRestart && nTried < pPars->nCandMax; j += 3 )
                {
                    iDiv0 = Vec_IntEntry( vConstr, j );
                    iDiv1 = Vec_IntEntry( vConstr, j + 1 );
                    iEntry = Vec_IntEntry( vConstr, j + 2 );
                    fChanged = Cec_TranTryCommit( &p, pPars, i, f, iFanin1, iDiv0, iDiv1, iEntry,
                        &nTried, &nPositive, &nGainRejected, &nRetainUnproved,
                        &nFinalUnproved, &nAccepted, pDb, &fCegisRestart, &Prof );
                }
                Vec_IntFree( vConstr );
                Vec_WrdFree( vConstrSigs );
                ABC_FREE( pConstrSig );
                Vec_IntFree( vBases );
                Cec_TranSpecStop( pSpec );
                }
            }
            ABC_FREE( pCare );
            Vec_IntFree( vSuper );
            if ( pPars->fProfile )
            {
                Target.timeTotal = Abc_Clock() - clkTarget;
                Target.timeCare = Prof.timeCare - Snap.timeCare;
                Target.timeSearch = Prof.timeSpec + Prof.timeExisting + Prof.timeConstruct - Snap.timeSearch;
                Target.timeGain = Prof.timeGain - Snap.timeGain;
                Target.timeWindow = Prof.timeWindowMiter + Prof.timeWindowCorr - Snap.timeWindow;
                Target.timeCexBmc = Prof.timeCexBmc - Snap.timeCexBmc;
                Target.timeProof = Prof.timeRetainMiter + Prof.timeRetainCorr +
                    Prof.timeFinalMiter + Prof.timeFinalCorr + Prof.timeShadow - Snap.timeProof;
                Target.nVictimSets = nVictimSets - Snap.nVictimSets;
                Target.nExistingChecks = nExisting - Snap.nExistingChecks;
                Target.nExistingMatched = nExistingMatched - Snap.nExistingMatched;
                Target.nExistingRetained = nExistingRetained - Snap.nExistingRetained;
                Target.nConstructChecks = nConstructed - Snap.nConstructChecks;
                Target.nConstructMatched = nConstructMatched - Snap.nConstructMatched;
                Target.nConstructRetained = nConstructRetained - Snap.nConstructRetained;
                Target.nDuplicates = nSigDuplicate - Snap.nDuplicates;
                Target.nGainCalls = Prof.nGainCalls - Snap.nGainCalls;
                Target.nGainPositive = nPositive - Snap.nGainPositive;
                Target.nGainRejected = nGainRejected - Snap.nGainRejected;
                Target.nProofs = nTried - Snap.nProofs;
                Target.nRetainUnproved = nRetainUnproved - Snap.nRetainUnproved;
                Target.nFinalUnproved = nFinalUnproved - Snap.nFinalUnproved;
                Target.nAccepted = nAccepted - Snap.nAccepted;
                Target.nWindowCalls = Prof.nWindowCalls - Snap.nWindowCalls;
                Target.nWindowProved = Prof.nWindowProved - Snap.nWindowProved;
                Target.nWindowExpanded = Prof.nWindowExpanded - Snap.nWindowExpanded;
                Target.nCexBmcCalls = Prof.nCexBmcCalls - Snap.nCexBmcCalls;
                Target.nCexBmcSat = Prof.nCexBmcSat - Snap.nCexBmcSat;
                Cec_TranTargetProfAdd( &Prof, pTop, &nTop, pPars->nProfileTop, &Target );
            }
            if ( fChanged || fCegisRestart || nTried >= pPars->nCandMax || nAccepted >= pPars->nChangesMax )
                break;
        }
        Cec_TranSimStop( pSim );
        if ( fCegisRestart )
            Prof.nCegisRestarts++;
        nRound++;
    }
    while ( (fChanged || fCegisRestart) && nTried < pPars->nCandMax && nAccepted < pPars->nChangesMax );
    Prof.timeTotal = Abc_Clock() - clk;
    Abc_Print( 1, "Sequential transduction: victim-sets=%d proofs=%d existing=%d constructed=%d care-bits=%d sig-checks=%d sig-rejected=%d sig-matched=%d sig-duplicates=%d gain-positive=%d gain-rejected=%d retain-unproved=%d final-unproved=%d accepted=%d, AND=%d -> %d, time=%.2f sec.\n",
        nVictimSets, nTried, nExisting, nConstructed, nCareBits, nSigChecks, nSigRejected, nSigMatched, nSigDuplicate,
        nPositive, nGainRejected, nRetainUnproved, nFinalUnproved, nAccepted,
        Gia_ManAndNum(pGia), Gia_ManAndNum(p),
        Cec_TranTimeSec(Prof.timeTotal) );
    Prof.nCexStored = Vec_PtrSize(pDb->vCexes);
    if ( pPars->fProfile )
        Cec_TranPrintProfile( &Prof, pTop, nTop );
    ABC_FREE( pTop );
    Cec_TranPatDbStop( pDb );
    return p;
}

Gia_Man_t * Cec_ManSequentialTransduction( Gia_Man_t * pGia, Cec_ParTran_t * pPars )
{
    // This branch exposes Direct root replacement with an explicit proof
    // scope.  Keep the legacy leaf-SODC implementation above isolated until
    // it is split into a separate command or branch.
    assert( pPars->fUseDirect && !pPars->fUseSodc );
    return Cec_ManSequentialDirectResubstitution( pGia, pPars );
}

ABC_NAMESPACE_IMPL_END
