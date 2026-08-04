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
#include "misc/util/utilTruth.h"
#include "sat/bmc/bmc.h"

ABC_NAMESPACE_IMPL_START

enum
{
    CEC_TRAN_CAND_CONST = 0,
    CEC_TRAN_CAND_EXIST = 1,
    CEC_TRAN_CAND_CONSTR = 2,
    CEC_TRAN_ROOT_ALT_PROFILE_MAX = CEC_TRAN_RESUB_CHOICES_MAX + 3
};

extern void Abc_ResubPrepareManager( int nWords );
extern int Abc_ResubComputeFunctions( void ** ppDivs, int nDivs,
    int nWords, int nLimit, int nDivsMax, int nChoices, int iChoiceStart,
    int fUseZero, int fUseXor, int fDebug, int fVerbose,
    Vec_Wec_t * vResults, int * pnAttempts,
    abctime * pTimeInit, abctime * pTimeSearch,
    abctime * pTimeAttempts, int * pAttemptUnique );

void Cec_ManTranSetDefaultParams( Cec_ParTran_t * p )
{
    memset( p, 0, sizeof(Cec_ParTran_t) );
    p->nFrames     = 1;
    p->nBTLimit    = 1000;
    p->nStepsMax   = -1;
    p->nCandMax    = 0;
    p->nDivsMax    = 16;
    p->nConstrMax  = 8;
    p->nConstrBaseMax = 16;
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
    p->nRootWaves  = 1;
    p->nRootConstrTop = 1;
    // CBS is a fast all-state certificate lane, not the main sequential
    // oracle.  Keep its per-cube budget separate and intentionally much lower
    // than the scorr budget in nBTLimit.
    p->nCombBTLimit = 64;
    p->nFreeWords  = 2;
    p->nFreeCexMax = 64;
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
    // Zero-gate dependency recipes overlap heavily with constants and
    // constructed recipes in root scope.  Keep this lane opt-in while the
    // independent global-existing lookup remains controlled by -l.
    p->fUseResubZero = 0;
    p->fUseConstr  = 1;
    p->fUseCbsMultiLit = 1;
    // Prove only the best retained candidate per root in one shared closure.
    // This is the default scheduling policy; command-line -r toggles back to
    // the all-alternatives A/B mode.
    p->fRootProgressive = 1;
    // Keep candidate discovery, combinational proof, and sequential proof on
    // one immutable snapshot, then commit all winners together.  Command-line
    // -s retains the old commit-and-rebuild split path as an A/B mode.
    p->fRootSplitStages = 0;
    p->fUseFreeSim = 1;
    p->nRootStage = 0;
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
    abctime timeFreeBuild;
    abctime timeFreeCheck;
    abctime timeFreeCexSim;
    abctime timeRootDivPool;
    abctime timeRootDepSynthesis;
    abctime timeRootDepInit;
    abctime timeRootDepSearch;
    abctime timeRootPairEnum;
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
    abctime timeRootDepAttempt[2 * CEC_TRAN_RESUB_CHOICES_MAX];
    abctime timeRootKindContribution;
    Cec_ProfCor_t Corr;
    long long nDirectAndGain[3];
    long long nDirectRegGain[3];
    long long nRootBundleAndGain;
    long long nRootBundleRegGain;
    long long nRootKindSubsetAndGain[8];
    long long nRootKindSubsetRegGain[8];
    // Exact stage-by-kind contribution.  Stage 0 is the arbitrary-state
    // combinational certificate lane; stage 1 is the additional reduction
    // enabled only by sequential correspondence.  Each eight-entry table is
    // the characteristic function of the three candidate kinds and is used
    // to report exact Shapley gain despite cleanup/sharing interactions.
    long long nStageKindSubsetAndGain[2][8];
    long long nStageKindSubsetRegGain[2][8];
    long long nStageConstructProvedGates[2];
    long long nStageConstructSelectedGates[2];
    long long nRootRank1AndGain;
    long long nRootRank1RegGain;
    long long nRootWave1AndGain;
    long long nRootWave1RegGain;
    long long nRootBundlePortfolioAdvantage;
    long long nRootExistingGlobalLeaveoutAndGain;
    long long nRootExistingResubLeaveoutAndGain;
    long long nCombConfUsed;
    long long nStageAndBefore;
    long long nStageAndAfterComb;
    long long nStageAndAfterSeq;
    long long nStageRegBefore;
    long long nStageRegAfterComb;
    long long nStageRegAfterSeq;
    int       nRootBundleCommits;
    int       nRootBundlePrimaryWins;
    int       nRootBundleGainWins;
    int       nRootBundlePortfolioTies;
    int       nStageKindProved[2][3];
    int       nStageKindSelected[2][3];
    int       nStageConstructProvedMaxGates[2];
    int       nStageConstructSelectedMaxGates[2];
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
    int     nCombQueryCalls;    // ordinary CBS calls on constructed XOR queries
    int     nCombTwoCubeCands;  // generic two-implication candidates
    int     nCombAndConeCands;  // recipe AND-cone candidates split into leaf cubes
    long long nCombAndLeaves;   // flattened recipe leaves across these candidates
    long long nCombCubesSkippedUnknown;// cube calls avoided after the first UNKNOWN
    long long nCombFreePotentialGain;// local gain of candidates routed away from CBS
    int     nCombFreeBaseRejected;// candidates rejected by initial free-state words
    int     nCombFreeCexRejected;// candidates rejected by learned CBS free-state CEXes
    int     nCombFreeCexStored; // valid CBS models added to the batch signature bank
    int     nCombFreeCexInvalid;// partial CBS models that failed scalar validation
    int     nCombUnknownEarly;  // candidates stopped immediately on the first UNKNOWN cube
    int     nCombNoModelCalls;  // solve calls skipping unused model extraction
    int     nRootDivPoolCalls;   // strict-root divisor pools constructed
    long long nRootDivPoolNodes; // physical divisors retained in reservoirs
    int     nRootDivAltCalls;    // dependency calls using a non-BFS pool
    int     nRootDivAltRescues;  // roots first solved by a non-BFS pool
    int     nRootDivAltRecipes;  // recipes returned by non-BFS pools
    int     nRootDivAltSubmitted;// non-BFS recipes sent to proof
    int     nRootDivAltProved;   // non-BFS recipes formally proved
    int     nRootDivAltSelected; // non-BFS recipes committed
    int     nRootDivGlobalRecipes;   // exact matches found only by global hash
    int     nRootDivGlobalSubmitted;
    int     nRootDivGlobalProved;
    int     nRootDivGlobalSelected;
    long long nRootDivRouteNodes[4]; // TFI/boundary/local/global reservoir nodes
    int     nRootDivRouteCalls[5];   // pool calls by route (last is mixed)
    int     nRootDivRouteRecipes[5]; // returned recipes by route
    int     nRootDepCalls;       // dependency-synthesis calls
    int     nRootDepFound;       // dependency-synthesis calls returning a recipe
    int     nRootDepAttempts;    // bounded choice-ranked searches
    int     nRootDepRecipes;     // unique recipes returned by these searches
    int     nRootDepAttemptCalls[2 * CEC_TRAN_RESUB_CHOICES_MAX];
    int     nRootDepAttemptUnique[2 * CEC_TRAN_RESUB_CHOICES_MAX];
    int     nRootExistingGlobalProofs;
    int     nRootExistingResubProofs;
    int     nRootExistingGlobalSelected;
    int     nRootExistingResubSelected;
    int     nRootDepYield[CEC_TRAN_RESUB_CHOICES_MAX + 1];
    int     nRootResubGenerated[CEC_TRAN_RESUB_CHOICES_MAX];
    int     nRootResubSubmitted[CEC_TRAN_RESUB_CHOICES_MAX];
    int     nRootResubCombProved[CEC_TRAN_RESUB_CHOICES_MAX];
    int     nRootResubSeqProved[CEC_TRAN_RESUB_CHOICES_MAX];
    int     nRootResubSelected[CEC_TRAN_RESUB_CHOICES_MAX];
    int     nRootLayerSubmitted[CEC_TRAN_ROOT_ALT_PROFILE_MAX];
    int     nRootLayerProved[CEC_TRAN_ROOT_ALT_PROFILE_MAX];
    int     nRootLayerSelected[CEC_TRAN_ROOT_ALT_PROFILE_MAX];
    int     nRootWaveDepCalls[64];
    int     nRootWaveRecipes[64];
    int     nRootWaveSubmitted[64];
    int     nRootWaveProved[64];
    int     nRootWaveSelected[64];
    abctime timeRootWaveConstruct[64];
    abctime timeRootWaveProof[64];
    abctime timeRootWaveTotal[64];
    long long nRootPairChecks;   // one-gate divisor-pair signature checks
    long long nRootPairMatches;  // pair checks matching the reachable signature
    int     nSeqCands;          // unresolved candidates sent to scorr
    int     nSeqSeeded;         // endpoint relations actually seeded into scorr classes
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

static double Cec_TranThreeKindShapley( long long const pGain[8], int iKind )
{
    int iBit = 1 << iKind;
    int iOther0 = 1 << ((iKind + 1) % 3);
    int iOther1 = 1 << ((iKind + 2) % 3);
    long long Numer = 2 * pGain[iBit] +
        (pGain[iBit | iOther0] - pGain[iOther0]) +
        (pGain[iBit | iOther1] - pGain[iOther1]) +
        2 * (pGain[7] - pGain[iOther0 | iOther1]);
    return Numer / 6.0;
}

static void Cec_TranPrintDirectProfile( Cec_TranProf_t * p,
    int nStrictProofs, int nContextProofs,
    int nContextProofMax,
    int nConstantProofs, int nExistingProofs, int nConstructedProofs,
    int nConstantAccepted, int nExistingAccepted, int nConstructedAccepted,
    int fUseCbsMultiLit, int fRootProgressive, int nRootWaves )
{
    Cec_ProfCor_t * pC = &p->Corr;
    int i;
    abctime Miter = p->timeWindowMiter + p->timeRetainMiter + p->timeFinalMiter;
    abctime Corr = p->timeWindowCorr + p->timeRetainCorr + p->timeFinalCorr;
    abctime Accounted = p->timeSim + p->timeCare + p->timeSpec +
        p->timeExisting + p->timeConstruct + p->timeGain + Miter + Corr +
        p->timeCombSolve + p->timeShadow + p->timeCexBmc;
    abctime Other = p->timeTotal > Accounted ? p->timeTotal - Accounted : 0;
    Abc_Print( 1, "Sequential direct phase profile: total=%.3f sec\n", Cec_TranTimeSec(p->timeTotal) );
    Abc_Print( 1, "  sim=%.3f care=%.3f spec=%.3f existing=%.3f construct=%.3f\n",
        Cec_TranTimeSec(p->timeSim), Cec_TranTimeSec(p->timeCare),
        Cec_TranTimeSec(p->timeSpec), Cec_TranTimeSec(p->timeExisting),
        Cec_TranTimeSec(p->timeConstruct) );
    Abc_Print( 1, "  gain=%.3f miter=%.3f corr=%.3f comb-solve=%.3f cex=%.3f shadow=%.3f other=%.3f\n",
        Cec_TranTimeSec(p->timeGain), Cec_TranTimeSec(Miter),
        Cec_TranTimeSec(Corr), Cec_TranTimeSec(p->timeCombSolve),
        Cec_TranTimeSec(p->timeCexBmc), Cec_TranTimeSec(p->timeShadow),
        Cec_TranTimeSec(Other) );
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
    Abc_Print( 1, "Sequential direct scorr pipeline:\n" );
    Abc_Print( 1, "  class-discover: %.3f sec\n",  Cec_TranTimeHrSec(pC->timeClasses) );
    Abc_Print( 1, "  init:           %.3f sec\n",  Cec_TranTimeHrSec(pC->timeInit) );
    Abc_Print( 1, "  bmc:            %.3f sec (srm=%.3f sat=%.3f setup=%.3f solve=%.3f resim=%.3f)\n",
        Cec_TranTimeHrSec(pC->timeBmc), Cec_TranTimeHrSec(pC->timeBmcSrm),
        Cec_TranTimeHrSec(pC->timeBmcSat), Cec_TranTimeHrSec(pC->timeBmcSetup),
        Cec_TranTimeHrSec(pC->timeBmcSolve), Cec_TranTimeHrSec(pC->timeBmcSim) );
    Abc_Print( 1, "  induction:      %.3f sec (srm=%.3f sat=%.3f setup=%.3f solve=%.3f resim=%.3f)\n",
        Cec_TranTimeHrSec(pC->timeInd), Cec_TranTimeHrSec(pC->timeIndSrm),
        Cec_TranTimeHrSec(pC->timeIndSat), Cec_TranTimeHrSec(pC->timeIndSetup),
        Cec_TranTimeHrSec(pC->timeIndSolve), Cec_TranTimeHrSec(pC->timeIndSim) );
    Abc_Print( 1, "  reduce:         %.3f sec\n",  Cec_TranTimeHrSec(pC->timeReduce) );
    Abc_Print( 1, "  calls:          %d\n",          pC->nCalls );
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
    Abc_Print( 1, "Sequential direct kind-contribution profile: AND total=%lld constant=%.3f/%lld/%lld existing=%.3f/%lld/%lld constructed=%.3f/%lld/%lld rank1=%lld extra-rank=%lld wave1=%lld later-wave=%lld; Reg total=%lld constant=%.3f/%lld/%lld existing=%.3f/%lld/%lld constructed=%.3f/%lld/%lld rank1=%lld extra-rank=%lld wave1=%lld later-wave=%lld; eval=%.6f sec.\n",
        p->nRootKindSubsetAndGain[7],
        Cec_TranThreeKindShapley(p->nRootKindSubsetAndGain, 0),
        p->nRootKindSubsetAndGain[1],
        p->nRootKindSubsetAndGain[7] - p->nRootKindSubsetAndGain[6],
        Cec_TranThreeKindShapley(p->nRootKindSubsetAndGain, 1),
        p->nRootKindSubsetAndGain[2],
        p->nRootKindSubsetAndGain[7] - p->nRootKindSubsetAndGain[5],
        Cec_TranThreeKindShapley(p->nRootKindSubsetAndGain, 2),
        p->nRootKindSubsetAndGain[4],
        p->nRootKindSubsetAndGain[7] - p->nRootKindSubsetAndGain[3],
        p->nRootRank1AndGain,
        p->nRootKindSubsetAndGain[7] - p->nRootRank1AndGain,
        p->nRootWave1AndGain,
        p->nRootKindSubsetAndGain[7] - p->nRootWave1AndGain,
        p->nRootKindSubsetRegGain[7],
        Cec_TranThreeKindShapley(p->nRootKindSubsetRegGain, 0),
        p->nRootKindSubsetRegGain[1],
        p->nRootKindSubsetRegGain[7] - p->nRootKindSubsetRegGain[6],
        Cec_TranThreeKindShapley(p->nRootKindSubsetRegGain, 1),
        p->nRootKindSubsetRegGain[2],
        p->nRootKindSubsetRegGain[7] - p->nRootKindSubsetRegGain[5],
        Cec_TranThreeKindShapley(p->nRootKindSubsetRegGain, 2),
        p->nRootKindSubsetRegGain[4],
        p->nRootKindSubsetRegGain[7] - p->nRootKindSubsetRegGain[3],
        p->nRootRank1RegGain,
        p->nRootKindSubsetRegGain[7] - p->nRootRank1RegGain,
        p->nRootWave1RegGain,
        p->nRootKindSubsetRegGain[7] - p->nRootWave1RegGain,
        Cec_TranTimeSec(p->timeRootKindContribution) );
    for ( i = 0; i < 2; i++ )
    {
        long long nAndBefore = i ? p->nStageAndAfterComb : p->nStageAndBefore;
        long long nAndAfter = i ? p->nStageAndAfterSeq : p->nStageAndAfterComb;
        long long nRegBefore = i ? p->nStageRegAfterComb : p->nStageRegBefore;
        long long nRegAfter = i ? p->nStageRegAfterSeq : p->nStageRegAfterComb;
        Abc_Print( 1, "Sequential direct stage-kind profile: stage=%s counts=selected/proved gain=proved-portfolio-shapley constant=%d/%d and-gain=%.3f reg-gain=%.3f existing=%d/%d and-gain=%.3f reg-gain=%.3f constructed=%d/%d and-gain=%.3f reg-gain=%.3f constructed-gates=%lld/%lld max-gates=%d/%d; AND=%lld -> %lld gain=%lld; Reg=%lld -> %lld gain=%lld.\n",
            i ? "seq" : "comb",
            p->nStageKindSelected[i][CEC_TRAN_CAND_CONST],
            p->nStageKindProved[i][CEC_TRAN_CAND_CONST],
            Cec_TranThreeKindShapley(p->nStageKindSubsetAndGain[i],
                CEC_TRAN_CAND_CONST),
            Cec_TranThreeKindShapley(p->nStageKindSubsetRegGain[i],
                CEC_TRAN_CAND_CONST),
            p->nStageKindSelected[i][CEC_TRAN_CAND_EXIST],
            p->nStageKindProved[i][CEC_TRAN_CAND_EXIST],
            Cec_TranThreeKindShapley(p->nStageKindSubsetAndGain[i],
                CEC_TRAN_CAND_EXIST),
            Cec_TranThreeKindShapley(p->nStageKindSubsetRegGain[i],
                CEC_TRAN_CAND_EXIST),
            p->nStageKindSelected[i][CEC_TRAN_CAND_CONSTR],
            p->nStageKindProved[i][CEC_TRAN_CAND_CONSTR],
            Cec_TranThreeKindShapley(p->nStageKindSubsetAndGain[i],
                CEC_TRAN_CAND_CONSTR),
            Cec_TranThreeKindShapley(p->nStageKindSubsetRegGain[i],
                CEC_TRAN_CAND_CONSTR),
            p->nStageConstructSelectedGates[i],
            p->nStageConstructProvedGates[i],
            p->nStageConstructSelectedMaxGates[i],
            p->nStageConstructProvedMaxGates[i],
            nAndBefore, nAndAfter, nAndBefore - nAndAfter,
            nRegBefore, nRegAfter, nRegBefore - nRegAfter );
    }
    Abc_Print( 1, "Sequential direct existing-source profile: global=%d/%d leaveout-and-gain=%lld resub=%d/%d leaveout-and-gain=%lld.\n",
        p->nRootExistingGlobalSelected, p->nRootExistingGlobalProofs,
        p->nRootExistingGlobalLeaveoutAndGain,
        p->nRootExistingResubSelected, p->nRootExistingResubProofs,
        p->nRootExistingResubLeaveoutAndGain );
    Abc_Print( 1, "Sequential direct lane profile: strict=%d attempt=%.3f context=%d attempt=%.3f sec.\n",
        nStrictProofs, Cec_TranTimeSec(p->timeDirectLane[1]),
        nContextProofs, Cec_TranTimeSec(p->timeDirectLane[0]) );
    Abc_Print( 1, "Sequential direct root-batch profile: scheduling=%s snapshots=%d batches=%d calls=%d candidates=%d proved=%d max=%d initial=%d/%d/%d refill=%d/%d/%d screened=%d local-gain-evals=%d value-filtered=%d existing-large-skipped=%d existing-kept=%d committed-roots=%d and-gain=%lld reg-gain=%lld time=%.3f avg-candidates=%.1f avg-ms=%.3f rescue=%d/%d time=%.3f.\n",
        fRootProgressive ? "bounded-per-root" : "all-at-once",
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
    Abc_Print( 1, "Sequential direct two-stage proof profile: shared-build=%.6f; comb-candidates=%d proved=%d disproved=%d unknown=%d free-base=%d free-cex-filtered=%d cubes=%d two-cube=%d and-cone=%d leaves=%lld queries=%d conflicts=%lld time=%.6f; scorr-candidates=%d seeded=%d comb-helper-seeds=%d proved=%d time=%.6f; selected=comb:%d/scorr:%d interface=%s.\n",
        Cec_TranTimeSec(p->timeCombBuild),
        p->nCombCands, p->nCombProved, p->nCombDisproved, p->nCombUnknown,
        p->nCombFreeBaseRejected, p->nCombFreeCexRejected,
        p->nCombCubeCalls, p->nCombTwoCubeCands, p->nCombAndConeCands,
        p->nCombAndLeaves,
        p->nCombQueryCalls,
        p->nCombConfUsed, Cec_TranTimeSec(p->timeCombSolve),
        p->nSeqCands, p->nSeqSeeded,
        p->nSeqSeeded - p->nSeqCands, p->nSeqProved,
        Cec_TranTimeSec(p->timeSeqSolve),
        p->nCombSelected, p->nSeqSelected,
        fUseCbsMultiLit ? "multi-lit" : "xor-query" );
    Abc_Print( 1, "Sequential direct free-state profile: build=%.6f check=%.6f cex-sim=%.6f sec; initial-filtered=%d learned-filtered=%d cex-stored=%d invalid=%d potential-gain=%lld; unknown-early=%d cube-calls-skipped=%lld no-model-calls=%d.\n",
        Cec_TranTimeSec(p->timeFreeBuild), Cec_TranTimeSec(p->timeFreeCheck),
        Cec_TranTimeSec(p->timeFreeCexSim), p->nCombFreeBaseRejected,
        p->nCombFreeCexRejected, p->nCombFreeCexStored,
        p->nCombFreeCexInvalid, p->nCombFreePotentialGain,
        p->nCombUnknownEarly, p->nCombCubesSkippedUnknown,
        p->nCombNoModelCalls );
    Abc_Print( 1, "Sequential direct construct profile: div-pool calls=%d nodes=%lld time=%.6f; dependency calls=%d found=%d attempts=%d recipes=%d time=%.6f init=%.6f search=%.6f; pair-checks=%lld matched=%lld time=%.6f sec.\n",
        p->nRootDivPoolCalls, p->nRootDivPoolNodes,
        Cec_TranTimeSec(p->timeRootDivPool),
        p->nRootDepCalls, p->nRootDepFound,
        p->nRootDepAttempts, p->nRootDepRecipes,
        Cec_TranTimeSec(p->timeRootDepSynthesis),
        Cec_TranTimeSec(p->timeRootDepInit),
        Cec_TranTimeSec(p->timeRootDepSearch),
        p->nRootPairChecks, p->nRootPairMatches,
        Cec_TranTimeSec(p->timeRootPairEnum) );
    Abc_Print( 1, "Sequential direct divisor-diversity profile: alternate-calls=%d rescued-roots=%d recipes=%d submitted=%d proved=%d selected=%d.\n",
        p->nRootDivAltCalls, p->nRootDivAltRescues,
        p->nRootDivAltRecipes, p->nRootDivAltSubmitted,
        p->nRootDivAltProved, p->nRootDivAltSelected );
    Abc_Print( 1, "Sequential direct global-divisor profile: recipes=%d submitted=%d proved=%d selected=%d.\n",
        p->nRootDivGlobalRecipes, p->nRootDivGlobalSubmitted,
        p->nRootDivGlobalProved, p->nRootDivGlobalSelected );
    Abc_Print( 1, "Sequential direct divisor-route profile: nodes=tfi:%lld/boundary:%lld/local:%lld/global:%lld; calls-recipes=legacy:%d/%d direct:%d/%d boundary:%d/%d local:%d/%d global:%d/%d.\n",
        p->nRootDivRouteNodes[0], p->nRootDivRouteNodes[1],
        p->nRootDivRouteNodes[2], p->nRootDivRouteNodes[3],
        p->nRootDivRouteCalls[0], p->nRootDivRouteRecipes[0],
        p->nRootDivRouteCalls[1], p->nRootDivRouteRecipes[1],
        p->nRootDivRouteCalls[2], p->nRootDivRouteRecipes[2],
        p->nRootDivRouteCalls[3], p->nRootDivRouteRecipes[3],
        p->nRootDivRouteCalls[4], p->nRootDivRouteRecipes[4] );
    Abc_Print( 1, "Sequential direct bundle-portfolio profile: primary-wins=%d gain-wins=%d ties=%d avoided-cost=%lld.\n",
        p->nRootBundlePrimaryWins, p->nRootBundleGainWins,
        p->nRootBundlePortfolioTies, p->nRootBundlePortfolioAdvantage );
    Abc_Print( 1, "Sequential direct dependency-attempt profile:" );
    for ( i = 0; i < 2 * CEC_TRAN_RESUB_CHOICES_MAX; i++ )
        if ( p->nRootDepAttemptCalls[i] )
            Abc_Print( 1, " a%d=%d/%d/%.6f", i + 1,
                p->nRootDepAttemptCalls[i],
                p->nRootDepAttemptUnique[i],
                Cec_TranTimeSec(p->timeRootDepAttempt[i]) );
    Abc_Print( 1, ".\n" );
    Abc_Print( 1, "Sequential direct dependency-yield profile:" );
    for ( i = 0; i <= CEC_TRAN_RESUB_CHOICES_MAX; i++ )
        Abc_Print( 1, " y%d=%d", i, p->nRootDepYield[i] );
    Abc_Print( 1, ".\n" );
    Abc_Print( 1, "Sequential direct resub-rank profile:" );
    for ( i = 0; i < CEC_TRAN_RESUB_CHOICES_MAX; i++ )
        Abc_Print( 1, " r%d=%d/%d/%d/%d/%d", i + 1,
            p->nRootResubGenerated[i], p->nRootResubSubmitted[i],
            p->nRootResubCombProved[i], p->nRootResubSeqProved[i],
            p->nRootResubSelected[i] );
    Abc_Print( 1, ".\n" );
    Abc_Print( 1, "Sequential direct root-layer profile:" );
    for ( i = 0; i < CEC_TRAN_ROOT_ALT_PROFILE_MAX; i++ )
        Abc_Print( 1, " l%d=%d/%d/%d", i + 1,
            p->nRootLayerSubmitted[i], p->nRootLayerProved[i],
            p->nRootLayerSelected[i] );
    Abc_Print( 1, ".\n" );
    Abc_Print( 1, "Sequential direct root-wave profile:" );
    for ( i = 0; i < nRootWaves; i++ )
        Abc_Print( 1, " w%d=%d/%d/%.6f/%d/%d/%d/%.6f/%.6f", i + 1,
            p->nRootWaveDepCalls[i], p->nRootWaveRecipes[i],
            Cec_TranTimeSec(p->timeRootWaveConstruct[i]),
            p->nRootWaveSubmitted[i], p->nRootWaveProved[i],
            p->nRootWaveSelected[i], Cec_TranTimeSec(p->timeRootWaveProof[i]),
            Cec_TranTimeSec(p->timeRootWaveTotal[i]) );
    Abc_Print( 1, ".\n" );
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

// Independent PI/RO simulation used only by the all-state combination lane.
// Reachable signatures intentionally start every trace from reset and cannot
// observe a mismatch confined to an unreachable register state.  Here every
// CI, including every RO, is independent.  CBS SAT models are appended as
// individual lanes and immediately screen later candidates in the same batch.
typedef struct Cec_TranFreeSim_t_ Cec_TranFreeSim_t;
struct Cec_TranFreeSim_t_
{
    Gia_Man_t * pGia;
    int         nBaseWords;
    int         nCexMax;
    int         nCexes;
    int         nWords;
    word *      pSims;          // [object ID][allocated word]
};

static inline word * Cec_TranFreeSimObj( Cec_TranFreeSim_t * p, int iObj )
{
    return p->pSims + (size_t)iObj * p->nWords;
}

static inline word Cec_TranFreeSimLit( Cec_TranFreeSim_t * p, int iLit, int w )
{
    return Cec_TranFreeSimObj(p, Abc_Lit2Var(iLit))[w] ^
        (Abc_LitIsCompl(iLit) ? ~(word)0 : 0);
}

static inline word Cec_TranFreeRandom( word * pState )
{
    word x = *pState;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    return *pState = x;
}

static Cec_TranFreeSim_t * Cec_TranFreeSimStart( Gia_Man_t * pGia,
    int nBaseWords, int nCexMax )
{
    Cec_TranFreeSim_t * p = ABC_CALLOC( Cec_TranFreeSim_t, 1 );
    Gia_Obj_t * pObj;
    word Rand = ABC_CONST(0x9e3779b97f4a7c15), v0, v1;
    int i, w, iFan0, iFan1;
    p->pGia = pGia;
    p->nBaseWords = nBaseWords;
    p->nCexMax = nCexMax;
    p->nWords = nBaseWords + (nCexMax + 63) / 64;
    p->nWords = Abc_MaxInt( p->nWords, 1 );
    p->pSims = ABC_CALLOC( word, (size_t)Gia_ManObjNum(pGia) * p->nWords );
    for ( w = 0; w < nBaseWords; w++ )
    {
        Gia_ManForEachCi( pGia, pObj, i )
            Cec_TranFreeSimObj(p, Gia_ObjId(pGia, pObj))[w] =
                Cec_TranFreeRandom( &Rand );
        Gia_ManForEachAnd( pGia, pObj, i )
        {
            iFan0 = Gia_ObjFaninId0p( pGia, pObj );
            iFan1 = Gia_ObjFaninId1p( pGia, pObj );
            v0 = Cec_TranFreeSimObj(p, iFan0)[w] ^
                (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0);
            v1 = Cec_TranFreeSimObj(p, iFan1)[w] ^
                (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0);
            Cec_TranFreeSimObj(p, i)[w] = Gia_ObjIsXor(pObj) ?
                (v0 ^ v1) : (v0 & v1);
        }
    }
    return p;
}

static void Cec_TranFreeSimStop( Cec_TranFreeSim_t * p )
{
    if ( p == NULL )
        return;
    ABC_FREE( p->pSims );
    ABC_FREE( p );
}

// Return 1 for an initial-random mismatch and 2 for a mismatch first exposed
// by an appended CBS model.  Unused lanes in the last CEX word are masked.
static int Cec_TranFreeSimMismatch( Cec_TranFreeSim_t * p, int iLit0, int iLit1 )
{
    word Diff, Mask;
    int w, nValid;
    if ( p == NULL )
        return 0;
    for ( w = 0; w < p->nBaseWords; w++ )
        if ( Cec_TranFreeSimLit(p, iLit0, w) !=
             Cec_TranFreeSimLit(p, iLit1, w) )
            return 1;
    for ( w = 0; w < (p->nCexes + 63) / 64; w++ )
    {
        nValid = Abc_MinInt( 64, p->nCexes - 64 * w );
        Mask = nValid == 64 ? ~(word)0 : ((((word)1) << nValid) - 1);
        Diff = (Cec_TranFreeSimLit(p, iLit0, p->nBaseWords + w) ^
                Cec_TranFreeSimLit(p, iLit1, p->nBaseWords + w)) & Mask;
        if ( Diff )
            return 2;
    }
    return 0;
}

// Append one CBS model as a free-state lane.  CBS reports only assigned CIs;
// unreported CIs are don't-cares and are completed with zero.  Scalar
// resimulation validates that this completion still separates the candidate
// before the lane becomes visible to later signature checks.
static int Cec_TranFreeSimAddModel( Cec_TranFreeSim_t * p, Vec_Int_t * vModel,
    int iLit0, int iLit1 )
{
    Gia_Man_t * pGia;
    Gia_Obj_t * pObj;
    word Mask, v0, v1;
    int i, iModel, iCi, iObj, iFan0, iFan1, w;
    if ( p == NULL || p->nCexes >= p->nCexMax )
        return 0;
    pGia = p->pGia;
    w = p->nBaseWords + p->nCexes / 64;
    Mask = ((word)1) << (p->nCexes & 63);
    Gia_ManForEachObj( pGia, pObj, i )
        Cec_TranFreeSimObj(p, i)[w] &= ~Mask;
    Vec_IntForEachEntry( vModel, iModel, i )
    {
        iCi = Abc_Lit2Var( iModel );
        if ( iCi < 0 || iCi >= Gia_ManCiNum(pGia) || Abc_LitIsCompl(iModel) )
            continue;
        iObj = Gia_ObjId( pGia, Gia_ManCi(pGia, iCi) );
        Cec_TranFreeSimObj(p, iObj)[w] |= Mask;
    }
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        iFan0 = Gia_ObjFaninId0p( pGia, pObj );
        iFan1 = Gia_ObjFaninId1p( pGia, pObj );
        v0 = Cec_TranFreeSimObj(p, iFan0)[w] ^
            (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0);
        v1 = Cec_TranFreeSimObj(p, iFan1)[w] ^
            (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0);
        if ( (Gia_ObjIsXor(pObj) ? (v0 ^ v1) : (v0 & v1)) & Mask )
            Cec_TranFreeSimObj(p, i)[w] |= Mask;
    }
    if ( !((Cec_TranFreeSimLit(p, iLit0, w) ^
            Cec_TranFreeSimLit(p, iLit1, w)) & Mask) )
        return 0;
    p->nCexes++;
    return 1;
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
    unsigned fStrict   : 1;
    unsigned nKind     : 2;
    unsigned nProofStage : 2;   // 0=unproved, 1=combinational, 2=sequential
    unsigned nResubRank : 4;    // 0=non-resub, otherwise raw recipe rank 1..8
    unsigned nSchedRank : 6;    // normal/rescue layer, including audit pass
    unsigned fDivRescue : 1;    // recipe came from a non-BFS failure pool
    unsigned fDivGlobal : 1;    // direct divisor required global hash fallback
    unsigned fPrimaryFrontier : 1; // candidate belongs to exact q=1 frontier
    unsigned nWave      : 6;    // zero-based root CEGAR wave
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

static int Cec_TranRecipeBuildMapped( Gia_Man_t * p, Gia_Man_t * pNew,
    Cec_TranCand_t const * pCand, int * pGates )
{
    int i, iLit0, iLit1;
    assert( pCand->nGates <= CEC_TRAN_RECIPE_NODES_MAX );
    for ( i = 0; i < pCand->nGates; i++ )
    {
        iLit0 = Cec_TranRecipeCopyCode( p, pCand->Recipe[2*i], pGates, i );
        iLit1 = Cec_TranRecipeCopyCode( p, pCand->Recipe[2*i+1], pGates, i );
        pGates[i] = Gia_ManHashAnd( pNew, iLit0, iLit1 );
    }
    return Cec_TranRecipeCopyCode( p, pCand->iOut, pGates, pCand->nGates );
}

static int Cec_TranRecipeBuild( Gia_Man_t * p, Gia_Man_t * pNew,
    Cec_TranCand_t const * pCand )
{
    int Gates[CEC_TRAN_RECIPE_NODES_MAX];
    return Cec_TranRecipeBuildMapped( p, pNew, pCand, Gates );
}

// Flatten only positive-polarity ANDs created by this recipe.  External
// divisors remain atomic even when they happen to be AND nodes in the source
// graph; recursively opening those cones would make a supposedly cheap CBS
// query proportional to the original TFI.  A complemented recipe gate is
// also atomic because De Morgan expansion would turn one cube family into an
// exponential cover.  Repeated positive recipe gates are idempotent in an
// AND cone and are traversed once.
static int Cec_TranRecipeCollectAndLeaves_rec( Cec_TranCand_t const * pCand,
    int Code, char * pSeen, int * pLeaves, int nLeaves )
{
    int iLit, iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
    {
        pLeaves[nLeaves++] = Code;
        return nLeaves;
    }
    iLit = Cec_TranRecipeGateLit( Code );
    iGate = Abc_Lit2Var( iLit );
    assert( iGate < pCand->nGates );
    if ( Abc_LitIsCompl(iLit) )
    {
        pLeaves[nLeaves++] = Code;
        return nLeaves;
    }
    if ( pSeen[iGate] )
        return nLeaves;
    pSeen[iGate] = 1;
    nLeaves = Cec_TranRecipeCollectAndLeaves_rec( pCand,
        pCand->Recipe[2*iGate], pSeen, pLeaves, nLeaves );
    return Cec_TranRecipeCollectAndLeaves_rec( pCand,
        pCand->Recipe[2*iGate+1], pSeen, pLeaves, nLeaves );
}

static int Cec_TranRecipeCollectAndLeaves( Cec_TranCand_t const * pCand,
    int * pLeaves )
{
    char Seen[CEC_TRAN_RECIPE_NODES_MAX] = {0};
    int iOutLit, iOutGate;
    if ( !Cec_TranRecipeCodeIsGate(pCand->iOut) )
        return 0;
    iOutLit = Cec_TranRecipeGateLit( pCand->iOut );
    iOutGate = Abc_Lit2Var( iOutLit );
    assert( iOutGate < pCand->nGates );
    return Cec_TranRecipeCollectAndLeaves_rec( pCand,
        Cec_TranRecipeGateCode(iOutGate, 0), Seen, pLeaves, 0 );
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
    int iDiv, word * pCare )
{
    int s;
    word h;
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        h = Cec_TranSimLit( pSim, iDiv, s );
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

static Cec_TranCand_t Cec_TranCandCreateLiteral( int iTarget, int iDiv,
    int nMffc, int nKind, int fStrict )
{
    Cec_TranCand_t Cand;
    memset( &Cand, 0, sizeof(Cand) );
    Cand.iTarget = iTarget;
    Cand.iDiv0 = iDiv;
    Cand.iDiv1 = -1;
    Cand.nMffc = nMffc;
    Cand.Gain = -1;
    Cand.nKind = nKind;
    Cand.fStrict = fStrict;
    Cand.nGates = 0;
    Cand.iOut = iDiv;
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
    Vec_Int_t ** pvPairs, Vec_Int_t ** pvQueries,
    Vec_Int_t ** pvAndLeaves, Vec_Str_t ** pvAndCounts )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vPairs = Vec_IntAlloc( 2 * nCands );
    Vec_Int_t * vQueries = Vec_IntAlloc( nCands );
    Vec_Int_t * vAndLeaves = pvAndLeaves ? Vec_IntAlloc( 2 * nCands ) : NULL;
    Vec_Str_t * vAndCounts = pvAndCounts ? Vec_StrAlloc( nCands ) : NULL;
    int nPis = Gia_ManPiNum(p);
    int * pPiProxies = nPis ? ABC_FALLOC( int, 2 * nPis ) : NULL;
    int Gates[CEC_TRAN_RECIPE_NODES_MAX];
    int Leaves[2 * CEC_TRAN_RECIPE_NODES_MAX + 1];
    int i, k, nLeaves, iLit0, iLit1, iRoot, iRep, iQuery;
    assert( nCands > 0 );
    assert( (pvAndLeaves != NULL) == (pvAndCounts != NULL) );
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
        iRep = Cec_TranRecipeBuildMapped( p, pNew, pCands + i, Gates );
        if ( vAndCounts )
        {
            nLeaves = Cec_TranRecipeCollectAndLeaves( pCands + i, Leaves );
            assert( nLeaves <= 2 * CEC_TRAN_RECIPE_NODES_MAX + 1 );
            for ( k = 0; k < nLeaves; k++ )
                Vec_IntPush( vAndLeaves, Cec_TranRecipeCopyCode(
                    p, Leaves[k], Gates, pCands[i].nGates) );
            Vec_StrPush( vAndCounts, (char)nLeaves );
        }
        // Build ordinary CBS/BMC queries from the real recipe endpoint.  A PI
        // proxy is only a correspondence-class representation; exposing its
        // unstrashed x&1 gate to CBS would make the solver visit constant
        // fanins, which are not CBS candidate variables.
        if ( fCreateQueries )
        {
            iQuery = Gia_ManHashXor( pNew, iRoot, iRep );
            Vec_IntPush( vQueries, iQuery );
        }
        iRep = Cec_TranRootClassEndpoint( pNew, iRep, nPis, pPiProxies );
        Vec_IntPushTwo( vPairs, iRoot, iRep );
    }
    Vec_IntForEachEntry( vQueries, iQuery, i )
        Gia_ManAppendCo( pNew, iQuery );
    // Endpoint COs only keep seeded class members alive through cleanup.  A
    // normal correspondence closure reads status from representatives and
    // needs no XOR property at all; the separate reachable-CEX miter requests
    // XOR queries and retains candidate endpoints through those queries.
    // Mode 2 is the ordinary-CBS A/B path: keep the class endpoints as well
    // as the XOR queries because the same graph continues into scorr.  Mode 1
    // is the standalone reachable-CEX miter and must expose only query POs.
    for ( i = 0; fCreateQueries != 1 && i < Vec_IntSize(vPairs); i++ )
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
    if ( vAndLeaves )
        Gia_ManDupRemapLiterals( vAndLeaves, pTemp );
    Gia_ManStop( pTemp );
    ABC_FREE( pPiProxies );

    *pvPairs = vPairs;
    *pvQueries = vQueries;
    if ( pvAndLeaves )
        *pvAndLeaves = vAndLeaves;
    if ( pvAndCounts )
        *pvAndCounts = vAndCounts;
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
    int nLits, int fSaveModel, Cec_TranProf_t * pProf )
{
    int Status = fSaveModel ?
        Cbs_ManSolveLits( pCbs, pLits, nLits ) :
        Cbs_ManSolveLitsNoModel( pCbs, pLits, nLits );
    pProf->nCombCubeCalls++;
    pProf->nCombNoModelCalls += !fSaveModel;
    pProf->nCombConfUsed += Cbs_ManReadConflicts( pCbs );
    return Status;
}

// Correspondence represents a PI endpoint with an unstrashed x&1 proxy.
// Remove that proof-only wrapper before passing a literal to CBS.
static int Cec_TranCombUnwrapPiProxy( Gia_Man_t * pBatch, int iLit )
{
    Gia_Obj_t * pObj = Gia_ManObj( pBatch, Abc_Lit2Var(iLit) );
    int iLit0, iLit1, iReal = -1;
    if ( !Gia_ObjIsAnd(pObj) )
        return iLit;
    iLit0 = Gia_ObjFaninLit0p( pBatch, pObj );
    iLit1 = Gia_ObjFaninLit1p( pBatch, pObj );
    if ( iLit0 == 1 )
        iReal = iLit1;
    else if ( iLit1 == 1 )
        iReal = iLit0;
    return iReal == -1 ? iLit :
        Abc_LitNotCond( iReal, Abc_LitIsCompl(iLit) );
}

// Solve one explicitly constructed XOR query through CBS's ordinary
// single-root interface.  This path exists as an A/B baseline for the direct
// multi-literal interface above; both share the same manager and conflict cap.
static int Cec_TranCombSolveQuery( Cbs_Man_t * pCbs, Gia_Man_t * pBatch,
    int iQuery, int fSaveModel, Cec_TranProf_t * pProf )
{
    int Status = fSaveModel ?
        Cbs_ManSolve( pCbs, Gia_ObjFromLit(pBatch, iQuery) ) :
        Cbs_ManSolveNoModel( pCbs, Gia_ObjFromLit(pBatch, iQuery) );
    pProf->nCombQueryCalls++;
    pProf->nCombNoModelCalls += !fSaveModel;
    pProf->nCombConfUsed += Cbs_ManReadConflicts( pCbs );
    return Status;
}

// Candidate-directed combinational equivalence.  Registers are treated as
// independent CIs, so every UNSAT result is valid in all states.  A generic
// a=h relation is two implication counterexample cubes.  If h is a recipe
// AND/NAND cone, flatten only that recipe cone into one short cube per leaf
// plus one long cube; the first SAT cube terminates the candidate immediately.
static Vec_Str_t * Cec_TranProveCombBatch( Gia_Man_t * pBatch,
    Cec_TranCand_t const * pCands, int nCands, Vec_Int_t * vPairs,
    Vec_Int_t * vQueries, Vec_Int_t * vAndLeaves, Vec_Str_t * vAndCounts,
    Cec_ParTran_t * pPars, Cec_TranProf_t * pProf )
{
    Cbs_Man_t * pCbs = Cbs_ManAlloc( pBatch );
    Cec_TranFreeSim_t * pFree = NULL;
    Vec_Str_t * vStage = Vec_StrStart( nCands );
    int Cube[2 * CEC_TRAN_RECIPE_NODES_MAX + 2];
    int i, k, iBeg = 0, iEnd = 0, nLeaves, a, h, t;
    int Status, fSat, fUnknown, fSaveModel, FreeMismatch;
    abctime clk = Abc_Clock();
    if ( pPars->fUseFreeSim && (pPars->nFreeWords || pPars->nFreeCexMax) )
    {
        abctime clkFree = Abc_Clock();
        pFree = Cec_TranFreeSimStart( pBatch, pPars->nFreeWords,
            pPars->nFreeCexMax );
        pProf->timeFreeBuild += Abc_Clock() - clkFree;
    }
    Cbs_ManSetConflictNum( pCbs, pPars->nCombBTLimit );
    assert( pPars->fUseCbsMultiLit || Vec_IntSize(vQueries) == nCands );
    pProf->nCombCands += nCands;
    for ( i = 0; i < nCands; i++ )
    {
        nLeaves = pPars->fUseCbsMultiLit ?
            (unsigned char)Vec_StrEntry(vAndCounts, i) : 0;
        iBeg = iEnd;
        iEnd += nLeaves;
        a = Vec_IntEntry( vPairs, 2*i );
        h = Vec_IntEntry( vPairs, 2*i + 1 );
        h = Cec_TranCombUnwrapPiProxy( pBatch, h );
        if ( a == h )
        {
            Vec_StrWriteEntry( vStage, i, 1 );
            pProf->nCombProved++;
            continue;
        }
        if ( pFree )
        {
            abctime clkFree = Abc_Clock();
            FreeMismatch = Cec_TranFreeSimMismatch( pFree, a, h );
            pProf->timeFreeCheck += Abc_Clock() - clkFree;
            if ( FreeMismatch )
            {
                pProf->nCombFreeBaseRejected += FreeMismatch == 1;
                pProf->nCombFreeCexRejected += FreeMismatch == 2;
                pProf->nCombFreePotentialGain += Abc_MaxInt(0, pCands[i].Gain);
                continue;
            }
        }
        // Model extraction is useful only while the batch CEGIS bank still
        // has room.  Once full, use the cheaper solve entry point for every
        // remaining cube/query instead of repeatedly collecting unused CIs.
        fSaveModel = pFree != NULL && pFree->nCexes < pFree->nCexMax;
        fSat = fUnknown = 0;
        if ( !pPars->fUseCbsMultiLit )
        {
            Status = Cec_TranCombSolveQuery( pCbs, pBatch,
                Vec_IntEntry(vQueries, i), fSaveModel, pProf );
            if ( Status == 0 )
            {
                pProf->nCombDisproved++;
                if ( fSaveModel && pFree->nCexes < pFree->nCexMax )
                {
                    abctime clkFree = Abc_Clock();
                    if ( Cec_TranFreeSimAddModel(pFree, Cbs_ReadModel(pCbs), a, h) )
                        pProf->nCombFreeCexStored++;
                    else
                        pProf->nCombFreeCexInvalid++;
                    pProf->timeFreeCexSim += Abc_Clock() - clkFree;
                }
            }
            else if ( Status < 0 )
                pProf->nCombUnknown++;
            else
            {
                Vec_StrWriteEntry( vStage, i, 1 );
                pProf->nCombProved++;
            }
            continue;
        }
        if ( nLeaves )
        {
            int iOutLit = Cec_TranRecipeGateLit( pCands[i].iOut );
            // If h = AND(leaves), a != h is covered by one short cube
            // a & !leaf[k] per leaf, plus one long cube !a & all(leaves).
            // For a complemented recipe output, replacing a by !a gives the
            // same cover.  Only recipe ANDs were flattened when the shared
            // proof graph was built; original divisor cones stay atomic.
            t = Abc_LitNotCond( a, Abc_LitIsCompl(iOutLit) );
            pProf->nCombAndConeCands++;
            pProf->nCombAndLeaves += nLeaves;
            for ( k = iBeg; k < iEnd; k++ )
            {
                Cube[0] = t;
                Cube[1] = Abc_LitNot( Vec_IntEntry(vAndLeaves, k) );
                Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                    fSaveModel, pProf );
                if ( Status == 0 ) { fSat = 1; break; }
                if ( Status < 0 )
                {
                    fUnknown = 1;
                    pProf->nCombUnknownEarly++;
                    pProf->nCombCubesSkippedUnknown += iEnd - k;
                    break;
                }
            }
            if ( !fSat && !fUnknown )
            {
                Cube[0] = Abc_LitNot( t );
                for ( k = 0; k < nLeaves; k++ )
                    Cube[k+1] = Vec_IntEntry( vAndLeaves, iBeg + k );
                Status = Cec_TranCombSolveCube( pCbs, Cube, nLeaves + 1,
                    fSaveModel, pProf );
                if ( Status == 0 )
                    fSat = 1;
                else
                {
                    fUnknown = Status < 0;
                    pProf->nCombUnknownEarly += Status < 0;
                }
            }
        }
        else
        {
            Cube[0] = a;             Cube[1] = Abc_LitNot(h);
            pProf->nCombTwoCubeCands++;
            Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                fSaveModel, pProf );
            if ( Status == 0 )
                fSat = 1;
            else
            {
                fUnknown = Status < 0;
                if ( fUnknown )
                {
                    pProf->nCombUnknownEarly++;
                    pProf->nCombCubesSkippedUnknown++;
                }
            }
            if ( !fSat && !fUnknown )
            {
                Cube[0] = Abc_LitNot(a); Cube[1] = h;
                Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                    fSaveModel, pProf );
                if ( Status == 0 )
                    fSat = 1;
                else
                {
                    fUnknown = Status < 0;
                    pProf->nCombUnknownEarly += Status < 0;
                }
            }
        }
        if ( fSat )
        {
            pProf->nCombDisproved++;
            if ( fSaveModel && pFree->nCexes < pFree->nCexMax )
            {
                abctime clkFree = Abc_Clock();
                if ( Cec_TranFreeSimAddModel(pFree, Cbs_ReadModel(pCbs), a, h) )
                    pProf->nCombFreeCexStored++;
                else
                    pProf->nCombFreeCexInvalid++;
                pProf->timeFreeCexSim += Abc_Clock() - clkFree;
            }
        }
        else if ( fUnknown )
            pProf->nCombUnknown++;
        else
        {
            Vec_StrWriteEntry( vStage, i, 1 );
            pProf->nCombProved++;
        }
    }
    pProf->timeCombSolve += Abc_Clock() - clk;
    Cec_TranFreeSimStop( pFree );
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
    Vec_Int_t * vSeqPairs = NULL;
    Vec_Int_t * vAndLeaves = NULL;
    Vec_Str_t * vAndCounts = NULL;
    Vec_Int_t * vStatus = Vec_IntStart( nCands );
    Vec_Str_t * vStage;
    int fNeedComb = pPars->nRootStage != 2;
    int fNeedSeq = pPars->nRootStage != 1;
    int i, RetValue = 1, nProved = 0, nSeq = 0, nSeqProved = 0;
    abctime clk, timeSeq = 0, clkBatch = Abc_Clock();
    memset( &Cor, 0, sizeof(Cor) );
    clk = Abc_Clock();
    pBatch = Cec_TranBuildRootBatch( p, pCands, nCands,
        fNeedComb && !pPars->fUseCbsMultiLit ? 2 : 0,
        &vPairs, &vQueries,
        fNeedComb && pPars->fUseCbsMultiLit ? &vAndLeaves : NULL,
        fNeedComb && pPars->fUseCbsMultiLit ? &vAndCounts : NULL );
    clk = Abc_Clock() - clk;
    pProf->timeFinalMiter += clk;
    pProf->timeCombBuild += clk;
    pProf->nFinalCalls++;
    vStage = fNeedComb ? Cec_TranProveCombBatch( pBatch, pCands, nCands,
        vPairs, vQueries, vAndLeaves, vAndCounts, pPars, pProf ) :
        Vec_StrStart( nCands );
    for ( i = 0; i < nCands; i++ )
        if ( Vec_StrEntry(vStage, i) == 0 && !pCands[i].fDivGlobal )
            nSeq++;
    if ( fNeedSeq )
        pProf->nSeqCands += nSeq;
    if ( fNeedSeq && nSeq )
    {
        Gia_ManSetPhase( pBatch );
        pBatch->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(pBatch) );
        Gia_ManForEachObj( pBatch, pObj, i )
            Gia_ObjSetRepr( pBatch, i, GIA_VOID );
        Gia_ManCreateValueRefs( pBatch );
        // Keep universally proved combinational relations in the same class
        // hypothesis.  Global-hash fallback relations, however, enter this
        // closure only when CBS already proved them: an unresolved distant
        // signature match has very low sequential conversion and can make a
        // large shared closure substantially more expensive.
        vSeqPairs = Vec_IntAlloc( 2 * nCands );
        for ( i = 0; i < nCands; i++ )
            if ( Vec_StrEntry(vStage, i) == 1 || !pCands[i].fDivGlobal )
                Vec_IntPushTwo( vSeqPairs, Vec_IntEntry(vPairs, 2*i),
                    Vec_IntEntry(vPairs, 2*i + 1) );
        Cec_TranSeedRootClasses( pBatch, vSeqPairs );
        pProf->nSeqSeeded += Vec_IntSize(vSeqPairs) / 2;
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
        if ( !fProved && fNeedSeq && nSeq && !pCands[i].fDivGlobal )
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
    if ( fNeedSeq && nSeq )
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
    Vec_IntFreeP( &vSeqPairs );
    Vec_IntFreeP( &vAndLeaves );
    Vec_StrFreeP( &vAndCounts );
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
    Cec_TranCand_t const * pCands, Vec_Int_t * vStatus,
    char const * pFailed, int nCands,
    char const * pSolved, Cec_ParTran_t * pPars,
    Cec_TranPatDb_t * pDb, Cec_TranProf_t * pProf, int * piCand )
{
    Cec_TranCandVec_t Retry = {0};
    Gia_Man_t * pMiter;
    Vec_Int_t * vPairs, * vQueries, * vOrig = Vec_IntAlloc( nCands );
    int i, iPo = -1, fAdded;
    *piCand = -1;
    assert( (vStatus != NULL) != (pFailed != NULL) );
    for ( i = 0; i < nCands; i++ )
        if ( (pFailed ? pFailed[i] : !Vec_IntEntry(vStatus, i)) &&
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
        &vPairs, &vQueries, NULL, NULL );
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
    // The recipe costs at most nGates new AIG nodes; structural hashing can
    // only improve the final gain.  Strict-root candidates cache the simpler
    // MFFC-nGates bound at discovery, so this affected-MFFC walk is only a
    // fallback for lanes whose divisors are not guaranteed outside the MFFC.
    // The one real bundle commit below still performs cleanup and checks the
    // exact combined AND+register gain.
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

// Group candidates by MFFC-ranked target and sort each root's alternatives by
// local gain.  Every layer is proved even after another alternative succeeds;
// the exact-cost portfolio at commit time then compares this order's winner
// with the q=1-primary winner and prevents a globally worse replacement.
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

// qStrictAll is grouped by target and gain-sorted within each group.  Store
// each [begin,end) range and the maximum normal/rescue widths.  Layer lookup
// scans the small per-root range, first exposing legacy candidates, then
// failure-pool candidates, and finally repeating both classes as an audit;
// vTried makes that repeat submit only alternatives skipped after a root was
// solved.  The metadata remains O(number of roots).
static Vec_Int_t * Cec_TranCandBuildRootGroups(
    Cec_TranCandVec_t const * pCands, int * pnNormalLayers,
    int * pnRescueLayers )
{
    Vec_Int_t * vGroups = Vec_IntAlloc( 128 );
    int i, k, iEnd, nNormal, nRescue;
    *pnNormalLayers = *pnRescueLayers = 0;
    for ( i = 0; i < pCands->nSize; i = iEnd )
    {
        for ( iEnd = i + 1; iEnd < pCands->nSize &&
              pCands->pArray[iEnd].iTarget == pCands->pArray[i].iTarget;
              iEnd++ ) {}
        Vec_IntPushTwo( vGroups, i, iEnd );
        nNormal = nRescue = 0;
        for ( k = i; k < iEnd; k++ )
            if ( pCands->pArray[k].fDivRescue )
                nRescue++;
            else
                nNormal++;
        *pnNormalLayers = Abc_MaxInt( *pnNormalLayers, nNormal );
        *pnRescueLayers = Abc_MaxInt( *pnRescueLayers, nRescue );
    }
    return vGroups;
}

static int Cec_TranCandRootGroupLayerPos(
    Cec_TranCandVec_t const * pCands, int iBeg, int iEnd,
    int iLayer, int nNormalLayers, int nRescueLayers )
{
    int i, iRank, fRescue = 0;
    iLayer %= nNormalLayers + nRescueLayers;
    iRank = iLayer;
    if ( iRank >= nNormalLayers )
        iRank -= nNormalLayers, fRescue = 1;
    for ( i = iBeg; i < iEnd; i++ )
        if ( pCands->pArray[i].fDivRescue == (unsigned)fRescue &&
             iRank-- == 0 )
            return i;
    return -1;
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
            if ( Cec_TranCandGainCompare(pCands + i,
                    pCands + iPrev) < 0 )
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

// The exact q=1 frontier is a conservative portfolio member.  It includes
// ordinary non-resub candidates and candidates explicitly generated by the
// legacy/direct/boundary q=1 path, but never admits a root which exists only
// because q>1 explored additional choices.  Comparing its cleanup cost with
// the full gain portfolio gives large q a strict q=1 bundle fallback.
static Vec_Int_t * Cec_TranSelectRootBatchPrimary( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, Vec_Int_t * vStatus, int nCands,
    int nSelectMax )
{
    Vec_Int_t * vSelected = Vec_IntAlloc( nCands );
    int * pTargetPos = ABC_FALLOC( int, Gia_ManObjNum(p) );
    int i, iPos, iPrev;
    for ( i = 0; i < nCands; i++ )
    {
        if ( !Vec_IntEntry(vStatus, i) ||
             (pCands[i].nResubRank > 0 &&
              !pCands[i].fPrimaryFrontier) )
            continue;
        iPos = pTargetPos[pCands[i].iTarget];
        if ( iPos >= 0 )
        {
            iPrev = Vec_IntEntry( vSelected, iPos );
            if ( Cec_TranCandGainCompare(pCands + i,
                    pCands + iPrev) < 0 )
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

static int Cec_TranRootSelectedCost( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, Vec_Int_t * vSelected )
{
    Gia_Man_t * pTemp, * pClean;
    int Cost;
    if ( Vec_IntSize(vSelected) == 0 )
        return Gia_ManAndNum(p) + Gia_ManRegNum(p);
    pTemp = Cec_TranDupRootBundle( p, pCands, vSelected );
    pClean = Cec_TranCleanup( pTemp );
    Cost = Gia_ManAndNum(pClean) + Gia_ManRegNum(pClean);
    Gia_ManStop( pTemp );
    Gia_ManStop( pClean );
    return Cost;
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

// Counterfactual size profiles use the same per-target winner selection and
// cleanup as the real commit.  With only three candidate kinds, the six
// proper nonempty subsets are enough to recover exact Shapley contributions;
// the empty size is the input and the full size is the actual committed
// result.  Additional subsets expose the marginal utility of raw resub ranks
// above one, CEGAR waves after wave one, and the two sources currently folded
// into the existing kind (global lookup versus zero-gate resub recipes).
static void Cec_TranRootContributionCost( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, Vec_Int_t * vStatus, int nCands,
    int nSelectMax, int pKindAnds[8], int pKindRegs[8],
    int * pnRank1Ands, int * pnRank1Regs,
    int * pnWave1Ands, int * pnWave1Regs,
    int * pnNoGlobalExistAnds, int * pnNoResubExistAnds )
{
    Vec_Int_t * vEnabled = Vec_IntStart( nCands );
    int i, Mask, fHasExtraRank = 0, fHasLaterWave = 0;
    int fHasGlobalExist = 0, fHasResubExist = 0, nDummyRegs;
    pKindAnds[0] = Gia_ManAndNum( p );
    pKindRegs[0] = Gia_ManRegNum( p );
    pKindAnds[7] = pKindRegs[7] = -1;
    for ( Mask = 1; Mask < 7; Mask++ )
    {
        for ( i = 0; i < nCands; i++ )
            Vec_IntWriteEntry( vEnabled, i,
                Vec_IntEntry(vStatus, i) &&
                (Mask & (1 << pCands[i].nKind)) );
        Cec_TranRootBundleCost( p, pCands, vEnabled, nCands,
            nSelectMax, pKindAnds + Mask, pKindRegs + Mask );
    }
    for ( i = 0; i < nCands; i++ )
    {
        fHasExtraRank |= Vec_IntEntry(vStatus, i) &&
            pCands[i].nResubRank > 1;
        Vec_IntWriteEntry( vEnabled, i,
            Vec_IntEntry(vStatus, i) && pCands[i].nResubRank <= 1 );
    }
    if ( fHasExtraRank )
        Cec_TranRootBundleCost( p, pCands, vEnabled, nCands,
            nSelectMax, pnRank1Ands, pnRank1Regs );
    else
        *pnRank1Ands = *pnRank1Regs = -1;
    for ( i = 0; i < nCands; i++ )
    {
        fHasLaterWave |= Vec_IntEntry(vStatus, i) && pCands[i].nWave > 0;
        Vec_IntWriteEntry( vEnabled, i,
            Vec_IntEntry(vStatus, i) && pCands[i].nWave == 0 );
    }
    if ( fHasLaterWave )
        Cec_TranRootBundleCost( p, pCands, vEnabled, nCands,
            nSelectMax, pnWave1Ands, pnWave1Regs );
    else
        *pnWave1Ands = *pnWave1Regs = -1;
    for ( i = 0; i < nCands; i++ )
    {
        int fGlobalExist = pCands[i].nKind == CEC_TRAN_CAND_EXIST &&
            pCands[i].nResubRank == 0;
        fHasGlobalExist |= Vec_IntEntry(vStatus, i) && fGlobalExist;
        Vec_IntWriteEntry( vEnabled, i,
            Vec_IntEntry(vStatus, i) && !fGlobalExist );
    }
    if ( fHasGlobalExist )
        Cec_TranRootBundleCost( p, pCands, vEnabled, nCands,
            nSelectMax, pnNoGlobalExistAnds, &nDummyRegs );
    else
        *pnNoGlobalExistAnds = -1;
    for ( i = 0; i < nCands; i++ )
    {
        int fResubExist = pCands[i].nKind == CEC_TRAN_CAND_EXIST &&
            pCands[i].nResubRank > 0;
        fHasResubExist |= Vec_IntEntry(vStatus, i) && fResubExist;
        Vec_IntWriteEntry( vEnabled, i,
            Vec_IntEntry(vStatus, i) && !fResubExist );
    }
    if ( fHasResubExist )
        Cec_TranRootBundleCost( p, pCands, vEnabled, nCands,
            nSelectMax, pnNoResubExistAnds, &nDummyRegs );
    else
        *pnNoResubExistAnds = -1;
    Vec_IntFree( vEnabled );
}

// Split the exact cleanup gain by both proof stage and candidate kind.  The
// combinational characteristic function starts from the input network.  The
// sequential characteristic function starts from the full combinational
// bundle, so its Shapley values add up to the incremental temporal reduction
// instead of double-counting reductions already certified combinationally.
static void Cec_TranRootStageContributionCost( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, Vec_Int_t * vStatus, int nCands,
    int nSelectMax, int nAndAfterComb, int nRegAfterComb,
    long long pStageAndGain[2][8], long long pStageRegGain[2][8] )
{
    Vec_Int_t * vEnabled = Vec_IntStart( nCands );
    int i, Mask, Stage, nAnds, nRegs;
    memset( pStageAndGain, 0, 2 * 8 * sizeof(long long) );
    memset( pStageRegGain, 0, 2 * 8 * sizeof(long long) );
    for ( Stage = 0; Stage < 2; Stage++ )
    for ( Mask = 1; Mask < 7; Mask++ )
    {
        for ( i = 0; i < nCands; i++ )
        {
            int fComb = pCands[i].nProofStage == 1;
            int fKind = (Mask & (1 << pCands[i].nKind)) != 0;
            Vec_IntWriteEntry( vEnabled, i, Vec_IntEntry(vStatus, i) &&
                (Stage == 0 ? (fComb && fKind) : (fComb || fKind)) );
        }
        Cec_TranRootBundleCost( p, pCands, vEnabled, nCands,
            nSelectMax, &nAnds, &nRegs );
        pStageAndGain[Stage][Mask] =
            (Stage ? nAndAfterComb : Gia_ManAndNum(p)) - nAnds;
        pStageRegGain[Stage][Mask] =
            (Stage ? nRegAfterComb : Gia_ManRegNum(p)) - nRegs;
    }
    pStageAndGain[0][7] = Gia_ManAndNum(p) - nAndAfterComb;
    pStageRegGain[0][7] = Gia_ManRegNum(p) - nRegAfterComb;
    Vec_IntFree( vEnabled );
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
    Vec_Int_t * vObjMap, * vSelected, * vPrimary;
    int Gain, CostGain, CostPrimary, fProved = 1;
    abctime clk;
    *pvSelected = NULL;
    vSelected = Cec_TranSelectRootBatchBundle( p, pCands, vStatus,
        nCands, nSelectMax );
    vPrimary = Cec_TranSelectRootBatchPrimary( p, pCands, vStatus,
        nCands, nSelectMax );
    if ( Vec_IntSize(vSelected) == 0 )
    {
        Vec_IntFree( vSelected );
        Vec_IntFree( vPrimary );
        return 0;
    }
    // Exact cleanup is cheap compared with proving the relations.  Evaluate
    // both the legacy local-gain bundle and the primary-first fallback bundle,
    // then commit the globally smaller one.  This preserves q>1 improvements
    // such as transmitter while preventing negative interactions such as
    // loopv3, without attempting an exponential per-root combination search.
    if ( Vec_IntEqual(vSelected, vPrimary) )
    {
        pProf->nRootBundlePortfolioTies++;
        Vec_IntFree( vPrimary );
    }
    else
    {
        CostGain = Cec_TranRootSelectedCost( p, pCands, vSelected );
        CostPrimary = Cec_TranRootSelectedCost( p, pCands, vPrimary );
        pProf->nRootBundlePortfolioAdvantage +=
            Abc_AbsInt( CostGain - CostPrimary );
        if ( CostPrimary <= CostGain )
        {
            Vec_IntFree( vSelected );
            vSelected = vPrimary;
            pProf->nRootBundlePrimaryWins++;
        }
        else
        {
            Vec_IntFree( vPrimary );
            pProf->nRootBundleGainWins++;
        }
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

static void Cec_TranMffcScratchClear( char * pMark, Vec_Int_t * vMarked )
{
    int i, iObj;
    Vec_IntForEachEntry( vMarked, iObj, i )
        pMark[iObj] = 0;
    Vec_IntClear( vMarked );
}

static void Cec_TranMarkMffc_rec( Gia_Man_t * p, int iObj, char * pMark,
    Vec_Int_t * vMarked )
{
    Gia_Obj_t * pObj;
    int iFan;
    if ( pMark[iObj] )
        return;
    pMark[iObj] = 1;
    Vec_IntPush( vMarked, iObj );
    pObj = Gia_ManObj( p, iObj );
    if ( !Gia_ObjIsAnd(pObj) )
        return;
    iFan = Gia_ObjFaninId0p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         Gia_ObjRefNumId(p, iFan) == 1 )
        Cec_TranMarkMffc_rec( p, iFan, pMark, vMarked );
    iFan = Gia_ObjFaninId1p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         Gia_ObjRefNumId(p, iFan) == 1 )
        Cec_TranMarkMffc_rec( p, iFan, pMark, vMarked );
}

// Collect physical divisor nodes by increasing TFI distance.  MFFC nodes are
// traversed but never retained, which reaches the MFFC boundary and then its
// upstream support.  PI and RO objects are both legal CIs.  Complemented
// phases are explored by the dependency engine and therefore do not consume
// separate B slots.  Every collected divisor is in the target's TFI and has a
// smaller topological object ID, so a separate full-graph TFO mark is both
// redundant and needlessly quadratic across all roots.
static Vec_Int_t * Cec_TranCollectDivPool( Gia_Man_t * p, int iTarget,
    int nDepthMax, int nNodesMax, char * pMffc, Vec_Int_t * vMffc )
{
    Vec_Int_t * vPool = Vec_IntAlloc( nNodesMax ? nNodesMax : 64 );
    Vec_Int_t * vFront = Vec_IntAlloc( 32 );
    Vec_Int_t * vNext = Vec_IntAlloc( 32 );
    Gia_Obj_t * pObj, * pFan;
    int d, i, k, iObj, iFan, fFull = 0;
    Cec_TranMffcScratchClear( pMffc, vMffc );
    Cec_TranMarkMffc_rec( p, iTarget, pMffc, vMffc );
    // The BFS used to allocate and clear one |G|-byte pSeen array per root.
    // Traversal IDs provide the same membership test with O(visited TFI)
    // writes and no per-root full-graph zeroing.
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrentId( p, iTarget );
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
                if ( Gia_ObjIsTravIdCurrentId(p, iFan) )
                    continue;
                Gia_ObjSetTravIdCurrentId( p, iFan );
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
    return vPool;
}

// Add divisors reached by entering the target MFFC at all of its external
// boundary leaves and then expanding upstream in parallel.  A target-rooted
// depth bound can stop before a deep MFFC boundary; measuring depth from the
// boundary gives these leaves and their supports an independent opportunity.
// When a boundary is wide, evenly spaced leaves avoid inheriting the DFS
// order used by the MFFC marker.
static void Cec_TranAppendBoundaryDivs( Gia_Man_t * p, int iTarget,
    int nDepthMax, int nAddMax, char const * pMffc, Vec_Int_t * vMffc,
    Vec_Int_t * vPool )
{
    Vec_Int_t * vBoundary = Vec_IntAlloc( 32 );
    Vec_Int_t * vFront = Vec_IntAlloc( 32 );
    Vec_Int_t * vNext = Vec_IntAlloc( 32 );
    Gia_Obj_t * pObj, * pFan;
    int i, k, d, iObj, iFan, iPos, nSelect, nAdded = 0;
    if ( nAddMax <= 0 )
        goto cleanup;
    Gia_ManIncrementTravId( p );
    Vec_IntForEachEntry( vMffc, iObj, i )
    {
        pObj = Gia_ManObj( p, iObj );
        if ( !Gia_ObjIsAnd(pObj) )
            continue;
        for ( k = 0; k < 2; k++ )
        {
            iFan = k ? Gia_ObjFaninId1p(p, pObj) :
                       Gia_ObjFaninId0p(p, pObj);
            if ( iFan == 0 || iFan >= iTarget || pMffc[iFan] ||
                 Gia_ObjIsTravIdCurrentId(p, iFan) )
                continue;
            Gia_ObjSetTravIdCurrentId( p, iFan );
            if ( Gia_ObjIsCand(Gia_ManObj(p, iFan)) )
                Vec_IntPush( vBoundary, iFan );
        }
    }
    nSelect = Abc_MinInt( Vec_IntSize(vBoundary),
        Abc_MaxInt(1, nAddMax / 2) );
    // Start a bounded upstream search from a uniform subset of the boundary.
    Gia_ManIncrementTravId( p );
    for ( i = 0; i < nSelect; i++ )
    {
        iPos = (int)(((long long)(2 * i + 1) *
            Vec_IntSize(vBoundary)) / (2 * nSelect));
        iObj = Vec_IntEntry( vBoundary,
            Abc_MinInt(iPos, Vec_IntSize(vBoundary) - 1) );
        if ( Gia_ObjIsTravIdCurrentId(p, iObj) )
            continue;
        Gia_ObjSetTravIdCurrentId( p, iObj );
        Vec_IntPush( vFront, iObj );
        if ( Vec_IntFind(vPool, iObj) < 0 )
        {
            Vec_IntPush( vPool, iObj );
            if ( ++nAdded == nAddMax )
                goto cleanup;
        }
    }
    for ( d = 1; Vec_IntSize(vFront) &&
         (!nDepthMax || d <= nDepthMax); d++ )
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
                if ( Gia_ObjIsTravIdCurrentId(p, iFan) )
                    continue;
                Gia_ObjSetTravIdCurrentId( p, iFan );
                pFan = Gia_ManObj( p, iFan );
                if ( iFan != 0 && iFan < iTarget && !pMffc[iFan] &&
                     Gia_ObjIsCand(pFan) && Vec_IntFind(vPool, iFan) < 0 )
                {
                    Vec_IntPush( vPool, iFan );
                    if ( ++nAdded == nAddMax )
                        goto cleanup;
                }
                if ( Gia_ObjIsAnd(pFan) )
                    Vec_IntPush( vNext, iFan );
            }
        }
        ABC_SWAP( Vec_Int_t, *vFront, *vNext );
    }
cleanup:
    Vec_IntFree( vBoundary );
    Vec_IntFree( vFront );
    Vec_IntFree( vNext );
}

// Nearby earlier objects often represent reconvergent side logic which is
// absent from the target TFI.  Earlier topological IDs cannot depend on the
// target, so excluding the target MFFC is sufficient to keep these divisors
// combinationally legal.  Bound the scan to keep the per-root cost predictable.
static void Cec_TranAppendLocalDivs( Gia_Man_t * p, int iTarget,
    int nAddMax, char const * pMffc, Vec_Int_t * vPool )
{
    Gia_Obj_t * pObj;
    int iObj, nAdded = 0, nScanned = 0;
    int nScanMax = 64 * nAddMax;
    for ( iObj = iTarget - 1; iObj > 0 && nAdded < nAddMax &&
          nScanned < nScanMax; iObj--, nScanned++ )
    {
        pObj = Gia_ManObj( p, iObj );
        if ( pMffc[iObj] || !Gia_ObjIsCand(pObj) ||
             Vec_IntFind(vPool, iObj) >= 0 )
            continue;
        Vec_IntPush( vPool, iObj );
        nAdded++;
    }
}

// Uniform samples over the whole earlier topological prefix provide a cheap
// deterministic analogue of random global divisors.  The later simulation
// ranking decides which sampled signals actually enter B.
static void Cec_TranAppendGlobalDivs( Gia_Man_t * p, int iTarget,
    int nAddMax, char const * pMffc, Vec_Int_t * vPool )
{
    Gia_Obj_t * pObj;
    int i, iObj, nAdded = 0;
    int nTrials = Abc_MinInt( iTarget - 1, 64 * nAddMax );
    if ( nTrials <= 0 )
        return;
    for ( i = 0; i < nTrials && nAdded < nAddMax; i++ )
    {
        iObj = 1 + (int)(((long long)(2 * i + 1) *
            (iTarget - 1)) / (2 * nTrials));
        iObj = Abc_MinInt( iObj, iTarget - 1 );
        pObj = Gia_ManObj( p, iObj );
        if ( pMffc[iObj] || !Gia_ObjIsCand(pObj) ||
             Vec_IntFind(vPool, iObj) >= 0 )
            continue;
        Vec_IntPush( vPool, iObj );
        nAdded++;
    }
}

// The first B entries remain the legacy target-TFI BFS pool.  Extra capacity
// is divided among independent structural routes instead of extending only
// that BFS order.  Route boundaries let later attempts construct from one
// source at a time before falling back to a mixed information-ranked pool.
static Vec_Int_t * Cec_TranCollectDivReservoir( Gia_Man_t * p, int iTarget,
    int nDepthMax, int nPoolMax, char * pMffc, Vec_Int_t * vMffc,
    int RouteBeg[4], int RouteEnd[4] )
{
    Vec_Int_t * vPool;
    int nRouteMax;
    RouteBeg[0] = 0;
    if ( nPoolMax <= 0 )
    {
        vPool = Cec_TranCollectDivPool( p, iTarget, nDepthMax, 0,
            pMffc, vMffc );
        RouteEnd[0] = Vec_IntSize(vPool);
        RouteBeg[1] = RouteEnd[1] = RouteEnd[0];
        RouteBeg[2] = RouteEnd[2] = RouteEnd[0];
        RouteBeg[3] = RouteEnd[3] = RouteEnd[0];
        return vPool;
    }
    nRouteMax = 2 * nPoolMax;
    vPool = Cec_TranCollectDivPool( p, iTarget, nDepthMax, nRouteMax,
        pMffc, vMffc );
    RouteEnd[0] = Vec_IntSize(vPool);
    RouteBeg[1] = RouteEnd[0];
    Cec_TranAppendBoundaryDivs( p, iTarget, nDepthMax, nRouteMax,
        pMffc, vMffc, vPool );
    RouteEnd[1] = Vec_IntSize(vPool);
    RouteBeg[2] = RouteEnd[1];
    Cec_TranAppendLocalDivs( p, iTarget, nRouteMax, pMffc, vPool );
    RouteEnd[2] = Vec_IntSize(vPool);
    RouteBeg[3] = RouteEnd[2];
    Cec_TranAppendGlobalDivs( p, iTarget, nRouteMax, pMffc, vPool );
    RouteEnd[3] = Vec_IntSize(vPool);
    return vPool;
}

// Rank a physical divisor by the number of opposite-label simulation pairs
// it separates.  If O0/O1 and I0/I1 are the off/on-set counts in the two
// divisor cofactors, O0*I1 + O1*I0 is exactly the number of off/on pairs cut
// by this divisor.  The score is phase-independent and is therefore a cheap
// proxy for the reduction in the residual dependency ambiguity.
typedef struct Cec_TranDivRank_t_ Cec_TranDivRank_t;
struct Cec_TranDivRank_t_
{
    word Score;
    int  iPos;
};

static int Cec_TranDivRankCompare( const void * p1, const void * p2 )
{
    Cec_TranDivRank_t const * pR1 = (Cec_TranDivRank_t const *)p1;
    Cec_TranDivRank_t const * pR2 = (Cec_TranDivRank_t const *)p2;
    if ( pR1->Score > pR2->Score )
        return -1;
    if ( pR1->Score < pR2->Score )
        return 1;
    return pR1->iPos - pR2->iPos;
}

static Cec_TranDivRank_t * Cec_TranRankDivReservoir( Cec_TranSim_t * pSim,
    int iTarget, Vec_Int_t * vReservoir )
{
    Cec_TranDivRank_t * pRanks = ABC_ALLOC( Cec_TranDivRank_t,
        Vec_IntSize(vReservoir) );
    word * pTarget = Cec_TranSimObj( pSim, iTarget );
    word * pDiv;
    word nOff0, nOff1, nOn0, nOn1;
    int i, s, iObj;
    Vec_IntForEachEntry( vReservoir, iObj, i )
    {
        pDiv = Cec_TranSimObj( pSim, iObj );
        nOff0 = nOff1 = nOn0 = nOn1 = 0;
        for ( s = 0; s < pSim->nSlots; s++ )
        {
            nOff0 += Abc_TtCountOnes( ~pTarget[s] & ~pDiv[s] );
            nOff1 += Abc_TtCountOnes( ~pTarget[s] &  pDiv[s] );
            nOn0  += Abc_TtCountOnes(  pTarget[s] & ~pDiv[s] );
            nOn1  += Abc_TtCountOnes(  pTarget[s] &  pDiv[s] );
        }
        pRanks[i].Score = nOff0 * nOn1 + nOff1 * nOn0;
        pRanks[i].iPos = i;
    }
    qsort( pRanks, Vec_IntSize(vReservoir),
        sizeof(Cec_TranDivRank_t), Cec_TranDivRankCompare );
    return pRanks;
}

// A zero-gate existing replacement does not need the resub cover engine.
// Scan all structural routes for an exact full-signature match and return the
// first local/diverse/global divisor (including complemented phase).  This is
// both broader than selecting 2B first and much cheaper than initializing the
// unate/pair machinery for a direct literal answer.
static int Cec_TranFindDirectDiv( Cec_TranSim_t * pSim,
    Cec_TranRoot_t const * pRoot, Vec_Int_t * vReservoir,
    Cec_TranCand_t * pCand )
{
    int i, f, iObj;
    Vec_IntForEachEntry( vReservoir, iObj, i )
        for ( f = 0; f < 2; f++ )
            if ( Cec_TranSigMatchesRoot(pSim, pRoot->iObj,
                    Abc_Var2Lit(iObj, f), NULL) )
            {
                *pCand = Cec_TranCandCreateLiteral( pRoot->iObj,
                    Abc_Var2Lit(iObj, f), pRoot->nMffc,
                    CEC_TRAN_CAND_EXIST, 1 );
                pCand->Gain = pRoot->nMffc;
                return 1;
            }
    return 0;
}

// Pool zero is byte-for-byte the former BFS prefix, preserving the strong
// first candidate.  Pools one through three first draw from boundary, local,
// and global routes respectively.  Later pools mix all unused routes.  Every
// alternate keeps a small set of informative BFS anchors so the dependency
// engine can combine new information with strong local divisors.
static Vec_Int_t * Cec_TranBuildDivPool( Vec_Int_t * vReservoir,
    int nPoolMax, int iPool, Cec_TranDivRank_t const * pRanks,
    unsigned char * pUseCount, int const RouteBeg[4],
    int const RouteEnd[4] )
{
    Vec_Int_t * vPool;
    char * pPicked;
    int i, iPos, iRoute, nBase, nPoolSize, nAnchors;
    nBase = nPoolMax ? Abc_MinInt(nPoolMax, RouteEnd[0]) : RouteEnd[0];
    nPoolSize = nPoolMax ?
        Abc_MinInt(nPoolMax, Vec_IntSize(vReservoir)) :
        Vec_IntSize(vReservoir);
    vPool = Vec_IntAlloc( nPoolSize );
    if ( iPool == 0 || pRanks == NULL )
    {
        for ( i = 0; i < nBase; i++ )
        {
            Vec_IntPush( vPool, Vec_IntEntry(vReservoir, i) );
            if ( pUseCount )
                pUseCount[i]++;
        }
        return vPool;
    }
    pPicked = ABC_CALLOC( char, Vec_IntSize(vReservoir) );
    nAnchors = Abc_MinInt( nBase,
        Abc_MaxInt(1, nPoolSize / 4) );
    // Informative anchors from the original BFS pool retain locality.
    for ( i = 0; i < Vec_IntSize(vReservoir) &&
         Vec_IntSize(vPool) < nAnchors; i++ )
    {
        iPos = pRanks[i].iPos;
        if ( iPos >= nBase )
            continue;
        Vec_IntPush( vPool, Vec_IntEntry(vReservoir, iPos) );
        pPicked[iPos] = 1;
    }
    // Give each structural route one independent choice-zero construction.
    iRoute = iPool >= 1 && iPool <= 3 ? iPool : -1;
    for ( i = 0; iRoute >= 0 && i < Vec_IntSize(vReservoir) &&
         Vec_IntSize(vPool) < nPoolSize; i++ )
    {
        iPos = pRanks[i].iPos;
        if ( iPos < RouteBeg[iRoute] || iPos >= RouteEnd[iRoute] ||
             pPicked[iPos] || pUseCount[iPos] )
            continue;
        Vec_IntPush( vPool, Vec_IntEntry(vReservoir, iPos) );
        pPicked[iPos] = 1;
    }
    // Fill from informative nodes outside the BFS prefix which have not yet
    // appeared in any pool.  This also implements the mixed route.
    for ( i = 0; i < Vec_IntSize(vReservoir) &&
         Vec_IntSize(vPool) < nPoolSize; i++ )
    {
        iPos = pRanks[i].iPos;
        if ( iPos < nBase || pPicked[iPos] || pUseCount[iPos] )
            continue;
        Vec_IntPush( vPool, Vec_IntEntry(vReservoir, iPos) );
        pPicked[iPos] = 1;
    }
    // Reservoirs smaller than the requested number of alternatives may need
    // controlled reuse; keep the same information ordering for that tail.
    for ( i = 0; i < Vec_IntSize(vReservoir) &&
         Vec_IntSize(vPool) < nPoolSize; i++ )
    {
        iPos = pRanks[i].iPos;
        if ( pPicked[iPos] )
            continue;
        Vec_IntPush( vPool, Vec_IntEntry(vReservoir, iPos) );
        pPicked[iPos] = 1;
    }
    Vec_IntForEachEntry( vPool, iPos, i )
    {
        int k;
        for ( k = 0; k < Vec_IntSize(vReservoir); k++ )
            if ( Vec_IntEntry(vReservoir, k) == iPos )
            {
                pUseCount[k]++;
                break;
            }
    }
    ABC_FREE( pPicked );
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

typedef struct Cec_TranDepScratch_t_ Cec_TranDepScratch_t;
struct Cec_TranDepScratch_t_
{
    Vec_Ptr_t * vDivs;
    Vec_Wec_t * vRecipes;
    word *      pOff;
    word *      pOn;
    int         nAttemptsLast;
    abctime     timeInitLast;
    abctime     timeSearchLast;
    abctime     timeAttemptLast[2 * CEC_TRAN_RESUB_CHOICES_MAX];
    int         fAttemptUniqueLast[2 * CEC_TRAN_RESUB_CHOICES_MAX];
};

static void Cec_TranDepScratchStart( Cec_TranDepScratch_t * p,
    int nSlots, int nDivsMax )
{
    p->vDivs = Vec_PtrAlloc( nDivsMax + 2 );
    p->vRecipes = Vec_WecAlloc( CEC_TRAN_RESUB_CHOICES_MAX );
    p->pOff = ABC_ALLOC( word, nSlots );
    p->pOn  = ABC_ALLOC( word, nSlots );
    p->nAttemptsLast = 0;
    p->timeInitLast = p->timeSearchLast = 0;
    memset( p->timeAttemptLast, 0, sizeof(p->timeAttemptLast) );
    memset( p->fAttemptUniqueLast, 0, sizeof(p->fAttemptUniqueLast) );
}

static void Cec_TranDepScratchStop( Cec_TranDepScratch_t * p )
{
    Vec_PtrFree( p->vDivs );
    Vec_WecFree( p->vRecipes );
    ABC_FREE( p->pOff );
    ABC_FREE( p->pOn );
}

static void Cec_TranCandFromDependency( Cec_TranSim_t * pSim,
    Cec_TranRoot_t const * pRoot, Vec_Int_t * vPool, word * pCare,
    int fStrict, Vec_Ptr_t * vDivs, Vec_Int_t * vRecipe,
    Cec_TranCand_t * pCand )
{
    int i, Code, nArray = Vec_IntSize(vRecipe);
    int nVars = Vec_PtrSize(vDivs);
    memset( pCand, 0, sizeof(*pCand) );
    pCand->iTarget = pRoot->iObj;
    pCand->nMffc = pRoot->nMffc;
    pCand->Gain = -1;
    pCand->fStrict = fStrict;
    pCand->nGates = nArray / 2;
    assert( pCand->nGates <= CEC_TRAN_RECIPE_NODES_MAX );
    for ( i = 0; i < 2 * pCand->nGates; i++ )
        pCand->Recipe[i] = Cec_TranRecipeCodeFromResub(
            Vec_IntEntry(vRecipe, i), nVars, vPool );
    pCand->iOut = Cec_TranRecipeCodeFromResub(
        Vec_IntEntryLast(vRecipe), nVars, vPool );
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
}

static int Cec_TranComputeDependencies( Cec_TranSim_t * pSim,
    Cec_ParTran_t * pPars, Cec_TranRoot_t const * pRoot,
    Vec_Int_t * vPool, word * pCare, int fStrict,
    Cec_TranCand_t * pCands, int nChoices, int iChoiceStart,
    Cec_TranDepScratch_t * pScratch )
{
    Vec_Ptr_t * vDivs = pScratch->vDivs;
    word * pOff = pScratch->pOff;
    word * pOn  = pScratch->pOn;
    Vec_Int_t * vRecipe;
    int i, s, iObj, nLimit, nRecipes, nCands = 0;
    word Target, Care;
    assert( nChoices > 0 && iChoiceStart >= 0 &&
            iChoiceStart + nChoices <= CEC_TRAN_RESUB_CHOICES_MAX );
    Vec_PtrClear( vDivs );
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
    pScratch->timeInitLast = pScratch->timeSearchLast = 0;
    memset( pScratch->timeAttemptLast, 0,
        sizeof(pScratch->timeAttemptLast) );
    memset( pScratch->fAttemptUniqueLast, 0,
        sizeof(pScratch->fAttemptUniqueLast) );
    nRecipes = Abc_ResubComputeFunctions( Vec_PtrArray(vDivs),
        Vec_PtrSize(vDivs), pSim->nSlots, nLimit,
        Vec_IntSize(vPool), nChoices, iChoiceStart,
        pPars->fUseResubZero,
        0, 0, pPars->fVerbose,
        pScratch->vRecipes, &pScratch->nAttemptsLast,
        pPars->fProfile ? &pScratch->timeInitLast : NULL,
        pPars->fProfile ? &pScratch->timeSearchLast : NULL,
        pPars->fProfile ? pScratch->timeAttemptLast : NULL,
        pPars->fProfile ? pScratch->fAttemptUniqueLast : NULL );
    Vec_WecForEachLevel( pScratch->vRecipes, vRecipe, i )
    {
        Cec_TranCandFromDependency( pSim, pRoot, vPool, pCare,
            fStrict, vDivs, vRecipe, pCands + nCands );
        pCands[nCands].nResubRank = iChoiceStart + i + 1;
        // Zero-gate existing recipes are suppressed inside the resub search.
        // This lets the same attempt continue to a constructed recipe instead
        // of returning a buffer that would only be discarded here.
        assert( pPars->fUseResubZero ||
            pCands[nCands].nGates > 0 ||
            Abc_Lit2Var(pCands[nCands].iOut) == 0 );
        nCands++;
    }
    assert( nCands <= nRecipes && nCands <= nChoices );
    return nCands;
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
        if ( !Cec_TranSigMatchesRoot(pSim, pRoot->iObj, iLit, NULL) )
        {
            pStat->nSigRejected++;
            continue;
        }
        pStat->nSigMatched++;
        Cand = Cec_TranCandCreateLiteral( pRoot->iObj, iLit,
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

// Return one exact earlier-object replacement without allocating a candidate
// vector.  The hash index makes this a narrow signature-bucket lookup; the
// full signature check protects against hash collisions.  It is used only
// after both the legacy constructed pool and the local multi-route scan miss.
static int Cec_TranFindGlobalDirect( Cec_TranSim_t * pSim,
    Cec_TranRoot_t const * pRoot, Cec_TranSigEnt_t * pSigIndex,
    int nSigEntries, char const * pMffc, Cec_TranCand_t * pCand )
{
    word TargetHash;
    int iBeg, iEnd, i, iLit, iObj;
    if ( pSigIndex == NULL )
        return 0;
    TargetHash = Cec_TranLitHash( pSim,
        Abc_Var2Lit(pRoot->iObj, 0) );
    iBeg = Cec_TranSigIndexLowerBound( pSigIndex, nSigEntries,
        TargetHash );
    iEnd = Cec_TranSigIndexUpperBound( pSigIndex, iBeg, nSigEntries,
        TargetHash );
    i = Cec_TranSigIndexFirstEarlier( pSigIndex, iBeg, iEnd,
        pRoot->iObj );
    for ( ; i < iEnd; i++ )
    {
        iLit = pSigIndex[i].iLit;
        iObj = Abc_Lit2Var( iLit );
        if ( iObj == 0 || pMffc[iObj] ||
             !Cec_TranSigMatchesRoot(pSim, pRoot->iObj, iLit, NULL) )
            continue;
        *pCand = Cec_TranCandCreateLiteral( pRoot->iObj, iLit,
            pRoot->nMffc, CEC_TRAN_CAND_EXIST, 1 );
        pCand->Gain = pRoot->nMffc;
        return 1;
    }
    return 0;
}

static void Cec_TranCollectStrictExisting( Gia_Man_t * p,
    Cec_TranSim_t * pSim, Cec_ParTran_t * pPars,
    Cec_TranRoot_t * pRoots, int nRoots, Cec_TranSigEnt_t * pSigIndex,
    int nSigEntries, Cec_TranCandVec_t const * pTried,
    char const * pSolved, char * pMffc, Vec_Int_t * vMffc,
    Cec_TranCandVec_t * pExist,
    Cec_TranDiscStat_t * pStat, Cec_TranProf_t * pProf )
{
    int r, f, iExistStart, iExistingStart;
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
                    Abc_Var2Lit(0, f), NULL) )
            {
                pStat->nSigRejected++;
                continue;
            }
            pStat->nSigMatched++;
            Cand = Cec_TranCandCreateLiteral( pRoots[r].iObj,
                Abc_Var2Lit(0, f), pRoots[r].nMffc,
                CEC_TRAN_CAND_CONST, 1 );
            Cand.Gain = pRoots[r].nMffc;
            if ( !Cec_TranCandVecContains(pTried, &Cand) )
                Cec_TranCandVecPush( pExist, Cand );
        }
        iExistingStart = pExist->nSize;
        if ( pPars->fUseExisting &&
             pRoots[r].nMffc >= pPars->nHardMffc )
        {
            Cec_TranMffcScratchClear( pMffc, vMffc );
            Cec_TranMarkMffc_rec( p, pRoots[r].iObj, pMffc, vMffc );
            Cec_TranCollectGlobalExact( pSim, pRoots + r,
                pSigIndex, nSigEntries, pMffc, 1, 0, 1, pTried,
                pExist, pStat );
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
    Cec_TranRoot_t * pRoots, int nRoots, int iWave,
    Cec_TranSigEnt_t * pSigIndex, int nSigEntries,
    Cec_TranCandVec_t const * pTried, char const * pSolved,
    char * pHadRecipe,
    char * pMffc, Vec_Int_t * vMffc,
    Cec_TranCandVec_t const * pExist, Cec_TranCandVec_t * pConstr,
    Cec_TranDepScratch_t * pDep, Cec_TranDiscStat_t * pStat,
    Cec_TranProf_t * pProf )
{
    int r, k, iPool, iPoolBuild, iAttempt, iChoiceStart, iConstrStart;
    int nDepFound, nDepFoundBefore, nDepFoundTotal;
    int nAttemptsRoot;
    int nAttemptBudget, nCallChoices, nPoolThis, fCanDiversify;
    int fDirect, fGlobalDirect, fKeepLegacyChoices;
    int fFirstPoolMiss;
    int RouteBeg[4], RouteEnd[4];
    Vec_Int_t * vReservoir, * vPool;
    Cec_TranDivRank_t * pRanks;
    unsigned char * pUseCount;
    Cec_TranCand_t Cand, Cands[CEC_TRAN_RESUB_CHOICES_MAX];
    abctime clk, timePart;
    assert( iWave >= 0 && iWave < 64 );
    // Exact same-pool portfolios remain worthwhile when the whole q frontier
    // is small (for example control-heavy arbitrated/loop designs).  On large
    // frontiers their proof conversion collapses while shared-closure cost
    // grows sharply, so reserve the budget for previously unsolved roots.
    fKeepLegacyChoices = (long long)nRoots * pPars->nRootConstrTop <= 20000;
    for ( r = 0; r < nRoots; r++ )
    {
        if ( pSolved && pSolved[pRoots[r].iObj] )
            continue;
        if ( iWave > 0 && pHadRecipe[pRoots[r].iObj] )
            continue;
        if ( pRoots[r].nMffc < pPars->nGainMin )
            continue;
        iConstrStart = pConstr->nSize;
        clk = Abc_Clock();
        vReservoir = Cec_TranCollectDivReservoir( p, pRoots[r].iObj,
            pPars->nConstrMax, pPars->nConstrBaseMax, pMffc, vMffc,
            RouteBeg, RouteEnd );
        timePart = Abc_Clock() - clk;
        pProf->timeSpec += timePart;
        pProf->timeRootDivPool += timePart;
        pProf->timeRootWaveConstruct[iWave] += timePart;
        pProf->nRootDivPoolCalls++;
        pProf->nRootDivPoolNodes += Vec_IntSize(vReservoir);
        for ( k = 0; k < 4; k++ )
            pProf->nRootDivRouteNodes[k] += RouteEnd[k] - RouteBeg[k];
        pStat->nConstructed++;
        pStat->nSigChecks++;

        fCanDiversify = pPars->nConstrBaseMax > 0 &&
            Vec_IntSize(vReservoir) > pPars->nConstrBaseMax;
        // Preserve every legacy choice when the high-quality BFS choice zero
        // succeeds.  When it fails, redirect the remaining q-search budget to
        // independent choice-zero searches on diverse pools.  q=1 has no
        // spare budget, so it gets at most two cheap failure-only rescues.
        nAttemptBudget = pPars->nRootConstrTop == 1 ||
            !fKeepLegacyChoices ? 3 :
            Abc_MinInt( CEC_TRAN_RESUB_CHOICES_MAX,
                2 * pPars->nRootConstrTop + 1 );
        pRanks = NULL;
        pUseCount = ABC_CALLOC( unsigned char, Vec_IntSize(vReservoir) );
        nDepFoundTotal = 0;
        nAttemptsRoot = 0;
        fFirstPoolMiss = 0;
        while ( nAttemptsRoot < nAttemptBudget &&
                nDepFoundTotal < pPars->nRootConstrTop )
        {
            if ( fFirstPoolMiss && nAttemptsRoot == 1 )
            {
                // Route one is a full-reservoir direct literal scan.  Count
                // it as one rescue opportunity, but not as a dependency
                // synthesis attempt because no cover search is performed.
                nAttemptsRoot++;
                pProf->nRootDivAltCalls++;
                pProf->nRootDivRouteCalls[1]++;
                fDirect = Cec_TranFindDirectDiv(pSim, pRoots + r,
                    vReservoir, &Cand);
                fGlobalDirect = !fDirect &&
                    Cec_TranFindGlobalDirect(pSim, pRoots + r,
                        pSigIndex, nSigEntries, pMffc, &Cand);
                if ( fDirect || fGlobalDirect )
                {
                    Cand.nResubRank = 2;
                    Cand.fDivRescue = 1;
                    Cand.fDivGlobal = fGlobalDirect;
                    Cand.fPrimaryFrontier = 1;
                    Cand.nWave = iWave;
                    nDepFoundTotal++;
                    pProf->nRootDivAltRecipes++;
                    pProf->nRootDivGlobalRecipes += fGlobalDirect;
                    pProf->nRootDivRouteRecipes[1]++;
                    pProf->nRootResubGenerated[1]++;
                    if ( !Cec_TranCandVecContains(pTried, &Cand) &&
                         !Cec_TranCandVecContains(pExist, &Cand) &&
                         !Cec_TranCandVecContainsRange(pConstr,
                             iConstrStart, &Cand) )
                    {
                        pStat->nSigMatched++;
                        Cec_TranCandVecPush( pConstr, Cand );
                    }
                    else
                        pStat->nSigRejected++;
                    if ( !fKeepLegacyChoices )
                        break;
                }
                continue;
            }
            if ( nAttemptsRoot == 0 )
            {
                iPool = 0;
                iChoiceStart = 0;
                nCallChoices = 1;
            }
            else if ( !fFirstPoolMiss )
            {
                // Continue exactly where the legacy fixed-pool search left
                // off.  This retains its useful q>1 candidates unchanged.
                if ( nAttemptsRoot >= pPars->nRootConstrTop )
                    break;
                iPool = 0;
                iChoiceStart = nAttemptsRoot;
                nCallChoices = pPars->nRootConstrTop - nAttemptsRoot;
            }
            else
            {
                if ( !fCanDiversify )
                    break;
                iPool = nAttemptsRoot;
                iChoiceStart = 0;
                nCallChoices = 1;
            }
            clk = Abc_Clock();
            if ( iPool > 0 && pRanks == NULL )
                pRanks = Cec_TranRankDivReservoir( pSim,
                    pRoots[r].iObj, vReservoir );
            // After the direct scan misses, spend one ordinary-B constructed
            // attempt on the MFFC boundary route.
            iPoolBuild = iPool ? iPool - 1 : 0;
            nPoolThis = pPars->nConstrBaseMax;
            vPool = Cec_TranBuildDivPool( vReservoir,
                nPoolThis, iPoolBuild, pRanks, pUseCount,
                RouteBeg, RouteEnd );
            timePart = Abc_Clock() - clk;
            pProf->timeSpec += timePart;
            pProf->timeRootDivPool += timePart;
            pProf->timeRootWaveConstruct[iWave] += timePart;
            if ( pPars->fVerbose )
            {
                Abc_Print( 1, "  dependency pool root=%d mffc=%d variant=%d nodes=%d: ",
                    pRoots[r].iObj, pRoots[r].nMffc, iPool,
                    Vec_IntSize(vPool) );
                Vec_IntPrint( vPool );
            }
            clk = Abc_Clock();
            nDepFound = Cec_TranComputeDependencies(pSim, pPars,
                pRoots + r, vPool, NULL, 1,
                Cands, nCallChoices,
                iChoiceStart, pDep);
            timePart = Abc_Clock() - clk;
            pProf->timeConstruct += timePart;
            pProf->timeRootDepSynthesis += timePart;
            pProf->timeRootWaveConstruct[iWave] += timePart;
            pProf->timeRootDepInit += pDep->timeInitLast;
            pProf->timeRootDepSearch += pDep->timeSearchLast;
            iAttempt = nAttemptsRoot;
            for ( k = 0; k < pDep->nAttemptsLast; k++ )
            {
                int iAttemptProf = iAttempt + k;
                // Profile slots are global choice positions within a root,
                // not the local choice-zero index of each alternate pool.
                assert( iAttemptProf < 2 * CEC_TRAN_RESUB_CHOICES_MAX );
                pProf->nRootDepAttemptCalls[iAttemptProf]++;
                pProf->nRootDepAttemptUnique[iAttemptProf] +=
                    pDep->fAttemptUniqueLast[k];
                pProf->timeRootDepAttempt[iAttemptProf] +=
                    pDep->timeAttemptLast[k];
            }
            nAttemptsRoot += pDep->nAttemptsLast;
            pProf->nRootDepAttempts += pDep->nAttemptsLast;
            pProf->nRootDivRouteCalls[Abc_MinInt(iPool, 4)]++;
            pProf->nRootDivRouteRecipes[Abc_MinInt(iPool, 4)] +=
                nDepFound;
            if ( iPool > 0 )
                pProf->nRootDivAltCalls++;
            if ( iAttempt == 0 )
                fFirstPoolMiss = nDepFound == 0;
            nDepFoundBefore = nDepFoundTotal;
            nDepFoundTotal += nDepFound;
            for ( k = 0; k < nDepFound; k++ )
            {
                Cand = Cands[k];
                if ( iPool > 0 )
                {
                    Cand.nResubRank = iAttempt + k + 1;
                    Cand.fDivRescue = 1;
                    pProf->nRootDivAltRecipes++;
                }
                Cand.fPrimaryFrontier = iAttempt == 0 ||
                    (iAttempt <= 2 && nDepFoundBefore == 0 && k == 0);
                Cand.nWave = iWave;
                assert( Cand.nResubRank > 0 &&
                        Cand.nResubRank <= CEC_TRAN_RESUB_CHOICES_MAX );
                pProf->nRootResubGenerated[Cand.nResubRank - 1]++;
                if ( !Cec_TranCandVecContains(pTried, &Cand) &&
                     !Cec_TranCandVecContains(pExist, &Cand) &&
                     !Cec_TranCandVecContainsRange(pConstr,
                         iConstrStart, &Cand) )
                {
                    // Every strict-root divisor was collected outside this
                    // MFFC.  A safe isolated-gain lower bound is therefore
                    // MFFC minus the recipe's upper-bound AND cost; hashing
                    // can only make the committed result better.
                    Cand.Gain = Cand.nMffc - Cand.nGates;
                    pStat->nSigMatched++;
                    Cec_TranCandVecPush( pConstr, Cand );
                }
                else
                    pStat->nSigRejected++;
            }
            Vec_IntFree( vPool );
            // A successful legacy pool already supplied the strongest
            // candidate for this root.  Spend all additional q budget only
            // on roots which missed that frontier instead of enumerating
            // low-yield same-pool alternatives on the solved 35%.
            if ( iAttempt == 0 && nDepFound > 0 &&
                 !fKeepLegacyChoices )
                break;
        }
        assert( nDepFoundTotal <= CEC_TRAN_RESUB_CHOICES_MAX );
        pProf->nRootDepYield[nDepFoundTotal]++;
        pProf->nRootWaveDepCalls[iWave]++;
        pProf->nRootWaveRecipes[iWave] += nDepFoundTotal;
        if ( nDepFoundTotal == 0 )
            pStat->nSigRejected++;
        pProf->nRootDepCalls++;
        pProf->nRootDepFound += nDepFoundTotal > 0;
        pProf->nRootDepRecipes += nDepFoundTotal;
        pProf->nRootDivAltRescues += fFirstPoolMiss && nDepFoundTotal > 0;
        pHadRecipe[pRoots[r].iObj] |= nDepFoundTotal > 0;

        // Each search is choice-ranked by the resub engine; the candidate
        // vector above also removes duplicates across split/pool calls.  Keep
        // at most -q without re-enumerating arbitrary divisor tuples here.
        Cec_TranDiscFinishRoot( pStat, 0,
            pConstr->nSize - iConstrStart );
        ABC_FREE( pRanks );
        ABC_FREE( pUseCount );
        Vec_IntFree( vReservoir );
    }
}

static void Cec_TranCollectRootPhase( Gia_Man_t * p,
    Cec_TranSim_t * pSim, Cec_ParTran_t * pPars,
    Cec_TranRoot_t * pRoots, int nRoots, int iWave,
    Cec_TranSigEnt_t * pSigIndex, int nSigEntries,
    Cec_TranCandVec_t const * pTried, char const * pSolved,
    char * pHadRecipe,
    char * pMffc, Vec_Int_t * vMffc, int fExistingPhase,
    Cec_TranCandVec_t * pExist,
    Cec_TranCandVec_t * pConstr, Cec_TranCandVec_t * pAll,
    Cec_TranDepScratch_t * pDep, Cec_TranDiscStat_t * pStat,
    Cec_TranProf_t * pProf )
{
    int i;
    Cec_TranCandVecClear( pExist );
    Cec_TranCandVecClear( pConstr );
    Cec_TranCandVecClear( pAll );
    if ( fExistingPhase )
        Cec_TranCollectStrictExisting( p, pSim, pPars, pRoots, nRoots,
            pSigIndex, nSigEntries, pTried, pSolved, pMffc, vMffc,
            pExist, pStat, pProf );
    if ( pPars->fUseConstr )
        Cec_TranCollectStrictConstructed( p, pSim, pPars, pRoots, nRoots, iWave,
            pSigIndex, nSigEntries, pTried, pSolved, pHadRecipe,
            pMffc, vMffc, pExist, pConstr, pDep, pStat, pProf );
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
    char * pMffc, Vec_Int_t * vMffc,
    Cec_TranCandVec_t * pExist, Cec_TranCandVec_t * pConstr,
    Cec_TranDepScratch_t * pDep, Cec_TranDiscStat_t * pStat,
    Cec_TranProf_t * pProf )
{
    int k, nDepFound;
    int iExistStart = pExist->nSize, iConstrStart = pConstr->nSize;
    Vec_Int_t * vPool;
    Cec_TranCand_t Cand, Cands[CEC_TRAN_RESUB_CHOICES_MAX];
    word * pCare;
    abctime clk = Abc_Clock();
    vPool = Cec_TranCollectDivPool( p, pRoot->iObj,
        pPars->nConstrMax, pPars->nConstrBaseMax, pMffc, vMffc );
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
    nDepFound = Cec_TranComputeDependencies(pSim, pPars, pRoot,
        vPool, pCare, 0,
        Cands, pPars->nRootConstrTop, 0, pDep);
    for ( k = 0; k < nDepFound; k++ )
    {
        Cec_TranCandVec_t * pDest;
        int iStart;
        Cand = Cands[k];
        pStat->nSigMatched++;
        pDest = Cand.nGates ? pConstr : pExist;
        iStart = Cand.nGates ? iConstrStart : iExistStart;
        if ( !Cec_TranCandVecContains(pTried, &Cand) &&
             !Cec_TranCandVecContainsRange(pDest, iStart, &Cand) )
            Cec_TranCandVecPush( pDest, Cand );
        else
            pStat->nSigRejected++;
    }
    if ( nDepFound == 0 )
        pStat->nSigRejected++;
    pProf->timeConstruct += Abc_Clock() - clk;
    Cec_TranCandVecEvalSortTail( p, pExist, iExistStart, pProf );
    Cec_TranCandVecEvalSortTail( p, pConstr, iConstrStart, pProf );
    Cec_TranDiscFinishRoot( pStat, 1,
        pExist->nSize - iExistStart + pConstr->nSize - iConstrStart );
    ABC_FREE( pCare );
    Vec_IntFree( vPool );
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
    char * pRootSolved, * pRootHadRecipe;
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
    Abc_Print( 1, "Sequential direct resubstitution: stage=%s AND = %d, Reg = %d, random lanes = %d, sequential frames = %d, signature samples = %d, proof frames = %d, seq-conf = %d comb-conf = %d, proof scope = %s%s, root batch = %s, root search width = %d, root waves = %d, constructed mode = multi-resub/q%d, root scheduling = %s, contextual proof limit = %s, CEX batch = %d, TFI depth = %d, pool nodes = %d, dependency nodes = %d, unknown cooldown = low:%d/high:%d, global exact = %s, resub-zero = %s, dependency synthesis = %s, root CBS = %s, free-state=%s/%d words/%d cex.\n",
        pPars->nRootStage == 1 ? "comb-only" :
        pPars->nRootStage == 2 ? "seq-only" : "combined",
        Gia_ManAndNum(pGia), Gia_ManRegNum(pGia), pPars->nSimWords * 64,
        pPars->nSimFrames, pPars->nSimWords * 64 * pPars->nSimFrames,
        pPars->nFrames, pPars->nBTLimit, pPars->nCombBTLimit,
        pPars->nProofScope == CEC_TRAN_PROOF_ROOT ? "root" :
        pPars->nProofScope == CEC_TRAN_PROOF_WINDOW ? "window" : "output",
        pPars->nProofScope == CEC_TRAN_PROOF_WINDOW ? " (bounded TFO)" : "",
        pPars->nProofScope == CEC_TRAN_PROOF_ROOT ? "on" : "off",
        pPars->nRootBatch, pPars->nRootWaves, pPars->nRootConstrTop,
        pPars->fRootProgressive ? "bounded-per-root" : "all-at-once",
        pPars->nCandMax ? "bounded" : "unlimited",
        pPars->nCexBatch, pPars->nConstrMax, pPars->nConstrBaseMax,
        pPars->nDepNodesMax,
        pPars->nLowUnknownMax, pPars->nUnknownMax,
        pPars->fUseExisting ?
            (pPars->nProofScope == CEC_TRAN_PROOF_ROOT ?
                "large-MFFC-only" : "on") : "off",
        pPars->fUseResubZero ? "on" : "off",
        pPars->fUseConstr ? "on" : "off",
        pPars->fUseCbsMultiLit ? "multi-lit" : "xor-query",
        pPars->fUseFreeSim ? "on" : "off", pPars->nFreeWords,
        pPars->nFreeCexMax );
    Abc_Print( 1, "Sequential direct proof budgets: comb-conf=%d seq-conf=%d root-total=unlimited root-min-gain=%d root-existing-mffc=%d; context-low=%d/%d context-high=%d/%d context-high-gain=%d context-high-mffc=%d.\n",
        pPars->nCombBTLimit, pPars->nBTLimit,
        pPars->nRootGainMin, pPars->nHardMffc,
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
    pRootHadRecipe = ABC_CALLOC( char, Gia_ManObjNum(p) );
    do
    {
        Cec_TranCand_t Cand, Temp;
        Cec_TranDepScratch_t DepScratch;
        Cec_TranCandVec_t * pQueue = NULL;
        Vec_Int_t * vCommitMap = NULL;
        Vec_Int_t * vRootGroups = NULL;
        Vec_Int_t * vMffc = NULL;
        abctime * pRootLayerShare = NULL;
        int * pRootCandLayer = NULL;
        char * pRootWaveFailed = NULL;
        char * pCommitAffected = NULL;
        char * pMffc = NULL;
        int rContext = 0, iRootLayer = 0, nRootLayers = 0;
        int nRootNormalLayers = 0, nRootRescueLayers = 0;
        int fHaveSE, fHaveCE, fHaveCC;
        int fRootExistingPhase = 0;
        int nTriedOld, nAcceptedOld, nUnknownOld, nSatOld, iHist, fWasUnknown;
        int i, fFound, fCandCex, fNeedSigIndex;
        abctime timeUnknownOld, clkRound = Abc_Clock();
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
        Cec_TranDepScratchStart( &DepScratch, pSim->nSlots,
            pPars->nConstrBaseMax ? pPars->nConstrBaseMax : 64 );
        pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
        vMffc = Vec_IntAlloc( 128 );

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
        // Root construction uses the same index as a failure-only direct
        // divisor route.  Build it once in the initial root phase; later CEX
        // waves keep their narrower multi-route reservoirs.
        if ( pPars->nProofScope == CEC_TRAN_PROOF_ROOT &&
             !fRootExistingDone &&
             (pPars->fUseExisting || pPars->fUseConstr) )
            fNeedSigIndex = 1;
        if ( fNeedSigIndex )
            pSigIndex = Cec_TranBuildSigIndex( pSim, &nSigEntries );
        if ( pPars->fProfile )
            Prof.timeSpec += Abc_Clock() - clkPhase, Prof.nSpecCalls++;
        // The initial root wave contains constants, the restricted existing
        // lane, and bounded resub recipes per root.  Progressive mode keeps
        // legacy, failure-pool, and audit layers separate.  A later
        // reachable-CEX wave contains only new constructed recipes.
        if ( pPars->nProofScope == CEC_TRAN_PROOF_ROOT )
        {
            // -L is a generation cap, not merely a proof-queue cap: do not
            // build divisor pools or dependency recipes for lower-ranked roots
            // that cannot enter the current phase.
            fRootExistingPhase = !fRootExistingDone;
            Cec_TranCollectRootPhase( p, pSim, pPars, pRoots,
                pPars->nRootBatch ? Abc_MinInt(nRoots, pPars->nRootBatch) : nRoots,
                nRound,
                pSigIndex, nSigEntries, &vTried, pRootSolved,
                pRootHadRecipe, pMffc, vMffc, fRootExistingPhase,
                &qStrictExist, &qStrictConstr,
                &qStrictAll, &DepScratch, &Disc, &Prof );
            if ( fRootExistingPhase )
                fRootExistingDone = 1;
            if ( qStrictAll.nSize )
                Prof.nRootSnapshots++;
            if ( pPars->fRootProgressive && qStrictAll.nSize )
            {
                vRootGroups = Cec_TranCandBuildRootGroups(
                    &qStrictAll, &nRootNormalLayers,
                    &nRootRescueLayers );
                // Keep the legacy candidates in their original q layers.
                // Failure-pool candidates run only afterward, so they cannot
                // perturb the shared proof batch which established the q=1/q3
                // baseline on roots that already had recipes.
                {
                    int nLayerTop =
                        (long long)nRoots * pPars->nRootConstrTop <= 20000 ?
                            pPars->nRootConstrTop : 1;
                    nRootNormalLayers = Abc_MinInt( nRootNormalLayers,
                        nLayerTop );
                    nRootRescueLayers = Abc_MinInt( nRootRescueLayers,
                        nLayerTop );
                }
                // Repeat both layer classes as an audit pass.  Candidates
                // already submitted are removed by vTried; only alternatives
                // skipped after another candidate solved their root remain.
                nRootLayers = 2 * (nRootNormalLayers + nRootRescueLayers);
                if ( nRound + 1 < pPars->nRootWaves )
                {
                    pRootWaveFailed = ABC_CALLOC( char, qStrictAll.nSize );
                    pRootLayerShare = ABC_CALLOC( abctime, nRootLayers );
                    pRootCandLayer = ABC_FALLOC( int, qStrictAll.nSize );
                }
            }
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
                            &vTried, pMffc, vMffc,
                            &qContextExist, &qContextConstr,
                            &DepScratch, &Disc, &Prof );
                    else
                        nCooldownSkipped++;
                    rContext++;
                }
            }

            fHaveSE = pPars->nProofScope == CEC_TRAN_PROOF_ROOT &&
                (pPars->fRootProgressive ?
                    vRootGroups && iRootLayer < nRootLayers :
                    qStrictAll.iHead < qStrictAll.nSize);
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
                Vec_Int_t * vBatchOrig = pRootWaveFailed ?
                    Vec_IntAlloc( Vec_IntSize(vRootGroups) / 2 ) : NULL;
                Vec_Int_t * vBatchStatus;
                Vec_Str_t * vBatchStage;
                int iBatch, iLayerThis = -1;
                int iRootPhase = fRootExistingPhase ? 0 : 1;
                int Gain, fRootCex = 0, iRootCex = -1;
                int nRootScreenedNow = 0;
                abctime clkBatch, timeBatch, timeShare;
                if ( pPars->fRootProgressive )
                {
                    int iGroup, iGroupBeg, iGroupEnd, iCandPos;
                    iLayerThis = iRootLayer++;
                    for ( iGroup = 0; iGroup < Vec_IntSize(vRootGroups);
                          iGroup += 2 )
                    {
                        iGroupBeg = Vec_IntEntry( vRootGroups, iGroup );
                        iGroupEnd = Vec_IntEntry( vRootGroups, iGroup + 1 );
                        iCandPos = Cec_TranCandRootGroupLayerPos(
                            &qStrictAll, iGroupBeg, iGroupEnd,
                            iLayerThis, nRootNormalLayers,
                            nRootRescueLayers );
                        if ( iCandPos < 0 )
                            continue;
                        Cand = qStrictAll.pArray[iCandPos];
                        Cand.nSchedRank = iLayerThis + 1;
                        if ( iLayerThis == 0 )
                            Prof.nRootScreened++;
                        // The first pass preserves legacy solved-root
                        // skipping and therefore its shared proof context.
                        // The repeated audit pass proves only alternatives
                        // skipped by that rule, for exact portfolio choice.
                        if ( iLayerThis < nRootNormalLayers +
                             nRootRescueLayers &&
                             pRootSolved[Cand.iTarget] )
                            continue;
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
                        if ( vBatchOrig )
                        {
                            Vec_IntPush( vBatchOrig, iCandPos );
                            pRootCandLayer[iCandPos] = iLayerThis;
                        }
                    }
                }
                else
                {
                    // qStrictAll is grouped in MFFC order.  Retain every
                    // already capped construction candidate so its relation
                    // participates in the same stronger equivalence-class
                    // hypothesis.
                    while ( qStrictAll.iHead < qStrictAll.nSize &&
                           (!pPars->nRootBatch || nRootScreenedNow < pPars->nRootBatch) )
                    {
                        int iTarget = qStrictAll.pArray[qStrictAll.iHead].iTarget;
                        int iRootAlt = 0;
                        nRootScreenedNow++;
                        Prof.nRootScreened++;
                        while ( qStrictAll.iHead < qStrictAll.nSize &&
                                qStrictAll.pArray[qStrictAll.iHead].iTarget == iTarget )
                        {
                            int iCandPos = qStrictAll.iHead++;
                            Cand = qStrictAll.pArray[iCandPos];
                            Cand.nSchedRank = ++iRootAlt;
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
                }
                if ( Batch.nSize == 0 )
                {
                    Vec_IntFreeP( &vBatchOrig );
                    Cec_TranCandVecStop( &Batch );
                    if ( pPars->fRootProgressive )
                        continue;
                    break;
                }
                if ( !pPars->fRootProgressive )
                    qsort( Batch.pArray, Batch.nSize, sizeof(Cec_TranCand_t),
                        Cec_TranCandPriorityCompare );
                for ( iBatch = 0; iBatch < Batch.nSize; iBatch++ )
                {
                    Cand = Batch.pArray[iBatch];
                    Prof.nRootWaveSubmitted[nRound]++;
                    if ( Cand.nResubRank )
                        Prof.nRootResubSubmitted[Cand.nResubRank - 1]++;
                    if ( Cand.fDivRescue )
                        Prof.nRootDivAltSubmitted++;
                    if ( Cand.fDivGlobal )
                        Prof.nRootDivGlobalSubmitted++;
                    if ( Cand.nSchedRank &&
                         Cand.nSchedRank <= CEC_TRAN_ROOT_ALT_PROFILE_MAX )
                        Prof.nRootLayerSubmitted[Cand.nSchedRank - 1]++;
                    Cec_TranCandVecPush( &vTried, Cand );
                    nTried++;
                    nStrictProofs++;
                    if ( Cand.nKind == CEC_TRAN_CAND_CONST )
                        nConstantProofs++;
                    else if ( Cand.nKind == CEC_TRAN_CAND_EXIST )
                    {
                        nExistingProofs++;
                        if ( Cand.nResubRank )
                            Prof.nRootExistingResubProofs++;
                        else
                            Prof.nRootExistingGlobalProofs++;
                    }
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
                Prof.timeRootWaveProof[nRound] += timeBatch;
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
                        Prof.nRootWaveProved[nRound]++;
                        if ( Batch.pArray[iBatch].fDivRescue )
                            Prof.nRootDivAltProved++;
                        if ( Batch.pArray[iBatch].fDivGlobal )
                            Prof.nRootDivGlobalProved++;
                        if ( Batch.pArray[iBatch].nResubRank )
                        {
                            int iRank = Batch.pArray[iBatch].nResubRank - 1;
                            if ( Batch.pArray[iBatch].nProofStage == 1 )
                                Prof.nRootResubCombProved[iRank]++;
                            else
                                Prof.nRootResubSeqProved[iRank]++;
                        }
                        if ( Batch.pArray[iBatch].nSchedRank &&
                             Batch.pArray[iBatch].nSchedRank <=
                                CEC_TRAN_ROOT_ALT_PROFILE_MAX )
                            Prof.nRootLayerProved[
                                Batch.pArray[iBatch].nSchedRank - 1]++;
                        Prof.nRootPhaseProved[iRootPhase]++;
                        pRootSolved[Batch.pArray[iBatch].iTarget] = 1;
                        if ( !Cec_TranCandVecContains(&qRootProved,
                                Batch.pArray + iBatch) )
                        {
                            int iStage =
                                Batch.pArray[iBatch].nProofStage == 1 ? 0 : 1;
                            int iKind = Batch.pArray[iBatch].nKind;
                            Prof.nStageKindProved[iStage][iKind]++;
                            if ( iKind == CEC_TRAN_CAND_CONSTR )
                            {
                                Prof.nStageConstructProvedGates[iStage] +=
                                    Batch.pArray[iBatch].nGates;
                                Prof.nStageConstructProvedMaxGates[iStage] =
                                    Abc_MaxInt(
                                        Prof.nStageConstructProvedMaxGates[iStage],
                                        Batch.pArray[iBatch].nGates );
                            }
                            Cec_TranCandVecPush( &qRootProved,
                                Batch.pArray[iBatch] );
                        }
                    }

                if ( pRootWaveFailed )
                {
                    pRootLayerShare[iLayerThis] = timeShare;
                    for ( iBatch = 0; iBatch < Batch.nSize; iBatch++ )
                        if ( !Vec_IntEntry(vBatchStatus, iBatch) )
                            pRootWaveFailed[Vec_IntEntry(vBatchOrig, iBatch)] = 1;
                }

                // Only a reset-reachable witness may guide another construct
                // wave.  There is no point harvesting after the configured
                // final wave, or for roots already solved by another class
                // member in this closure.
                if ( !pPars->fRootProgressive &&
                     nRound + 1 < pPars->nRootWaves )
                    fRootCex = Cec_TranHarvestRootWaveCex( p,
                        Batch.pArray, vBatchStatus, NULL, Batch.nSize, pRootSolved,
                        pPars, pDb, &Prof, &iRootCex );
                for ( iBatch = 0; iBatch < Batch.nSize; iBatch++ )
                {
                    if ( Vec_IntEntry(vBatchStatus, iBatch) )
                    {
                        Prof.nProofUnsat++;
                        Prof.timeProofUnsat += timeShare;
                    }
                    else if ( !pPars->fRootProgressive &&
                              iBatch == iRootCex )
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
                Vec_IntFreeP( &vBatchOrig );
                Cec_TranCandVecStop( &Batch );
                if ( pPars->fRootProgressive )
                    continue;
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

        // Progressive root scheduling deliberately exhausts the cached
        // alternative layers on this immutable simulation snapshot before
        // asking for a new reachable witness.  The byte mask marks only
        // attempted failures; roots solved by a later layer are filtered
        // inside the harvester.
        if ( pPars->nProofScope == CEC_TRAN_PROOF_ROOT &&
             pPars->fRootProgressive && pRootWaveFailed &&
             nRound + 1 < pPars->nRootWaves )
        {
            int iRootCex = -1;
            int fRootCex = Cec_TranHarvestRootWaveCex( p,
                qStrictAll.pArray, NULL, pRootWaveFailed, qStrictAll.nSize,
                pRootSolved, pPars, pDb, &Prof, &iRootCex );
            if ( fRootCex )
            {
                if ( iRootCex >= 0 )
                {
                    int iLayer = pRootCandLayer[iRootCex];
                    assert( iLayer >= 0 && iLayer < nRootLayers );
                    abctime Share = pRootLayerShare[iLayer];
                    assert( Prof.nProofUnknown > 0 && Prof.nUnknownFirst > 0 );
                    Prof.nProofUnknown--;
                    Prof.nUnknownFirst--;
                    Prof.timeProofUnknown -= Share;
                    Prof.timeUnknownFirst -= Share;
                    Prof.nProofSat++;
                    Prof.timeProofSat += Share;
                }
                Cec_TranPatDbSealPending( pDb );
                Prof.nCegisRestarts++;
                Prof.nCexSigRefreshes++;
                fCegisRestart = 1;
            }
        }

        Vec_IntFreeP( &vRootGroups );
        Vec_IntFree( vMffc );
        ABC_FREE( pMffc );
        ABC_FREE( pRootWaveFailed );
        ABC_FREE( pRootLayerShare );
        ABC_FREE( pRootCandLayer );
        ABC_FREE( pRoots );
        ABC_FREE( pSigIndex );
        Cec_TranDepScratchStop( &DepScratch );
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
            int nKindAnds[8], nKindRegs[8];
            long long nStageKindAndGain[2][8];
            long long nStageKindRegGain[2][8];
            int nRank1Ands = -1, nRank1Regs = -1;
            int nWave1Ands = -1, nWave1Regs = -1;
            int nNoGlobalExistAnds = -1, nNoResubExistAnds = -1;
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
            if ( pPars->fProfile )
            {
                clkCand = Abc_Clock();
                Cec_TranRootContributionCost( p, qRootProved.pArray,
                    vAllProved, qRootProved.nSize, nSelectMax,
                    nKindAnds, nKindRegs,
                    &nRank1Ands, &nRank1Regs,
                    &nWave1Ands, &nWave1Regs,
                    &nNoGlobalExistAnds, &nNoResubExistAnds );
                Cec_TranRootStageContributionCost( p,
                    qRootProved.pArray, vAllProved, qRootProved.nSize,
                    nSelectMax, nAndAfterComb, nRegAfterComb,
                    nStageKindAndGain, nStageKindRegGain );
                Prof.timeRootKindContribution += Abc_Clock() - clkCand;
            }
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
                    Cec_TranCand_t const * pSelected =
                        qRootProved.pArray + iSelected;
                    int iStage = pSelected->nProofStage == 1 ? 0 : 1;
                    Prof.nStageKindSelected[iStage][pSelected->nKind]++;
                    if ( pSelected->nKind == CEC_TRAN_CAND_CONSTR )
                    {
                        Prof.nStageConstructSelectedGates[iStage] +=
                            pSelected->nGates;
                        Prof.nStageConstructSelectedMaxGates[iStage] =
                            Abc_MaxInt(
                                Prof.nStageConstructSelectedMaxGates[iStage],
                                pSelected->nGates );
                    }
                    Prof.nRootWaveSelected[pSelected->nWave]++;
                    if ( pSelected->nResubRank )
                        Prof.nRootResubSelected[pSelected->nResubRank - 1]++;
                    if ( pSelected->fDivRescue )
                        Prof.nRootDivAltSelected++;
                    if ( pSelected->fDivGlobal )
                        Prof.nRootDivGlobalSelected++;
                    if ( pSelected->nSchedRank &&
                         pSelected->nSchedRank <= CEC_TRAN_ROOT_ALT_PROFILE_MAX )
                        Prof.nRootLayerSelected[pSelected->nSchedRank - 1]++;
                    if ( qRootProved.pArray[iSelected].nProofStage == 1 )
                        Prof.nCombSelected++;
                    else
                        Prof.nSeqSelected++;
                    if ( qRootProved.pArray[iSelected].nKind ==
                         CEC_TRAN_CAND_CONST )
                        nConstantAccepted++;
                    else if ( qRootProved.pArray[iSelected].nKind ==
                              CEC_TRAN_CAND_EXIST )
                    {
                        nExistingAccepted++;
                        if ( pSelected->nResubRank )
                            Prof.nRootExistingResubSelected++;
                        else
                            Prof.nRootExistingGlobalSelected++;
                    }
                    else
                        nConstructedAccepted++;
                }
                Prof.nRootBundleAndGain += nAndOld - Gia_ManAndNum(p);
                Prof.nRootBundleRegGain += nRegOld - Gia_ManRegNum(p);
                if ( pPars->fProfile )
                {
                    int Mask, Stage;
                    nStageKindAndGain[1][7] =
                        nAndAfterComb - Gia_ManAndNum(p);
                    nStageKindRegGain[1][7] =
                        nRegAfterComb - Gia_ManRegNum(p);
                    for ( Mask = 1; Mask < 7; Mask++ )
                    {
                        Prof.nRootKindSubsetAndGain[Mask] +=
                            nAndOld - nKindAnds[Mask];
                        Prof.nRootKindSubsetRegGain[Mask] +=
                            nRegOld - nKindRegs[Mask];
                    }
                    Prof.nRootKindSubsetAndGain[7] +=
                        nAndOld - Gia_ManAndNum(p);
                    Prof.nRootKindSubsetRegGain[7] +=
                        nRegOld - Gia_ManRegNum(p);
                    for ( Stage = 0; Stage < 2; Stage++ )
                    for ( Mask = 1; Mask < 8; Mask++ )
                    {
                        Prof.nStageKindSubsetAndGain[Stage][Mask] +=
                            nStageKindAndGain[Stage][Mask];
                        Prof.nStageKindSubsetRegGain[Stage][Mask] +=
                            nStageKindRegGain[Stage][Mask];
                    }
                    Prof.nRootRank1AndGain += nRank1Ands < 0 ?
                        nAndOld - Gia_ManAndNum(p) : nAndOld - nRank1Ands;
                    Prof.nRootRank1RegGain += nRank1Regs < 0 ?
                        nRegOld - Gia_ManRegNum(p) : nRegOld - nRank1Regs;
                    Prof.nRootWave1AndGain += nWave1Ands < 0 ?
                        nAndOld - Gia_ManAndNum(p) : nAndOld - nWave1Ands;
                    Prof.nRootWave1RegGain += nWave1Regs < 0 ?
                        nRegOld - Gia_ManRegNum(p) : nRegOld - nWave1Regs;
                    Prof.nRootExistingGlobalLeaveoutAndGain +=
                        nNoGlobalExistAnds < 0 ? 0 :
                        (nAndOld - Gia_ManAndNum(p)) -
                        (nAndOld - nNoGlobalExistAnds);
                    Prof.nRootExistingResubLeaveoutAndGain +=
                        nNoResubExistAnds < 0 ? 0 :
                        (nAndOld - Gia_ManAndNum(p)) -
                        (nAndOld - nNoResubExistAnds);
                }
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
        if ( pPars->nProofScope == CEC_TRAN_PROOF_ROOT )
        {
            assert( nRound < 64 );
            Prof.timeRootWaveTotal[nRound] += Abc_Clock() - clkRound;
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
            nConstantAccepted, nExistingAccepted, nConstructedAccepted,
            pPars->fUseCbsMultiLit, pPars->fRootProgressive,
            pPars->nRootWaves );
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
    ABC_FREE( pRootHadRecipe );
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
    Gia_Man_t * pComb, * pSeq;
    Cec_ParTran_t CombPars, SeqPars;
    // This branch exposes Direct root replacement with an explicit proof
    // scope.  Keep the legacy leaf-SODC implementation above isolated until
    // it is split into a separate command or branch.
    assert( pPars->fUseDirect && !pPars->fUseSodc );
    if ( pPars->nProofScope == CEC_TRAN_PROOF_ROOT &&
         pPars->fRootSplitStages && pPars->nRootStage == 0 )
    {
        CombPars = SeqPars = *pPars;
        CombPars.nRootStage = 1;
        // Reachable CEGAR belongs to the temporal pass.  The combination pass
        // learns arbitrary-state CBS models inside each proof batch instead.
        CombPars.nRootWaves = 1;
        SeqPars.nRootStage = 2;
        SeqPars.fUseFreeSim = 0;
        // Keep the combination lane in one batch so random signatures and
        // learned CBS models are shared across all alternatives.  The scheduling
        // mode applies to the rebuilt sequential lane: false seeds every
        // retained alternative in one scorr closure; true seeds up to q/root.
        CombPars.fRootProgressive = 0;
        SeqPars.fRootProgressive = pPars->fRootProgressive;
        Abc_Print( 1, "Sequential direct split-stage profile: begin AND=%d Reg=%d comb-conf=%d seq-conf=%d free-words=%d free-cex=%d seq-scheduling=%s.\n",
            Gia_ManAndNum(pGia), Gia_ManRegNum(pGia),
            CombPars.nCombBTLimit, SeqPars.nBTLimit,
            CombPars.nFreeWords, CombPars.nFreeCexMax,
            SeqPars.fRootProgressive ? "top-q/root" : "all-alternatives" );
        pComb = Cec_ManSequentialDirectResubstitution( pGia, &CombPars );
        pSeq = Cec_ManSequentialDirectResubstitution( pComb, &SeqPars );
        Abc_Print( 1, "Sequential direct split-stage size profile: AND=%d -> comb=%d (gain=%d) -> scorr=%d (incremental-gain=%d); Reg=%d -> comb=%d -> scorr=%d.\n",
            Gia_ManAndNum(pGia), Gia_ManAndNum(pComb),
            Gia_ManAndNum(pGia) - Gia_ManAndNum(pComb),
            Gia_ManAndNum(pSeq), Gia_ManAndNum(pComb) - Gia_ManAndNum(pSeq),
            Gia_ManRegNum(pGia), Gia_ManRegNum(pComb), Gia_ManRegNum(pSeq) );
        Gia_ManStop( pComb );
        return pSeq;
    }
    return Cec_ManSequentialDirectResubstitution( pGia, pPars );
}

ABC_NAMESPACE_IMPL_END
