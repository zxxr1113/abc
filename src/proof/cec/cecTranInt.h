// Shared internal types and profiling state.
// Private implementation fragment included only by cecTrans.c.

// COM is deliberately independent of the SEQ q/j experiment.  Arbitrary-
// state certificates do not use retained induction helpers, so COM submits
// one modest frontier and commits it immediately instead of accumulating
// proof micro-batches on the initial graph.
#define CEC_TRAN_COMB_BUILD_Q 4
#define CEC_TRAN_BUILD_OUTCOMES 3
#define CEC_TRAN_BUILD_RANK_BINS 8
#define CEC_TRAN_BUILD_GATE_BINS 6
#define CEC_TRAN_BUILD_GAIN_BINS 6
#define CEC_TRAN_BUILD_DIVRANK_BINS 6
#define CEC_TRAN_BUILD_MFFC_BINS 6
#define CEC_TRAN_BUILD_SUPPORT_SIZE_BINS 6
#define CEC_TRAN_BUILD_SUPPORT_MULT_BINS 6
#define CEC_TRAN_BUILD_SUPPORT_RATIO_BINS 5
#define CEC_TRAN_BUILD_RESIDUAL_SAMPLE_RATE 32
#define CEC_TRAN_BUILD_RESIDUAL_SAMPLE_VALUES 8
#define CEC_TRAN_BUILD_RESIDUAL_DEPTH_BINS 6
#define CEC_TRAN_BUILD_RESIDUAL_SIZE_BINS 7
#define CEC_TRAN_PIVOT_RANK_BINS 8
#define CEC_TRAN_PIVOT_RATIO_BINS 5
#define CEC_TRAN_PIVOT_KIND_BINS 2
#define CEC_TRAN_MULTIPATH_RANK_BINS 9
#define CEC_TRAN_MULTIPATH_PATH_BINS 4
#define CEC_TRAN_MULTIPATH_CELLS \
    (CEC_TRAN_MULTIPATH_RANK_BINS * CEC_TRAN_MULTIPATH_PATH_BINS)

// Shared fixed-layout payload returned by giaResub.c.  Counts cover every
// greedy pivot consumed inside one Next(), including pivots whose recursive
// remainder failed and therefore never became a candidate.
enum
{
    CEC_TRAN_PIVOT_FRONTIER_FIRST = 0,
    CEC_TRAN_PIVOT_FRONTIER_SIZE,
    CEC_TRAN_PIVOT_FRONTIER_UNIQUE,
    CEC_TRAN_PIVOT_FRONTIER_ZERO_NOVEL,
    CEC_TRAN_PIVOT_FRONTIER_COVER_SUM,
    CEC_TRAN_PIVOT_FRONTIER_NOVEL_SUM,
    CEC_TRAN_PIVOT_ATTEMPT_TOTAL,
    CEC_TRAN_PIVOT_FOUND_TOTAL,
    CEC_TRAN_PIVOT_TIME_TOTAL,
    CEC_TRAN_PIVOT_SCHED_FRONTIERS,
    CEC_TRAN_PIVOT_SCHED_PIVOTS,
    CEC_TRAN_PIVOT_SCHED_COMPLETE,
    CEC_TRAN_PIVOT_SCHED_TIME,
    CEC_TRAN_CACHE_LOOKUPS,
    CEC_TRAN_CACHE_HITS,
    CEC_TRAN_CACHE_MISSES,
    CEC_TRAN_CACHE_SAME_PAGE_HITS,
    CEC_TRAN_CACHE_CROSS_PAGE_HITS,
    CEC_TRAN_CACHE_FAIL_HITS,
    CEC_TRAN_CACHE_SUCCESS_HITS,
    CEC_TRAN_CACHE_SAVED_TIME,
    CEC_TRAN_CACHE_LOOKUP_TIME,
    CEC_TRAN_CACHE_PAYLOAD_BYTES,
    CEC_TRAN_REC_CALLS,
    CEC_TRAN_REC_UNIQUE,
    CEC_TRAN_REC_DUPLICATE,
    CEC_TRAN_REC_SAME_PAGE,
    CEC_TRAN_REC_CROSS_PAGE,
    CEC_TRAN_REC_FAIL_HITS,
    CEC_TRAN_REC_SUCCESS_DUPLICATE,
    CEC_TRAN_REC_PAYLOAD_BYTES,
    CEC_TRAN_REC_SAVED_TIME,
    CEC_TRAN_REC_LOOKUP_TIME,
    CEC_TRAN_REC_DUP_DEPTH_0,
    CEC_TRAN_REC_DUP_DEPTH_1,
    CEC_TRAN_REC_DUP_DEPTH_2,
    CEC_TRAN_REC_DUP_DEPTH_3PLUS,
    CEC_TRAN_MULTIPATH_CACHE_ENTRIES,
    CEC_TRAN_MULTIPATH_CACHE_LOOKUPS,
    CEC_TRAN_MULTIPATH_CACHE_HITS,
    CEC_TRAN_MULTIPATH_CACHE_FAIL_HITS,
    CEC_TRAN_MULTIPATH_CACHE_SUCCESS_HITS,
    CEC_TRAN_MULTIPATH_CACHE_PAYLOAD_BYTES,
    CEC_TRAN_MULTIPATH_ATTEMPTS,
    CEC_TRAN_MULTIPATH_FOUND = CEC_TRAN_MULTIPATH_ATTEMPTS +
        CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_MULTIPATH_TIME = CEC_TRAN_MULTIPATH_FOUND +
        CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_MULTIPATH_SECOND_COVER = CEC_TRAN_MULTIPATH_TIME +
        CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_MULTIPATH_DIVERSITY_NEW =
        CEC_TRAN_MULTIPATH_SECOND_COVER + CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_MULTIPATH_DIVERSITY_SYM =
        CEC_TRAN_MULTIPATH_DIVERSITY_NEW + CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_PIVOT_CURRENT_PATH = CEC_TRAN_MULTIPATH_DIVERSITY_SYM +
        CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_PIVOT_CURRENT_SECOND_RANK,
    CEC_TRAN_PIVOT_CURRENT_SECOND_COVER,
    CEC_TRAN_PIVOT_CURRENT_DIVERSITY_NEW,
    CEC_TRAN_PIVOT_CURRENT_DIVERSITY_SYM,
    CEC_TRAN_PIVOT_CURRENT_VALID,
    CEC_TRAN_PIVOT_CURRENT_KIND,
    CEC_TRAN_PIVOT_CURRENT_RANK,
    CEC_TRAN_PIVOT_CURRENT_COVER,
    CEC_TRAN_PIVOT_CURRENT_TOTAL,
    CEC_TRAN_PIVOT_CURRENT_NOVEL,
    CEC_TRAN_PIVOT_CURRENT_REMAIN,
    CEC_TRAN_PIVOT_CURRENT_DUPLICATE,
    CEC_TRAN_PIVOT_RANK_ATTEMPTS,
    CEC_TRAN_PIVOT_RANK_FOUND = CEC_TRAN_PIVOT_RANK_ATTEMPTS +
        CEC_TRAN_PIVOT_RANK_BINS,
    CEC_TRAN_PIVOT_RANK_TIME = CEC_TRAN_PIVOT_RANK_FOUND +
        CEC_TRAN_PIVOT_RANK_BINS,
    CEC_TRAN_PIVOT_NOVEL_ATTEMPTS = CEC_TRAN_PIVOT_RANK_TIME +
        CEC_TRAN_PIVOT_RANK_BINS,
    CEC_TRAN_PIVOT_NOVEL_FOUND = CEC_TRAN_PIVOT_NOVEL_ATTEMPTS +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_NOVEL_TIME = CEC_TRAN_PIVOT_NOVEL_FOUND +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_COVER_ATTEMPTS = CEC_TRAN_PIVOT_NOVEL_TIME +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_COVER_FOUND = CEC_TRAN_PIVOT_COVER_ATTEMPTS +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_COVER_TIME = CEC_TRAN_PIVOT_COVER_FOUND +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_KIND_ATTEMPTS = CEC_TRAN_PIVOT_COVER_TIME +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_KIND_FOUND = CEC_TRAN_PIVOT_KIND_ATTEMPTS +
        CEC_TRAN_PIVOT_KIND_BINS,
    CEC_TRAN_PIVOT_KIND_TIME = CEC_TRAN_PIVOT_KIND_FOUND +
        CEC_TRAN_PIVOT_KIND_BINS,
    CEC_TRAN_PIVOT_STATE_ATTEMPTS = CEC_TRAN_PIVOT_KIND_TIME +
        CEC_TRAN_PIVOT_KIND_BINS,
    CEC_TRAN_PIVOT_STATE_FOUND = CEC_TRAN_PIVOT_STATE_ATTEMPTS + 2,
    CEC_TRAN_PIVOT_STATE_TIME = CEC_TRAN_PIVOT_STATE_FOUND + 2,
    CEC_TRAN_PIVOT_PROFILE_SIZE = CEC_TRAN_PIVOT_STATE_TIME + 2
};

enum
{
    CEC_TRAN_CAND_CONST = 0,
    CEC_TRAN_CAND_EXIST = 1,
    CEC_TRAN_CAND_CONSTR = 2
};
enum
{
    CEC_TRAN_STATE_CANDIDATE = 0,
    CEC_TRAN_STATE_STALE,
    CEC_TRAN_STATE_TRIED_SEQ,
    CEC_TRAN_STATE_PROVED_COMB,
    CEC_TRAN_STATE_PROVED_SEQ,
    CEC_TRAN_STATE_SELECTED
};

extern void Abc_ResubPrepareManager( int nWords );
extern void Abc_ResubSetBothPolarities( int Enable );
extern void * Abc_ResubIteratorResumeStart( void ** ppDivs, int nDivs,
    int nWords, int nLimit, int nDivsMax, int fUseZero, int fUseXor,
    int fUseSolvSched, int nStage5Paths, int fProfilePivots, int * pCursor,
    void ** ppRootCache );
extern void Abc_ResubRootCacheStop( void * pRootCache );
extern int Abc_ResubIteratorNext( void * pIter, int ** ppArray,
    int * pnAttempt, int * pfExhausted, int * pfInvalid );
extern int Abc_ResubIteratorReadPivotProfile( void * pIter,
    long long * pProfile );
extern void Abc_ResubIteratorResumeStop( void * pIter, int * pCursor );
extern int Abc_ResubIteratorSelfTest();

static int Cec_TranCanonicalizeSelfTest();
static int Cec_TranMffcSelfTest();
static int Cec_TranFrontierGainSelfTest();
static int Cec_TranPipelineSelfTest();
static int Cec_TranCommitWaveSelfTest();
static int Cec_TranProofMicroBatchSelfTest();
static int Cec_TranObservationSelfTest();
static int Cec_TranExactCoreSelfTest();
static int Cec_TranCompleteFaninTfoSelfTest();
static int Cec_TranWindowSelfTest();
static int Cec_TranFirstLevelCareSelfTest();
static int Cec_TranOdcRootCareSelfTest();
static int Cec_TranOdcFanoutSelfTest();
static int Cec_TranOdcDirectSelfTest();
static int Cec_TranCareIsfSelfTest();
static int Cec_TranSigGuideSelfTest();
static int Cec_TranStrictCexSelfTest();
static int Cec_TranStrictCexActiveSelfTest();
static int Cec_TranStrictGuideSelfTest();
static int Cec_TranRelObsSelfTest();
static int Cec_TranTraceBuildSelfTest();
typedef struct Cec_TranTfoStats_t_ Cec_TranTfoStats_t;
struct Cec_TranTfoStats_t_
{
    long long nSeeds;
    long long nScanned;
    long long nEdges;
    long long nAdded;
    int       fLimit;
    abctime   Time;
};
static Vec_Int_t * Cec_TranCollectDivPool( Gia_Man_t * p, int iTarget,
    int nDepthMax, int nNodesMax, int fUseMffcDivs,
    char const * pCovered, char const * pUsed,
    char * pMffc, Vec_Int_t * vMffc, int fUseTfoDivs, int nTfoMax,
    Vec_Int_t * vTfo, Cec_TranTfoStats_t * pTfoStats );

typedef struct Cec_TranSuppProf_t_ Cec_TranSuppProf_t;
typedef struct Cec_TranProf_t_ Cec_TranProf_t;
typedef struct Cec_TranPivotBucketProf_t_ Cec_TranPivotBucketProf_t;
struct Cec_TranPivotBucketProf_t_
{
    long long nAttempts;
    long long nFound;
    long long nValid;
    long long nAccepted;
    long long nValidGain;
    long long nAcceptedGain;
    long long nOutcome[CEC_TRAN_BUILD_OUTCOMES];
    long long nOutcomeGain[CEC_TRAN_BUILD_OUTCOMES];
    long long nSelectedAndGain;
    long long nSecondCover;
    long long nDiversityNew;
    long long nDiversitySym;
    abctime   Time;
};
// Diagnostic-only snapshot accounting.  None of these fields participates in
// generation, candidate identity, proof, or commit decisions.
typedef struct Cec_TranDiagBucket_t_ {
    long long Roots, Started, Exhausted, Next, Raw, Valid, Positive;
    long long Nonpositive, Duplicate, Collapsed, Invalid, Accepted, Pivots;
    abctime EnumTime, BuildTime;
} Cec_TranDiagBucket_t;
typedef struct Cec_TranDiagGate_t_ {
    long long Count, Accepted, Nonpositive, Boundary, Rescued;
    abctime Time;
} Cec_TranDiagGate_t;
static int Cec_TranDiagGateBin( int n )
{
    return n <= 4 ? n : n <= 8 ? 5 : n <= 16 ? 6 : 7;
}
typedef struct Cec_TranDiagMffc_t_ {
    long long Calls, Next, Accepted;
    long long Outcome[2][3], SelectedGain[2];
    abctime EnumTime, BuildTime;
} Cec_TranDiagMffc_t;
typedef struct Cec_TranStrictCex_t_ Cec_TranStrictCex_t;
struct Cec_TranProf_t_
{
    Cec_TranStrictCex_t * pStrictCex; // borrowed, strict SEQ proof observer only
    int DiagPhase;
    Cec_TranDiagMffc_t DiagMffc[8];
    int DiagRootAvailable;
    Cec_TranDiagBucket_t DiagRoots[8];
    Cec_TranDiagGate_t DiagGates[8][8], DiagReject[6][8];
    abctime DiagIteratorTime, DiagDecodeTime, DiagExhaustTime;

    long long nExpCiHit, nExpCiMiss, nExpObsRoots, nExpObsConflict;
    long long nExpFullRoots, nExpFullConflict, nExpObsTotal, nExpObsUnique;
    long long nExpPruned;
    abctime timeExpObs, timeExpRankScore, timeExpRankCi;
    abctime timeExpZeroBuild, timeExpPositiveBuild;
    abctime timeExpZeroRank, timeExpPositiveRank;
    abctime timeTotal;
    abctime timeGain;
    abctime timeShadow;
    abctime timeCombSolve;
    abctime timeFreeCexSim;
    abctime timeRootDivPool;
    // Diagnostic sub-buckets nested inside timeRootDivPool.  They are not
    // added to the top-level time total because that would double count.
    abctime timeRootDivCollect;
    abctime timeRootDivRank;
    abctime timeRootDivRankMffcOneFirst;
    abctime timeRootDivRankMffcOneCont;
    abctime timeRootDivRankEligibleFirst;
    abctime timeRootDivRankEligibleCont;
    long long nRootDivRankMffcOneFirstCalls;
    long long nRootDivRankMffcOneContCalls;
    long long nRootDivRankEligibleFirstCalls;
    long long nRootDivRankEligibleContCalls;
    abctime timeRootDivSelect;
    abctime timeRootDivHash;
    abctime timeRootDivTfo;
    // Rescue selection is nested in divisor discovery.  ISF total is a
    // disjoint top-level bucket; its remaining fields are nested diagnostics.
    abctime timeRootTfoCoreSelect;
    abctime timeRootTfoCoreValue;
    abctime timeRootIsf;
    abctime timeRootIsfCoreSelect;
    abctime timeRootIsfProjection;
    abctime timeRootKitSynthesis;
    abctime timeRootBdcSynthesis;
    long long nRootTfoCalls;
    long long nRootTfoSeeds;
    long long nRootTfoScanned;
    long long nRootTfoEdges;
    long long nRootTfoAdded;
    long long nRootTfoSelected;
    long long nRootTfoCoreRescueCalls;
    long long nRootTfoCoreRescueNoExtra;
    long long nRootTfoCoreRescueExact;
    long long nRootTfoCoreRescueRoots;
    long long nRootTfoCoreRescueNodes;
    long long nRootTfoCoreValueTrials;
    long long nRootTfoCoreValueExact;
    long long nRootTfoCoreValueChanged;
    long long nRootTfoCoreValueUnlocked;
    long long nRootKitCoreCalls;
    long long nRootKitCoreSeparated;
    long long nRootKitSynthesized;
    long long nRootKitAccepted;
    long long nRootKitSubmitted;
    long long nRootKitOutcome[3];
    long long nRootKitSelectedGain;
    long long nRootBdcCoreCalls;
    long long nRootBdcCoreSeparated;
    long long nRootBdcSynthesized;
    long long nRootBdcAccepted;
    long long nRootBdcSubmitted;
    long long nRootBdcOutcome[3];
    long long nRootBdcSelectedGain;
    long long nRootTfoLimitHits;
    int       nRootTfoAddedMax;
    abctime timeRootDepInit;
    abctime timeRootDepSearch;
    // Root-only redesign: the following top-level buckets are disjoint.
    abctime timeRootSimSig;
    abctime timeRootRefresh;
    // Diagnostic sub-buckets nested inside timeRootRefresh.
    abctime timeRootFrontDead;
    abctime timeRootPotentialRefresh;
    abctime timeRootFrontLoop;
    abctime timeRootFrontLoopFirst;
    abctime timeRootFrontLoopCont;
    abctime timeRootFrontSupport;
    abctime timeRootFrontGain;
    abctime timeRootFrontSort;
    long long nRootFrontPairScans;
    long long nRootFrontPairScansFirst;
    long long nRootFrontPairScansCont;
    long long nRootFrontMatched;
    int nRootFrontCalls;
    long long nRootPageMffcOneSkipped;
    abctime timeRootDirect;
    abctime timeRootDivCi;
    abctime timeRootResubInit;
    abctime timeRootResubEnumCanon;
    abctime timeRootTeach;
    abctime timeRootCbsGraph;
    abctime timeRootCbsScreen;
    abctime timeRootCbsSolve;
    abctime timeRootScorrGraph;
    abctime timeRootScorrBmc;
    abctime timeRootScorrIndSat;
    abctime timeRootScorrResim;
    abctime timeRootScorrOther;
    abctime timeRootPostSelect;
    abctime timeRootBundleDup;
    abctime timeRootCleanup;
    abctime timeRootExactAudit;
    Cec_ProfCor_t Corr;
    long long nRootBundleAndGain;
    long long nRootBundleRegGain;
    // Exact proof-origin phase-by-kind contribution.  Phase 0 is the initial
    // COMB pass and phase 1 contains later SEQ passes.  Proof-engine lane
    // (CBS/scorr) is tracked separately below.
    long long nCombConfUsed;
    int       nRootBundleCommits;
    int       nStageKindGenerated[2][3];
    int       nStageKindSubmitted[2][3];
    int       nStageKindProved[2][3];
    int       nStageKindSelected[2][3];
    int       nLaneKindSubmitted[2][3]; // CBS/scorr proof-engine lanes
    int       nLaneKindProved[2][3];
    int       nLaneKindSelected[2][3];
    long long nStageKindMarginalAndGain[2][3];
    long long nStageKindMarginalRegGain[2][3];
    int     nGainCalls;
    int     nHistoryTriedRemapped;   // tried entries retained across successful commits
    int     nHistoryTriedInvalidated;// tried entries invalidated in committed TFO
    int     nQueueTriedSkipped;      // regenerated exact candidates skipped by history
    int     nRootBatchCalls;    // two-stage proof batches in root scope
    int     nRootBatchMax;      // largest submitted relation batch
    int     nCombProved;        // combinationally proved candidates
    int     nCombDisproved;     // candidates with a combinational counterexample
    int     nCombUnknown;       // candidates not decided by CBS
    long long nCombCubesSkippedUnknown;// cube calls avoided after the first UNKNOWN
    int     nCombFreeCexStored; // valid CBS models added to the batch signature bank
    int     nCombFreeCexInvalid;// partial CBS models that failed scalar validation
    int     nCombUnknownEarly;  // candidates stopped immediately on the first UNKNOWN cube
    int     nCombNoModelCalls;  // solve calls skipping unused model extraction
    int     nRootResubIterInit;  // local iterators initialized per root/wave
    int     nRootResubIterNext;  // total Next calls, including final exhaustion
    int     nRootResubIterExhausted;// routes reaching their finite end
    int     nRootResubIterCapped;// non-terminal per-root q wave stops
    int     nRootResubIterDiscarded;// live iterators invalidated by a commit
    int     nRootResubIterLive;  // roots currently bound to shared workspace
    int     nRootResubIterLiveMax;
    int     nRootResubInvalid;   // generated recipes rejected by semantic audit
    long long nRootDivReservoirCalls;
    long long nRootDivReservoirNodes;
    int       nRootDivReservoirMax;
    long long nRootDivPoolNodes;
    int       nRootDivPoolMax;
    int       nRootDivPoolEmpty;
    long long nRootBuildMffcSum;
    int       nRootBuildMffcMax;
    long long nRootBuildMffcOneSkipped;
    long long nRootBuildCollapsedDirect;
    long long nRootBuildRejectNonPositive;
    long long nRootBuildRejectKnown;
    long long nRootBuildRejectDirect;
    long long nRootBuildRejectPage;
    long long nRootBuildAccepted;
    long long nRootTeachCalls;
    long long nRootTeachSelections;
    long long nRootTeachWithCex;
    long long nRootTeachCexSelected;
    long long nRootTeachHypotheses;
    long long nRootTeachHypCovered;
    long long nRootBuildStageValid[6];
    long long nRootBuildStageAccepted[6];
    abctime   timeRootBuildStage[6];
    long long nRootBuildStageOutcome[6][CEC_TRAN_BUILD_OUTCOMES];
    long long nRootBuildStageSelectedAndGain[6];
    long long nRootBuildRankOutcome[CEC_TRAN_BUILD_RANK_BINS][CEC_TRAN_BUILD_OUTCOMES];
    long long nRootBuildRankSelectedAndGain[CEC_TRAN_BUILD_RANK_BINS];
    long long nRootBuildGateOutcome[CEC_TRAN_BUILD_GATE_BINS][CEC_TRAN_BUILD_OUTCOMES];
    long long nRootBuildGateSelectedAndGain[CEC_TRAN_BUILD_GATE_BINS];
    long long nRootBuildGainOutcome[CEC_TRAN_BUILD_GAIN_BINS][CEC_TRAN_BUILD_OUTCOMES];
    long long nRootBuildGainSelectedAndGain[CEC_TRAN_BUILD_GAIN_BINS];
    long long nRootBuildCiOutcome[2][CEC_TRAN_BUILD_OUTCOMES];
    long long nRootBuildCiSelectedAndGain[2];
    long long nRootBuildDivRankOutcome[CEC_TRAN_BUILD_DIVRANK_BINS][CEC_TRAN_BUILD_OUTCOMES];
    long long nRootBuildDivRankSelectedAndGain[CEC_TRAN_BUILD_DIVRANK_BINS];
    long long nRootBuildMffcCalls[CEC_TRAN_BUILD_MFFC_BINS];
    long long nRootBuildMffcNext[CEC_TRAN_BUILD_MFFC_BINS];
    long long nRootBuildMffcAccepted[CEC_TRAN_BUILD_MFFC_BINS];
    abctime   timeRootBuildMffc[CEC_TRAN_BUILD_MFFC_BINS];
    long long nRootGreedyFrontierRoots;
    long long nRootGreedyFrontierPivots;
    long long nRootGreedyFrontierUnique;
    long long nRootGreedyFrontierZeroNovel;
    long long nRootGreedyFrontierCoverSum;
    long long nRootGreedyFrontierNovelSum;
    int       nRootGreedyFrontierMax;
    long long nOdcWindowRoots, nOdcWindowNodes, nOdcWindowEnds;
    long long nOdcWindowOverflow, nOdcWindowCareBits, nOdcWindowBits;
    long long nOdcCoreVariants, nOdcCarePoolChanged;
    long long nRootGreedyPivotAttempts;
    long long nRootGreedyPivotFound;
    abctime   timeRootGreedyPivot;
    long long nRootGreedySchedFrontiers;
    long long nRootGreedySchedPivots;
    long long nRootGreedySchedComplete;
    abctime   timeRootGreedySched;
    long long nRootResidualCacheLookups;
    long long nRootResidualCacheHits;
    long long nRootResidualCacheMisses;
    long long nRootResidualCacheSamePageHits;
    long long nRootResidualCacheCrossPageHits;
    long long nRootResidualCacheFailHits;
    long long nRootResidualCacheSuccessHits;
    long long nRootResidualCachePayloadBytes;
    abctime   timeRootResidualCacheSaved;
    abctime   timeRootResidualCacheLookup;
    long long nRootResidualRecCalls;
    long long nRootResidualRecUnique;
    long long nRootResidualRecDuplicate;
    long long nRootResidualRecSamePage;
    long long nRootResidualRecCrossPage;
    long long nRootResidualRecFailHits;
    long long nRootResidualRecSuccessDuplicate;
    long long nRootResidualRecPayloadBytes;
    long long nRootResidualRecDuplicateDepth[4];
    abctime   timeRootResidualRecSaved;
    abctime   timeRootResidualRecLookup;
    long long nRootMultiPathCacheEntries;
    long long nRootMultiPathCacheLookups;
    long long nRootMultiPathCacheHits;
    long long nRootMultiPathCacheFailHits;
    long long nRootMultiPathCacheSuccessHits;
    long long nRootMultiPathCachePayloadBytes;
    long long nRootMultiPathFingerprintDuplicates;
    long long nRootMultiPathAccepted;
    long long nRootMultiPathQSlots;
    Cec_TranPivotBucketProf_t GreedyPivotRank[CEC_TRAN_PIVOT_RANK_BINS];
    Cec_TranPivotBucketProf_t GreedyPivotNovel[CEC_TRAN_PIVOT_RATIO_BINS];
    Cec_TranPivotBucketProf_t GreedyPivotCover[CEC_TRAN_PIVOT_RATIO_BINS];
    Cec_TranPivotBucketProf_t GreedyPivotKind[CEC_TRAN_PIVOT_KIND_BINS];
    Cec_TranPivotBucketProf_t GreedyPivotState[2];
    Cec_TranPivotBucketProf_t MultiPath[CEC_TRAN_MULTIPATH_RANK_BINS]
        [CEC_TRAN_MULTIPATH_PATH_BINS];
    Cec_TranSuppProf_t * pBuildSuppProf;
    int     nRootWaveDepCalls[64];
    int     nRootWaveRecipes[64];
    int     nRootWaveSubmitted[64];
    int     nRootWaveProved[64];
    int     nRootWaveSelected[64];
    abctime timeRootWaveConstruct[64];
    int     nSeqCands;          // unresolved candidates sent to scorr
    int     nSeqSeeded;         // endpoint relations actually seeded into scorr classes
    int     nSeqProved;         // candidates proved only by scorr
    int     nSeqSplit;          // seeded relations split by the fixed point
    int     nSeqUnknown;        // surviving relations under an incomplete oracle
    int     nSeqRoots;          // distinct roots seeded into shared scorr
    int     nSeqClassMax;       // largest root proof class (root plus candidates)
    long long nSeqClassSum;     // total class members over seeded roots
    int     nSeqFixedRounds;    // completed fixed-point refinement rounds
    int     nHelperRetained;    // valid formal certificates kept as metadata
    int     nHelperInjected;    // helper relations materialized across waves
    int     nHelperInactive;    // retained relations skipped only when helpers are off
    int     nHelperDedup;       // exact canonical duplicates suppressed
    int     nHelperInvalidated; // retained certificates invalid on this snapshot
    int     nHelperClasses;     // source-root helper classes represented
    int     nHelperEndpoints;   // maximum unique endpoints in one injected set
    int     nHelperMaterialGates;// recipe gates materialized across batches
    int     nRootProofWaves;    // proof waves consumed on one snapshot
    int     nRootWaveContinues; // waves after the first without iterator rebuild
    int     nRootSrmNodesMax;   // maximum temporary batch node count
    int     nRootNewProved;     // newly discharged obligations
    int     nRootHistorySelected;// selected relations proved on an older snapshot
    int     nDirtyRootFreed;    // cached relation whose root is already free/used
    int     nDirtySupportFreed; // cached relation whose external support was freed
    int     nDirtyMffcChanged;  // still-legal relation with changed marginal MFFC
};

static double Cec_TranTimeSec( abctime Time )
{
    return 1.0 * Time / CLOCKS_PER_SEC;
}
