/**CFile****************************************************************

  FileName    [cecTrans.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential Direct root resubstitution.]

  Synopsis    [Candidate-and-prove sequential root replacement.]

  Description [The active algorithm replaces an AND root by a constant,
  earlier literal, or dependency recipe.  Root candidates are discovered and
  proved on an immutable GIA, selected under bundle interactions, and committed
  together.  Window/output scopes are frozen compatibility paths.  Legacy SODC
  code in this file is not part of the active &stran command.]

***********************************************************************/

#include "cecInt.h"
#include "aig/gia/giaAig.h"
#include "misc/util/utilTruth.h"
#include "sat/bmc/bmc.h"
#include <stddef.h>

ABC_NAMESPACE_IMPL_START

// COM is deliberately independent of the SEQ q/j experiment.  Arbitrary-
// state certificates do not use retained induction helpers, so COM submits
// one modest frontier and commits it immediately instead of accumulating
// proof micro-batches on the initial graph.
#define CEC_TRAN_COMB_BUILD_Q 4

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
extern void * Abc_ResubIteratorResumeStart( void ** ppDivs, int nDivs,
    int nWords, int nLimit, int nDivsMax, int fUseZero, int fUseXor,
    int * pCursor );
extern int Abc_ResubIteratorNext( void * pIter, int ** ppArray,
    int * pnAttempt, int * pfExhausted, int * pfInvalid );
extern void Abc_ResubIteratorResumeStop( void * pIter, int * pCursor );
extern int Abc_ResubIteratorSelfTest();

static int Cec_TranCanonicalizeSelfTest();
static int Cec_TranMffcSelfTest();
static int Cec_TranPipelineSelfTest();
static int Cec_TranCommitWaveSelfTest();
static int Cec_TranProofMicroBatchSelfTest();
static Vec_Int_t * Cec_TranCollectDivPool( Gia_Man_t * p, int iTarget,
    int nDepthMax, int nNodesMax, int fUseMffcDivs,
    char const * pCovered, char const * pUsed,
    char * pMffc, Vec_Int_t * vMffc );
int Cec_TranRootSelfTest()
{
    return Abc_ResubIteratorSelfTest() && Cec_TranCanonicalizeSelfTest() &&
        Cec_TranMffcSelfTest() && Cec_TranPipelineSelfTest() &&
        Cec_TranCommitWaveSelfTest() && Cec_TranProofMicroBatchSelfTest();
}

void Cec_ManTranSetDefaultParams( Cec_ParTran_t * p )
{
    memset( p, 0, sizeof(Cec_ParTran_t) );
    p->nFrames     = 1;
    p->nBTLimit    = 100;
    p->nStepsMax   = -1;
    p->nConstrMax  = 8;
    p->nConstrBaseMax = 16;
    p->nDepNodesMax = 20;
    p->nGainMin    = 1;
    p->nSimWords   = 4;
    p->nSimFrames  = 8;
    p->nRootWaves  = 8;
    p->nRootConstrTop = 1;
    p->nRootProofBatch = 0;
    // Use the same per-obligation conflict budget for the combinational CBS
    // certificate lane and the sequential scorr oracle by default.  The two
    // budgets remain independently configurable through -b and -C.
    p->nCombBTLimit = 100;
    p->nFreeWords  = 2;
    p->nFreeCexMax = 64;
    p->nHardConfTotal = 1000000;
    p->fUseExisting = 1;
    p->fUseMffcDivs = 1;
    p->fUseConstr  = 1;
    p->fUseCbsMultiLit = 1;
    // A round owns one immutable proof snapshot.  Every successful COMB/SEQ
    // selection is committed before the next snapshot is rediscovered.
    p->fRootExhaustive = 0;
    p->fUseFreeSim = 1;
    p->fUseHelpers = 1;
    p->fBuildOnly = 0;
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
    abctime timeGain;
    abctime timeShadow;
    abctime timeCombSolve;
    abctime timeFreeCexSim;
    abctime timeRootDivPool;
    abctime timeRootDepInit;
    abctime timeRootDepSearch;
    // Root-only redesign: the following top-level buckets are disjoint.
    abctime timeRootSimSig;
    abctime timeRootRefresh;
    abctime timeRootDirect;
    abctime timeRootDivCi;
    abctime timeRootResubInit;
    abctime timeRootResubEnumCanon;
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
static int Cec_TranPatDbNumSealed( Cec_TranPatDb_t * pDb )
{
    return Vec_IntSize(pDb->vBatchEnds) ? Vec_IntEntryLast(pDb->vBatchEnds) : 0;
}

// Seal pending CEXes into immutable blocks of at most 64 traces.  A sealed
// block always gets its own simulation word and is never overwritten later;
// consequently every refresh only adds signature constraints.
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
// For each sampled trace/timepoint, flip the target exactly at that frame and
// resimulate the remaining suffix.  A changed PO proves observability.  A
// changed RI is conservatively treated as observable too: its future RO may
// affect a PO beyond the sampled suffix.  The result is a sampled sequential
// care mask C_i^seq, not a formal proof and never a commit criterion.
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

// The check is exact over the current signature batch (not hash-based), so a
// duplicate cannot consume one of the expensive formal-proof slots.  Signature
// equality may merge different functions only on unsampled patterns, which
// can lose a search opportunity but can never compromise correctness.
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
// Cleanup is deliberately separated from the logical transaction.  Formal
// obligations are proved on the explicit add/remove structures; the cleaned
// copy is used only for exact cost and, after both proofs, for commit.
// Root-only transduction optimizes the AND network while preserving the
// sequential interface.  Generic sequential cleanup is allowed to delete
// latches that become unobservable after a constant replacement, which makes
// AND-only gain accounting inconsistent and changes the register boundary.
// The final root bundle therefore performs combinational cleanup/normalization
// only; other proof and compatibility paths retain Cec_TranCleanup().
static inline int Cec_TranMapLitByValue( Gia_Man_t * p, int iLit )
{
    int iMapped = Gia_ManObj(p, Abc_Lit2Var(iLit))->Value;
    return iMapped == ~0 ? -1 :
        Abc_LitNotCond( iMapped, Abc_LitIsCompl(iLit) );
}

// Return the exact input-object -> normalized-output literal map when asked.
// This is the proof-history bridge across a commit: object IDs are disposable,
// but a proved relation can be reused after both cleanup renumberings if every
// endpoint and recipe leaf has a surviving mapped literal.
static Gia_Man_t * Cec_TranCleanupKeepRegs( Gia_Man_t * p,
    Vec_Int_t ** pvMap )
{
    Gia_Man_t * pNew, * pTemp;
    Vec_Int_t * vMap = pvMap ? Vec_IntStartFull(Gia_ManObjNum(p)) : NULL;
    Gia_Obj_t * pObj;
    int i, iLit;
    pNew = Gia_ManCleanup( pTemp = Gia_ManDup(p) );
    if ( vMap )
        Gia_ManForEachObj( p, pObj, i )
        {
            iLit = Cec_TranMapLitByValue( p, Abc_Var2Lit(i, 0) );
            if ( iLit >= 0 )
                iLit = Cec_TranMapLitByValue( pTemp, iLit );
            Vec_IntWriteEntry( vMap, i, iLit );
        }
    Gia_ManStop( pTemp );
    pNew = Gia_ManDupNormalize( pTemp = pNew, 0 );
    if ( vMap )
        Vec_IntForEachEntry( vMap, iLit, i )
            if ( iLit >= 0 )
                Vec_IntWriteEntry( vMap, i,
                    Cec_TranMapLitByValue(pTemp, iLit) );
    Gia_ManStop( pTemp );
    assert( Gia_ManRegNum(pNew) == Gia_ManRegNum(p) );
    if ( pvMap )
        *pvMap = vMap;
    return pNew;
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

static inline int Cec_TranHashGate( Gia_Man_t * pNew, Gia_Obj_t * pObj, int iLit0, int iLit1 )
{
    return Gia_ObjIsXor(pObj) ? Gia_ManHashXor(pNew, iLit0, iLit1) :
        Gia_ManHashAnd(pNew, iLit0, iLit1);
}

// Mark the complete combinational TFO of the edited target, including the
// PO/RI boundaries.  A marked RI is emitted as a difference PO by the local
// miter; its corresponding RO is then related inductively by the common
// source-state machine built below.
// Compute the sampled care used by the bounded-window proof.  Unlike output
// scope, the window obligation observes the exact TFO cut as well as every
// PO/RI reached before the cut.  Re-simulating the marked cone with the root
// flipped therefore makes a harvested window CEX a real new dependency
// constraint instead of relying only on the tried-recipe history to avoid
// proposing the same invalid function again.
// Construct a single-state sequential difference machine.  It shares the
// original transition relation, duplicates only the target's combinational
// TFO for the edited variant, and emits differences at all affected PO/RI
// boundaries.  Equality of the affected RIs, together with unchanged
// unmarked RIs, inductively establishes a common state trajectory.  Thus this
// is an exact COI reduction for these pure combinational edits, not a bounded
// window approximation.
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
// The candidate has already passed the exact structural-gain test.  This
// routine is the transactional boundary: no speculative wiring reaches p
// unless the sequential miter is discharged by scorr's proof infrastructure.
#define CEC_TRAN_RECIPE_NODES_MAX 100

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
typedef struct Cec_TranRecipe_t_ Cec_TranRecipe_t;
struct Cec_TranRecipe_t_
{
    int nRefs;
    int Data[1];
};
struct Cec_TranCand_t_
{
    int iTarget;
    int iDiv0;                  // display/compatibility: first external literal
    int iDiv1;                  // display/compatibility: second external literal
    int nMffc;
    int Gain;                   // local structural gain for scheduling
    int nGates;                 // dependency AIG nodes in Recipe[]
    int iOut;                   // external or recipe-gate literal code
    int * Recipe;               // shared, immutable, exactly 2*nGates ints
    unsigned fStrict   : 1;
    unsigned nKind     : 2;
    // nProofStage is the certificate strength currently safe to reuse.  A
    // commit may downgrade it to sequential.  The three origin fields never
    // change and keep reporting stable across remap/canonicalization.
    unsigned nProofStage : 2;   // 0=unproved, 1=combinational, 2=sequential
    unsigned nProofLane  : 2;   // original proof engine: 1=CBS, 2=scorr
    unsigned nProofPhase : 1;   // original algorithm phase: 0=COMB, 1=SEQ
    unsigned nProofKind  : 2;   // candidate kind when originally proved
    unsigned nStatus    : 3;    // candidate/stale/tried_seq/proved_comb/proved_seq/selected
    unsigned fExactTemplate : 1;// finite exact resub template (before greedy diversity)
    unsigned fDivRescue : 1;
    unsigned fDivGlobal : 1;
    unsigned fPrimaryFrontier : 1;
    int      nResubRank;         // 0=non-resub, otherwise raw recipe rank
    int      nCiOverlap;         // CI support overlap with root; ordering only
    int      nWave;              // zero-based root CEGAR wave
};

// Candidate vectors copy scheduling metadata by value, but all copies of a
// constructed candidate refer to one immutable, reference-counted recipe.
// Literal/constant candidates allocate no recipe at all.  Keeping the recipe
// out of Cec_TranCand_t is important because the root lane can contain every
// exact earlier literal and may therefore hold millions of zero-gate entries.
static int * Cec_TranRecipeAlloc( int nSize )
{
    Cec_TranRecipe_t * p;
    assert( nSize > 0 && nSize <= 2 * CEC_TRAN_RECIPE_NODES_MAX );
    p = (Cec_TranRecipe_t *)ABC_ALLOC( char,
        sizeof(Cec_TranRecipe_t) + sizeof(int) * (nSize - 1) );
    p->nRefs = 1;
    return p->Data;
}

static Cec_TranRecipe_t * Cec_TranRecipeHead( int const * pData )
{
    return (Cec_TranRecipe_t *)((char *)pData -
        offsetof(Cec_TranRecipe_t, Data));
}

static void Cec_TranCandRecipeRetain( Cec_TranCand_t const * pCand )
{
    if ( pCand->Recipe )
        Cec_TranRecipeHead(pCand->Recipe)->nRefs++;
}

static void Cec_TranCandRecipeRelease( Cec_TranCand_t * pCand )
{
    Cec_TranRecipe_t * pRecipe;
    if ( pCand->Recipe == NULL )
        return;
    pRecipe = Cec_TranRecipeHead( pCand->Recipe );
    assert( pRecipe->nRefs > 0 );
    if ( --pRecipe->nRefs == 0 )
        ABC_FREE( pRecipe );
    pCand->Recipe = NULL;
}

static inline int Cec_TranRecipeNotCode( int Code )
{
    int iLit;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return Abc_LitNot( Code );
    iLit = Cec_TranRecipeGateLit( Code );
    return Cec_TranRecipeGateCode( Abc_Lit2Var(iLit),
        !Abc_LitIsCompl(iLit) );
}

static inline int Cec_TranRecipeMapCode( int Code, int const * pMap,
    int nMapped )
{
    int iLit, iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return Code;
    iLit = Cec_TranRecipeGateLit( Code );
    iGate = Abc_Lit2Var( iLit );
    assert( iGate < nMapped );
    return Abc_LitIsCompl(iLit) ?
        Cec_TranRecipeNotCode(pMap[iGate]) : pMap[iGate];
}

static void Cec_TranRecipeMarkUsed_rec( int Code, int const * pRecipe,
    int nGates, char * pUsed )
{
    int iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
        return;
    iGate = Abc_Lit2Var( Cec_TranRecipeGateLit(Code) );
    assert( iGate < nGates );
    if ( pUsed[iGate] )
        return;
    pUsed[iGate] = 1;
    Cec_TranRecipeMarkUsed_rec( pRecipe[2*iGate], pRecipe, nGates, pUsed );
    Cec_TranRecipeMarkUsed_rec( pRecipe[2*iGate+1], pRecipe, nGates, pUsed );
}

// Canonicalize the small recipe AIG before it enters a candidate set.  These
// are structural identities only: commutative fanins, constants, duplicate
// inputs, complementary inputs, one-level absorption, hash-identical gates,
// and dead gates.  Sampled dominance is deliberately not a pruning rule.
static void Cec_TranCandCanonicalizeRecipe( Cec_TranCand_t * pCand )
{
    int Work[2 * CEC_TRAN_RECIPE_NODES_MAX];
    int OldMap[CEC_TRAN_RECIPE_NODES_MAX];
    int CompactMap[CEC_TRAN_RECIPE_NODES_MAX];
    int Compact[2 * CEC_TRAN_RECIPE_NODES_MAX];
    char Used[CEC_TRAN_RECIPE_NODES_MAX] = {0};
    int i, k, a, b, Result, nWork = 0, nCompact = 0, iOut;
    if ( pCand->nGates == 0 )
        return;
    for ( i = 0; i < pCand->nGates; i++ )
    {
        a = Cec_TranRecipeMapCode( pCand->Recipe[2*i], OldMap, i );
        b = Cec_TranRecipeMapCode( pCand->Recipe[2*i+1], OldMap, i );
        if ( a == 0 || b == 0 || a == Cec_TranRecipeNotCode(b) )
            Result = 0;
        else if ( a == 1 )
            Result = b;
        else if ( b == 1 || a == b )
            Result = a;
        else
        {
            Result = -1;
            if ( Cec_TranRecipeCodeIsGate(a) &&
                 !Abc_LitIsCompl(Cec_TranRecipeGateLit(a)) )
            {
                k = Abc_Lit2Var( Cec_TranRecipeGateLit(a) );
                if ( Work[2*k] == b || Work[2*k+1] == b )
                    Result = a;
            }
            if ( Result == -1 && Cec_TranRecipeCodeIsGate(b) &&
                 !Abc_LitIsCompl(Cec_TranRecipeGateLit(b)) )
            {
                k = Abc_Lit2Var( Cec_TranRecipeGateLit(b) );
                if ( Work[2*k] == a || Work[2*k+1] == a )
                    Result = b;
            }
            if ( Result == -1 )
            {
                if ( a > b ) { int t = a; a = b; b = t; }
                for ( k = 0; k < nWork; k++ )
                    if ( Work[2*k] == a && Work[2*k+1] == b )
                        break;
                if ( k < nWork )
                    Result = Cec_TranRecipeGateCode( k, 0 );
                else
                {
                    Work[2*nWork] = a;
                    Work[2*nWork+1] = b;
                    Result = Cec_TranRecipeGateCode( nWork++, 0 );
                }
            }
        }
        OldMap[i] = Result;
    }
    iOut = Cec_TranRecipeMapCode( pCand->iOut, OldMap, pCand->nGates );
    Cec_TranRecipeMarkUsed_rec( iOut, Work, nWork, Used );
    for ( i = 0; i < nWork; i++ )
    {
        CompactMap[i] = -1;
        if ( !Used[i] )
            continue;
        a = Cec_TranRecipeMapCode( Work[2*i], CompactMap, i );
        b = Cec_TranRecipeMapCode( Work[2*i+1], CompactMap, i );
        Compact[2*nCompact] = a;
        Compact[2*nCompact+1] = b;
        CompactMap[i] = Cec_TranRecipeGateCode( nCompact++, 0 );
    }
    iOut = Cec_TranRecipeMapCode( iOut, CompactMap, nWork );
    Cec_TranCandRecipeRelease( pCand );
    pCand->nGates = nCompact;
    pCand->iOut = iOut;
    if ( nCompact )
    {
        pCand->Recipe = Cec_TranRecipeAlloc( 2 * nCompact );
        memcpy( pCand->Recipe, Compact, sizeof(int) * 2 * nCompact );
    }
    pCand->nKind = nCompact ? CEC_TRAN_CAND_CONSTR :
        (Abc_Lit2Var(iOut) == 0 ? CEC_TRAN_CAND_CONST :
            CEC_TRAN_CAND_EXIST);
}

static int Cec_TranCanonicalizeSelfTest()
{
    Cec_TranCand_t Cand;
    memset( &Cand, 0, sizeof(Cand) );
    Cand.nKind = CEC_TRAN_CAND_CONSTR;
    Cand.nGates = 3;
    Cand.Recipe = Cec_TranRecipeAlloc( 6 );
    // g0 = x & 1 = x; g1 = g0 & x = x; g2 = g1 & g0 = x.
    Cand.Recipe[0] = Abc_Var2Lit(2, 0); Cand.Recipe[1] = 1;
    Cand.Recipe[2] = Cec_TranRecipeGateCode(0, 0);
    Cand.Recipe[3] = Abc_Var2Lit(2, 0);
    Cand.Recipe[4] = Cec_TranRecipeGateCode(1, 0);
    Cand.Recipe[5] = Cec_TranRecipeGateCode(0, 0);
    Cand.iOut = Cec_TranRecipeGateCode(2, 0);
    Cec_TranCandCanonicalizeRecipe( &Cand );
    assert( Cand.nGates == 0 && Cand.Recipe == NULL );
    assert( Cand.nKind == CEC_TRAN_CAND_EXIST &&
        Cand.iOut == Abc_Var2Lit(2, 0) );
    // x & !x canonicalizes to constant zero.
    Cand.nKind = CEC_TRAN_CAND_CONSTR;
    Cand.nGates = 1;
    Cand.Recipe = Cec_TranRecipeAlloc( 2 );
    Cand.Recipe[0] = Abc_Var2Lit(3, 0);
    Cand.Recipe[1] = Abc_Var2Lit(3, 1);
    Cand.iOut = Cec_TranRecipeGateCode(0, 0);
    Cec_TranCandCanonicalizeRecipe( &Cand );
    assert( Cand.nGates == 0 && Cand.Recipe == NULL &&
        Cand.nKind == CEC_TRAN_CAND_CONST && Cand.iOut == 0 );
    return 1;
}

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

// Frozen structural hashing used by commit-wave gain evaluation.  DATE's
// DryReplace accounts for replacement nodes which are already present in the
// DAG.  Candidate nGates is only an upper bound on that cost.  Build one
// strashed copy per wave, then simulate each small recipe against this copy
// without appending anything to either network.
typedef struct Cec_TranFrozenHash_t_ Cec_TranFrozenHash_t;
struct Cec_TranFrozenHash_t_
{
    Gia_Man_t * pHash;
    Vec_Int_t * vOldToHash;
    Vec_Int_t * vHashToOld;      // earliest old object represented by a hash node
    int         nFrozenObjs;
};

static void Cec_TranFrozenHashStart( Gia_Man_t * p,
    Cec_TranFrozenHash_t * pHash )
{
    Gia_Obj_t * pObj;
    int i, iLit, iLit0, iLit1, iVar;
    memset( pHash, 0, sizeof(Cec_TranFrozenHash_t) );
    pHash->pHash = Gia_ManStart( Gia_ManObjNum(p) );
    Gia_ManHashAlloc( pHash->pHash );
    pHash->vOldToHash = Vec_IntStartFull( Gia_ManObjNum(p) );
    pHash->vHashToOld = Vec_IntAlloc( Gia_ManObjNum(p) );
    Vec_IntWriteEntry( pHash->vOldToHash, 0, 0 );
    Vec_IntFillExtra( pHash->vHashToOld, 1, 0 );
    Gia_ManForEachCi( p, pObj, i )
    {
        int iOld = Gia_ObjId( p, pObj );
        iLit = Gia_ManAppendCi( pHash->pHash );
        Vec_IntWriteEntry( pHash->vOldToHash, iOld, iLit );
        Vec_IntFillExtra( pHash->vHashToOld,
            Gia_ManObjNum(pHash->pHash), -1 );
        Vec_IntWriteEntry( pHash->vHashToOld,
            Abc_Lit2Var(iLit), iOld );
    }
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Vec_IntEntry( pHash->vOldToHash,
            Gia_ObjFaninId0p(p, pObj) );
        iLit1 = Vec_IntEntry( pHash->vOldToHash,
            Gia_ObjFaninId1p(p, pObj) );
        iLit0 = Abc_LitNotCond( iLit0, Gia_ObjFaninC0(pObj) );
        iLit1 = Abc_LitNotCond( iLit1, Gia_ObjFaninC1(pObj) );
        iLit = Cec_TranHashGate( pHash->pHash, pObj, iLit0, iLit1 );
        Vec_IntWriteEntry( pHash->vOldToHash, i, iLit );
        Vec_IntFillExtra( pHash->vHashToOld,
            Gia_ManObjNum(pHash->pHash), -1 );
        iVar = Abc_Lit2Var( iLit );
        if ( Vec_IntEntry(pHash->vHashToOld, iVar) < 0 )
            Vec_IntWriteEntry( pHash->vHashToOld, iVar, i );
    }
    pHash->nFrozenObjs = Gia_ManObjNum( pHash->pHash );
}

static void Cec_TranFrozenHashStop( Cec_TranFrozenHash_t * pHash )
{
    if ( pHash->pHash )
    {
        Gia_ManHashStop( pHash->pHash );
        Gia_ManStop( pHash->pHash );
    }
    Vec_IntFreeP( &pHash->vOldToHash );
    Vec_IntFreeP( &pHash->vHashToOld );
    memset( pHash, 0, sizeof(Cec_TranFrozenHash_t) );
}

static inline int Cec_TranFrozenRecipeCode(
    Cec_TranFrozenHash_t const * pHash, int Code,
    int const * pGates, int nBuilt )
{
    int iLit, iGate;
    if ( !Cec_TranRecipeCodeIsGate(Code) )
    {
        iLit = Vec_IntEntry( pHash->vOldToHash, Abc_Lit2Var(Code) );
        return Abc_LitNotCond( iLit, Abc_LitIsCompl(Code) );
    }
    iLit = Cec_TranRecipeGateLit( Code );
    iGate = Abc_Lit2Var( iLit );
    assert( iGate < nBuilt );
    return Abc_LitNotCond( pGates[iGate], Abc_LitIsCompl(iLit) );
}

static int Cec_TranFrozenHashAnd( Cec_TranFrozenHash_t const * pHash,
    int iTarget, char const * pCovered, int iLit0, int iLit1,
    int * pNew0, int * pNew1, int * pnNew )
{
    int i, iLit, iOld;
    if ( iLit0 < 2 )
        return iLit0 ? iLit1 : 0;
    if ( iLit1 < 2 )
        return iLit1 ? iLit0 : 0;
    if ( iLit0 == iLit1 )
        return iLit1;
    if ( iLit0 == Abc_LitNot(iLit1) )
        return 0;
    if ( iLit0 > iLit1 )
        ABC_SWAP( int, iLit0, iLit1 );
    if ( Abc_Lit2Var(iLit0) < pHash->nFrozenObjs &&
         Abc_Lit2Var(iLit1) < pHash->nFrozenObjs )
    {
        iLit = Gia_ManHashAndTry( pHash->pHash, iLit0, iLit1 );
        if ( iLit >= 0 )
        {
            iOld = Vec_IntEntry( pHash->vHashToOld, Abc_Lit2Var(iLit) );
            // The topological bundle has only copied nodes preceding the
            // target.  A hit at the target or in its TFO is not reusable.
            if ( iOld >= 0 && iOld < iTarget &&
                 (!pCovered || !pCovered[iOld]) )
                return iLit;
        }
    }
    for ( i = 0; i < *pnNew; i++ )
        if ( pNew0[i] == iLit0 && pNew1[i] == iLit1 )
            return Abc_Var2Lit( pHash->nFrozenObjs + i, 0 );
    assert( *pnNew < CEC_TRAN_RECIPE_NODES_MAX );
    pNew0[*pnNew] = iLit0;
    pNew1[*pnNew] = iLit1;
    return Abc_Var2Lit( pHash->nFrozenObjs + (*pnNew)++, 0 );
}

static int Cec_TranFrozenRecipeReach_rec(
    Cec_TranFrozenHash_t const * pHash, Gia_Man_t * p, int iLit,
    int const * pNew0, int const * pNew1, char * pSeen,
    Vec_Int_t * vBoundary )
{
    int iVar = Abc_Lit2Var( iLit );
    int iNew, iOld, Count;
    if ( iVar < pHash->nFrozenObjs )
    {
        iOld = Vec_IntEntry( pHash->vHashToOld, iVar );
        if ( iOld > 0 && Gia_ObjIsAnd(Gia_ManObj(p, iOld)) &&
             Vec_IntFind(vBoundary, iOld) < 0 )
            Vec_IntPush( vBoundary, iOld );
        return 0;
    }
    iNew = iVar - pHash->nFrozenObjs;
    if ( pSeen[iNew] )
        return 0;
    pSeen[iNew] = 1;
    Count = 1;
    Count += Cec_TranFrozenRecipeReach_rec( pHash, p, pNew0[iNew],
        pNew0, pNew1, pSeen, vBoundary );
    Count += Cec_TranFrozenRecipeReach_rec( pHash, p, pNew1[iNew],
        pNew0, pNew1, pSeen, vBoundary );
    return Count;
}

static int Cec_TranFrozenRecipeCost( Gia_Man_t * p,
    Cec_TranFrozenHash_t const * pHash, Cec_TranCand_t const * pCand,
    char const * pCovered, Vec_Int_t * vBoundary )
{
    int Gates[CEC_TRAN_RECIPE_NODES_MAX];
    int New0[CEC_TRAN_RECIPE_NODES_MAX];
    int New1[CEC_TRAN_RECIPE_NODES_MAX];
    char Seen[CEC_TRAN_RECIPE_NODES_MAX] = {0};
    int i, iLit0, iLit1, iOut, nNew = 0;
    for ( i = 0; i < pCand->nGates; i++ )
    {
        iLit0 = Cec_TranFrozenRecipeCode( pHash, pCand->Recipe[2*i],
            Gates, i );
        iLit1 = Cec_TranFrozenRecipeCode( pHash, pCand->Recipe[2*i+1],
            Gates, i );
        Gates[i] = Cec_TranFrozenHashAnd( pHash, pCand->iTarget,
            pCovered, iLit0, iLit1, New0, New1, &nNew );
    }
    iOut = Cec_TranFrozenRecipeCode( pHash, pCand->iOut,
        Gates, pCand->nGates );
    return Cec_TranFrozenRecipeReach_rec( pHash, p, iOut,
        New0, New1, Seen, vBoundary );
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

static int Cec_TranRecipeStructurallyValid( Cec_TranSim_t * pSim,
    Cec_TranCand_t const * pCand )
{
    int i, k, Code;
    if ( pCand->nGates < 0 ||
         pCand->nGates > CEC_TRAN_RECIPE_NODES_MAX )
        return 0;
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) )
        {
            k = Abc_Lit2Var( Cec_TranRecipeGateLit(Code) );
            if ( k >= (i < 0 ? pCand->nGates : i / 2) )
                return 0;
        }
        else if ( Code < 0 || Abc_Lit2Var(Code) >= Gia_ManObjNum(pSim->pGia) )
            return 0;
    }
    return 1;
}

// Direct resubstitution replaces the root itself, rather than one of the
// root's supergate leaves.  Formal proof remains the sole commit criterion.
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

typedef struct Cec_TranRoot_t_ Cec_TranRoot_t;
struct Cec_TranRoot_t_
{
    int iObj;
    int nMffc;
};

typedef struct Cec_TranRootCursor_t_ Cec_TranRootCursor_t;
struct Cec_TranRootCursor_t_
{
    int State[5];               // Gia resub Stage/n/i/k/iGreedy
    int nBuildYield;
    int nBuildAccepted;         // unique positive-gain Build candidates emitted on this snapshot
    int nPages;
    int fExhausted;
};

// With proof micro-batching disabled, q retains its historical meaning: one
// discovery wave pulls q Build candidates (or drains the iterator for q=0)
// and a positive proof is immediately eligible for selection.  With -j, q is
// instead the per-snapshot commit horizon and -j is the per-proof-call slice.
// Returning zero means either "legacy unlimited" (q=0, -j=0) or "horizon
// reached" (-j>0); callers distinguish these cases through nRootProofBatch.
static int Cec_TranRootBuildBudget( Cec_ParTran_t const * pPars,
    Cec_TranRootCursor_t const * pCursor )
{
    int nRemain;
    if ( pCursor->fExhausted )
        return 0;
    if ( pPars->nRootProofBatch <= 0 )
        return pPars->nRootConstrTop;
    if ( pPars->nRootConstrTop == 0 )
        return pPars->nRootProofBatch;
    nRemain = pPars->nRootConstrTop - pCursor->nBuildAccepted;
    return nRemain <= 0 ? 0 :
        Abc_MinInt( pPars->nRootProofBatch, nRemain );
}

static int Cec_TranRootBuildHorizonReached( Cec_ParTran_t const * pPars,
    Cec_TranRootCursor_t const * pCursor )
{
    assert( pPars->nRootProofBatch > 0 );
    return pCursor->fExhausted ||
        (pPars->nRootConstrTop > 0 &&
         pCursor->nBuildAccepted >= pPars->nRootConstrTop);
}

static int Cec_TranProofMicroBatchSelfTest()
{
    Cec_ParTran_t Pars;
    Cec_TranRootCursor_t Cursor = {{0}};
    Cec_ManTranSetDefaultParams( &Pars );
    Pars.nRootConstrTop = 100;
    assert( Cec_TranRootBuildBudget(&Pars, &Cursor) == 100 );
    Pars.nRootProofBatch = 5;
    assert( Cec_TranRootBuildBudget(&Pars, &Cursor) == 5 );
    Cursor.nBuildAccepted = 97;
    assert( Cec_TranRootBuildBudget(&Pars, &Cursor) == 3 );
    Cursor.nBuildAccepted = 100;
    assert( Cec_TranRootBuildBudget(&Pars, &Cursor) == 0 );
    assert( Cec_TranRootBuildHorizonReached(&Pars, &Cursor) );
    Cursor.nBuildAccepted = 0;
    Pars.nRootConstrTop = 0;
    assert( Cec_TranRootBuildBudget(&Pars, &Cursor) == 5 );
    assert( !Cec_TranRootBuildHorizonReached(&Pars, &Cursor) );
    Cursor.fExhausted = 1;
    assert( Cec_TranRootBuildBudget(&Pars, &Cursor) == 0 );
    assert( Cec_TranRootBuildHorizonReached(&Pars, &Cursor) );
    return 1;
}

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
    Cec_TranCandRecipeRetain( &Cand );
    p->pArray[p->nSize] = Cand;
    k = (int)(Cec_TranCandHash(&Cand) & (unsigned)(p->nHash - 1));
    while ( p->pHash[k] )
        k = (k + 1) & (p->nHash - 1);
    p->pHash[k] = ++p->nSize;
}

static void Cec_TranCandVecClear( Cec_TranCandVec_t * p )
{
    int i;
    for ( i = 0; i < p->nSize; i++ )
        Cec_TranCandRecipeRelease( p->pArray + i );
    p->nSize = p->iHead = 0;
    if ( p->pHash )
        memset( p->pHash, 0, sizeof(int) * p->nHash );
}

static void Cec_TranCandVecStop( Cec_TranCandVec_t * p )
{
    Cec_TranCandVecClear( p );
    ABC_FREE( p->pArray );
    ABC_FREE( p->pHash );
    memset( p, 0, sizeof(Cec_TranCandVec_t) );
}

static int Cec_TranCandEqual( Cec_TranCand_t const * p0, Cec_TranCand_t const * p1 )
{
    return p0->iTarget == p1->iTarget && p0->fStrict == p1->fStrict &&
        p0->nGates == p1->nGates && p0->iOut == p1->iOut &&
        (p0->nGates == 0 || !memcmp( p0->Recipe, p1->Recipe,
            sizeof(int) * 2 * p0->nGates ));
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

static int Cec_TranCandVecFind( Cec_TranCandVec_t const * p,
    Cec_TranCand_t const * pCand )
{
    int k;
    if ( p->nHash == 0 )
        return -1;
    k = (int)(Cec_TranCandHash(pCand) & (unsigned)(p->nHash - 1));
    while ( p->pHash[k] )
    {
        int i = p->pHash[k] - 1;
        if ( Cec_TranCandEqual(p->pArray + i, pCand) )
            return i;
        k = (k + 1) & (p->nHash - 1);
    }
    return -1;
}

static int Cec_TranProofHistoryCodeMap( int Code, Vec_Int_t * vMap,
    int * pfValid )
{
    int iMapped;
    if ( Cec_TranRecipeCodeIsGate(Code) )
        return Code;
    if ( Code < 0 || Abc_Lit2Var(Code) >= Vec_IntSize(vMap) )
    {
        *pfValid = 0;
        return 0;
    }
    iMapped = Vec_IntEntry( vMap, Abc_Lit2Var(Code) );
    if ( iMapped < 0 )
    {
        *pfValid = 0;
        return 0;
    }
    return Abc_LitNotCond( iMapped, Abc_LitIsCompl(Code) );
}

static int Cec_TranProofHistoryTopoValid( Gia_Man_t * p,
    Cec_TranCand_t const * pCand )
{
    int i, Code, iObj;
    if ( pCand->iTarget <= 0 || pCand->iTarget >= Gia_ManObjNum(p) ||
         !Gia_ObjIsAnd(Gia_ManObj(p, pCand->iTarget)) )
        return 0;
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) )
        {
            iObj = Abc_Lit2Var( Cec_TranRecipeGateLit(Code) );
            if ( iObj >= (i < 0 ? pCand->nGates : i / 2) )
                return 0;
            continue;
        }
        iObj = Abc_Lit2Var( Code );
        if ( Code < 0 || iObj >= Gia_ManObjNum(p) ||
             (iObj != 0 && iObj >= pCand->iTarget) )
            return 0;
    }
    return 1;
}

// Carry only formally proved relations across a commit.  UNKNOWN/split
// obligations are deliberately not cached; they can only reappear through
// natural discovery on a genuinely rebuilt graph.  A carried relation is
// downgraded to a sequential certificate because a sequentially proved commit
// need not preserve arbitrary-state internal identities.  Proof origin
// metadata is preserved so phase/kind/lane statistics do not move when a
// recipe canonicalizes or its reusable certificate strength is downgraded.
static void Cec_TranRemapProofHistory( Gia_Man_t * pNew,
    Vec_Int_t * vOldToNew, Cec_TranCandVec_t const * pCarry,
    Cec_TranCandVec_t * pHistory, Cec_TranProf_t * pProf )
{
    Cec_TranCand_t Cand;
    int i, k, Code, iTargetLit, fValid;
    Cec_TranCandVecClear( pHistory );
    for ( i = 0; i < pCarry->nSize; i++ )
    {
        Cec_TranCand_t const * pOld = pCarry->pArray + i;
        if ( pOld->iTarget < 0 || pOld->iTarget >= Vec_IntSize(vOldToNew) )
        {
            pProf->nHistoryTriedInvalidated++;
            continue;
        }
        iTargetLit = Vec_IntEntry( vOldToNew, pOld->iTarget );
        if ( iTargetLit < 0 )
        {
            pProf->nHistoryTriedInvalidated++;
            continue;
        }
        Cand = *pOld;
        Cand.Recipe = NULL;
        Cand.iTarget = Abc_Lit2Var( iTargetLit );
        Cand.nMffc = 0;
        Cand.Gain = -1;
        Cand.nProofStage = 2;
        Cand.nStatus = CEC_TRAN_STATE_PROVED_SEQ;
        fValid = 1;
        if ( Cand.nGates )
            Cand.Recipe = Cec_TranRecipeAlloc( 2 * Cand.nGates );
        for ( k = 0; k < 2 * Cand.nGates; k++ )
            Cand.Recipe[k] = Cec_TranProofHistoryCodeMap(
                pOld->Recipe[k], vOldToNew, &fValid );
        Cand.iOut = Cec_TranProofHistoryCodeMap(
            pOld->iOut, vOldToNew, &fValid );
        if ( fValid && Abc_LitIsCompl(iTargetLit) )
            Cand.iOut = Cec_TranRecipeNotCode( Cand.iOut );
        if ( fValid )
            Cec_TranCandCanonicalizeRecipe( &Cand );
        if ( !fValid || !Cec_TranProofHistoryTopoValid(pNew, &Cand) )
        {
            Cec_TranCandRecipeRelease( &Cand );
            pProf->nHistoryTriedInvalidated++;
            continue;
        }
        Cand.iDiv0 = Cand.iDiv1 = -1;
        for ( k = -1; k < 2 * Cand.nGates; k++ )
        {
            Code = k < 0 ? Cand.iOut : Cand.Recipe[k];
            if ( Cec_TranRecipeCodeIsGate(Code) || Abc_Lit2Var(Code) == 0 )
                continue;
            if ( Cand.iDiv0 == -1 )
                Cand.iDiv0 = Code;
            else if ( Abc_Lit2Var(Cand.iDiv0) != Abc_Lit2Var(Code) )
            {
                Cand.iDiv1 = Code;
                break;
            }
        }
        if ( !Cec_TranCandVecContains(pHistory, &Cand) )
        {
            Cec_TranCandVecPush( pHistory, Cand );
            pProf->nHistoryTriedRemapped++;
        }
        Cec_TranCandRecipeRelease( &Cand );
    }
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
    Cec_TranCand_t const * pHelpers, int nHelpers,
    Cec_TranCand_t const * pCands, int nCands,
    int fCreateQueries,
    Vec_Int_t ** pvPairs, Vec_Int_t ** pvCombPairs, Vec_Int_t ** pvQueries,
    Vec_Int_t ** pvAndLeaves, Vec_Str_t ** pvAndCounts )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int nRelations = nHelpers + nCands;
    Vec_Int_t * vPairs = Vec_IntAlloc( 2 * nRelations );
    Vec_Int_t * vCombPairs = Vec_IntAlloc( 2 * nCands );
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
    pNew = Gia_ManStart( Gia_ManObjNum(p) + 4 * nRelations + 16 );
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
    for ( i = 0; i < nRelations; i++ )
    {
        Cec_TranCand_t const * pCand = i < nHelpers ?
            pHelpers + i : pCands + i - nHelpers;
        int fObligation = i >= nHelpers;
        iRoot = Cec_TranCopyLit( p, Abc_Var2Lit(pCand->iTarget, 0) );
        iRep = Cec_TranRecipeBuildMapped( p, pNew, pCand, Gates );
        if ( fObligation )
            Vec_IntPushTwo( vCombPairs, iRoot, iRep );
        if ( fObligation && vAndCounts )
        {
            nLeaves = Cec_TranRecipeCollectAndLeaves( pCand, Leaves );
            assert( nLeaves <= 2 * CEC_TRAN_RECIPE_NODES_MAX + 1 );
            for ( k = 0; k < nLeaves; k++ )
                Vec_IntPush( vAndLeaves, Cec_TranRecipeCopyCode(
                    p, Leaves[k], Gates, pCand->nGates) );
            Vec_StrPush( vAndCounts, (char)nLeaves );
        }
        // Build ordinary CBS/BMC queries from the real recipe endpoint.  A PI
        // proxy is only a correspondence-class representation; exposing its
        // unstrashed x&1 gate to CBS would make the solver visit constant
        // fanins, which are not CBS candidate variables.
        if ( fObligation && fCreateQueries )
        {
            iQuery = Gia_ManHashXor( pNew, iRoot, iRep );
            Vec_IntPush( vQueries, iQuery );
        }
        // Shared induction must constrain both physical endpoints used by the
        // transition relation.  Isolated x&1 wrappers are combinationally
        // equivalent but cannot carry the relation across frames.
        iRep = Cec_TranRootClassEndpoint( pNew, iRep,
            nPis, pPiProxies );
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
    Gia_ManDupRemapLiterals( vCombPairs, pTemp );
    Gia_ManDupRemapLiterals( vQueries, pTemp );
    if ( vAndLeaves )
        Gia_ManDupRemapLiterals( vAndLeaves, pTemp );
    Gia_ManStop( pTemp );
    ABC_FREE( pPiProxies );

    *pvPairs = vPairs;
    *pvCombPairs = vCombPairs;
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
    Cec_ParTran_t * pPars, Cec_TranProf_t * pProf,
    int fStopAtFirstProof, int * pnAttempted )
{
    Cbs_Man_t * pCbs = Cbs_ManAlloc( pBatch );
    Cec_TranFreeSim_t * pFree = NULL;
    Vec_Str_t * vStage = Vec_StrStart( nCands );
    int Cube[2 * CEC_TRAN_RECIPE_NODES_MAX + 2];
    int i, k, iBeg = 0, iEnd = 0, nLeaves, a, h, t;
    int Status, fSat, fUnknown, fSaveModel, FreeMismatch;
    abctime clk = Abc_Clock(), timeSolve = 0, clkSolve;
    if ( pPars->fUseFreeSim && (pPars->nFreeWords || pPars->nFreeCexMax) )
        pFree = Cec_TranFreeSimStart( pBatch, pPars->nFreeWords,
            pPars->nFreeCexMax );
    Cbs_ManSetConflictNum( pCbs, pPars->nCombBTLimit );
    assert( pPars->fUseCbsMultiLit || Vec_IntSize(vQueries) == nCands );
    if ( pnAttempted )
        *pnAttempted = 0;
    for ( i = 0; i < nCands; i++ )
    {
        if ( pnAttempted )
            (*pnAttempted)++;
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
            if ( fStopAtFirstProof )
                break;
            continue;
        }
        if ( pFree )
        {
            FreeMismatch = Cec_TranFreeSimMismatch( pFree, a, h );
            if ( FreeMismatch )
                continue;
        }
        // Model extraction is useful only while the batch CEGIS bank still
        // has room.  Once full, use the cheaper solve entry point for every
        // remaining cube/query instead of repeatedly collecting unused CIs.
        fSaveModel = pFree != NULL && pFree->nCexes < pFree->nCexMax;
        fSat = fUnknown = 0;
        if ( !pPars->fUseCbsMultiLit )
        {
            clkSolve = Abc_Clock();
            Status = Cec_TranCombSolveQuery( pCbs, pBatch,
                Vec_IntEntry(vQueries, i), fSaveModel, pProf );
            timeSolve += Abc_Clock() - clkSolve;
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
                if ( fStopAtFirstProof )
                    break;
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
            for ( k = iBeg; k < iEnd; k++ )
            {
                Cube[0] = t;
                Cube[1] = Abc_LitNot( Vec_IntEntry(vAndLeaves, k) );
                clkSolve = Abc_Clock();
                Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                    fSaveModel, pProf );
                timeSolve += Abc_Clock() - clkSolve;
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
                clkSolve = Abc_Clock();
                Status = Cec_TranCombSolveCube( pCbs, Cube, nLeaves + 1,
                    fSaveModel, pProf );
                timeSolve += Abc_Clock() - clkSolve;
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
            clkSolve = Abc_Clock();
            Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                fSaveModel, pProf );
            timeSolve += Abc_Clock() - clkSolve;
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
                clkSolve = Abc_Clock();
                Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                    fSaveModel, pProf );
                timeSolve += Abc_Clock() - clkSolve;
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
            if ( fStopAtFirstProof )
                break;
        }
    }
    pProf->timeCombSolve += timeSolve;
    pProf->timeRootCbsScreen += Abc_Clock() - clk - timeSolve;
    Cec_TranFreeSimStop( pFree );
    Cbs_ManStop( pCbs );
    return vStage;
}

// Return one status bit per candidate.  Seed candidate endpoints as ordinary
// equivalence classes and run one shared correspondence closure over exactly
// these relations.  This retains &scorr's standard BMC, SRM, CEX resimulation,
// class refinement, and induction fixed point without unrelated class search.
static Vec_Int_t * Cec_TranProveRootBatch( Gia_Man_t * p,
    Cec_TranCand_t const * pHelpers, int nHelpers,
    Cec_TranCand_t const * pCands, int nCands, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, int fCombOnly, Vec_Str_t ** pvStage )
{
    Cec_ParCor_t Cor;
    Gia_Man_t * pBatch;
    Gia_Obj_t * pObj;
    Vec_Int_t * vPairs, * vCombPairs, * vQueries;
    Vec_Int_t * vSeqPairs = NULL;
    Vec_Int_t * vAndLeaves = NULL;
    Vec_Str_t * vAndCounts = NULL;
    Vec_Int_t * vStatus = Vec_IntStart( nCands );
    Vec_Str_t * vStage;
    Cec_ProfCor_t CorrBefore;
    int i, RetValue = 1, nSeq = 0;
    int nSeqSplit = 0, nSeqUnknown = 0, nSeqRoots = 0;
    abctime clk, timeSeq = 0;
    memset( &Cor, 0, sizeof(Cor) );
    clk = Abc_Clock();
    pBatch = Cec_TranBuildRootBatch( p, pHelpers, nHelpers, pCands, nCands,
        !pPars->fUseCbsMultiLit ? 2 : 0,
        &vPairs, &vCombPairs, &vQueries,
        pPars->fUseCbsMultiLit ? &vAndLeaves : NULL,
        pPars->fUseCbsMultiLit ? &vAndCounts : NULL );
    clk = Abc_Clock() - clk;
    pProf->timeRootCbsGraph += clk;
    pProf->nRootSrmNodesMax = Abc_MaxInt(
        pProf->nRootSrmNodesMax, Gia_ManObjNum(pBatch) );
    vStage = Cec_TranProveCombBatch( pBatch, pCands, nCands,
        vCombPairs, vQueries, vAndLeaves, vAndCounts, pPars, pProf,
        0, NULL );
    if ( !fCombOnly )
        for ( i = 0; i < nCands; i++ )
            if ( Vec_StrEntry(vStage, i) == 0 )
                nSeq++;
    pProf->nSeqCands += nSeq;
    if ( nSeq )
    {
        int iPrevTarget = -1, nClass = 0;
        for ( i = 0; i < nCands; i++ )
            {
                if ( pCands[i].iTarget != iPrevTarget )
                {
                    if ( nClass )
                    {
                        pProf->nSeqClassSum += nClass + 1;
                        pProf->nSeqClassMax = Abc_MaxInt(
                            pProf->nSeqClassMax, nClass + 1 );
                    }
                    nSeqRoots++;
                    iPrevTarget = pCands[i].iTarget;
                    nClass = 0;
                }
                nClass++;
            }
        if ( nClass )
        {
            pProf->nSeqClassSum += nClass + 1;
            pProf->nSeqClassMax = Abc_MaxInt(
                pProf->nSeqClassMax, nClass + 1 );
        }
        pProf->nSeqRoots += nSeqRoots;
        Gia_ManSetPhase( pBatch );
        pBatch->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(pBatch) );
        Gia_ManForEachObj( pBatch, pObj, i )
            Gia_ObjSetRepr( pBatch, i, GIA_VOID );
        Gia_ManCreateValueRefs( pBatch );
        // Universally proved combinational relations remain in the same
        // hypothesis as induction helpers.  They are not sequential proof
        // obligations, but removing them can break a shared invariant.
        vSeqPairs = Vec_IntAlloc( 2 * (nHelpers + nCands) );
        for ( i = 0; i < nHelpers + nCands; i++ )
            Vec_IntPushTwo( vSeqPairs, Vec_IntEntry(vPairs, 2*i),
                Vec_IntEntry(vPairs, 2*i + 1) );
        Cec_TranSeedRootClasses( pBatch, vSeqPairs );
        pProf->nSeqSeeded += Vec_IntSize(vSeqPairs) / 2;
        pBatch->pNexts = Gia_ManDeriveNexts( pBatch );
        Cec_ManCorSetDefaultParams( &Cor );
        Cor.nFrames   = pPars->nFrames;
        Cor.nBTLimit  = pPars->nBTLimit;
        // Root scorr intentionally has no shared conflict cap.  -C is the
        // per-output limit; an UNKNOWN output is removed from only its own
        // speculative class by ordinary scorr refinement.  A shared cap would
        // make solve order turn one hard relation into a global early stop.
        Cor.nConfTotal = 0;
        Cor.nStepsMax = pPars->nStepsMax;
        Cor.fVerbose  = 0;
        Cor.pProfile  = pPars->fProfile ? &pProf->Corr : NULL;
        CorrBefore = pProf->Corr;
        clk = Abc_Clock();
        RetValue = Cec_ManLSCorrespondenceClasses( pBatch, &Cor );
        timeSeq = Abc_Clock() - clk;
        // Detailed correspondence counters use nanosecond ticks.  Attribute
        // the complete base phase, inductive SAT, and resimulation separately;
        // the remaining wall time is class management and fixed-point control.
        {
            abctime TimeSrm = 0, TimeBmc = 0, TimeIndSat = 0;
            abctime TimeResim = 0, Remain = timeSeq, Use;
            if ( pPars->fProfile )
            {
                double BmcHr = pProf->Corr.timeBmc - CorrBefore.timeBmc;
                double BmcSrmHr = pProf->Corr.timeBmcSrm - CorrBefore.timeBmcSrm;
                double BmcSimHr = pProf->Corr.timeBmcSim - CorrBefore.timeBmcSim;
                double IndSrmHr = pProf->Corr.timeIndSrm - CorrBefore.timeIndSrm;
                double IndSatHr = pProf->Corr.timeIndSat - CorrBefore.timeIndSat;
                double IndSimHr = pProf->Corr.timeIndSim - CorrBefore.timeIndSim;
                double BmcOtherHr = BmcHr - BmcSrmHr - BmcSimHr;
                if ( BmcOtherHr < 0 )
                    BmcOtherHr = 0;
                TimeSrm = (abctime)(1.0e-9 * (BmcSrmHr + IndSrmHr) * CLOCKS_PER_SEC);
                TimeBmc = (abctime)(1.0e-9 * BmcOtherHr * CLOCKS_PER_SEC);
                TimeIndSat = (abctime)(1.0e-9 * IndSatHr * CLOCKS_PER_SEC);
                TimeResim = (abctime)(1.0e-9 * (BmcSimHr + IndSimHr) * CLOCKS_PER_SEC);
                Use = TimeSrm < Remain ? TimeSrm : Remain;
                pProf->timeRootScorrGraph += Use; Remain -= Use;
                Use = TimeBmc < Remain ? TimeBmc : Remain;
                pProf->timeRootScorrBmc += Use; Remain -= Use;
                Use = TimeIndSat < Remain ? TimeIndSat : Remain;
                pProf->timeRootScorrIndSat += Use; Remain -= Use;
                Use = TimeResim < Remain ? TimeResim : Remain;
                pProf->timeRootScorrResim += Use; Remain -= Use;
                pProf->timeRootScorrOther += Remain;
            }
            else
                pProf->timeRootScorrOther += timeSeq;
        }
        if ( Cor.fCompleted )
            pProf->nSeqFixedRounds += Cor.nRoundsDone;
    }
    for ( i = 0; i < nCands; i++ )
    {
        int fProved = Vec_StrEntry(vStage, i) == 1;
        if ( !fProved && nSeq )
        {
            int fSameClass = Cec_TranRootBatchPairProved( pBatch,
                Vec_IntEntry(vPairs, 2*(nHelpers+i)),
                Vec_IntEntry(vPairs, 2*(nHelpers+i)+1) );
            int fBatchComplete = RetValue && Cor.fCompleted;
            // fConfStop can only accompany an incomplete correspondence run;
            // it is not the per-output UNKNOWN indication.  Keep the invariant
            // explicit so callers cannot accidentally reintroduce batch-wide
            // poisoning for ordinary solver UNKNOWNs.
            assert( !Cor.fConfStop || !Cor.fCompleted );
            fProved = fBatchComplete && fSameClass;
            if ( !fProved )
            {
                // As in ordinary &scorr, SAT counterexamples split only the
                // affected speculative class.  A global early stop is UNKNOWN;
                // a completed fixed point classifies each relation by whether
                // its endpoints survived in the same refined class.
                nSeqSplit += fBatchComplete && !fSameClass;
                nSeqUnknown += !fBatchComplete;
            }
        }
        if ( fProved && Vec_StrEntry(vStage, i) == 0 )
        {
            Vec_StrWriteEntry( vStage, i, 2 );
            pProf->nSeqProved++;
        }
        Vec_IntWriteEntry( vStatus, i, fProved );
    }
    pProf->nRootBatchCalls++;
    pProf->nRootBatchMax = Abc_MaxInt( pProf->nRootBatchMax,
        nHelpers + nCands );
    pProf->nSeqSplit += nSeqSplit;
    pProf->nSeqUnknown += nSeqUnknown;
    Vec_IntFree( vPairs );
    Vec_IntFree( vCombPairs );
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

// Among candidates that already passed signature/care matching and structural
// legality, root-only order is deterministic: constants first, then existing
// literals, then constructed recipes by increasing gate count.  Kind priority
// never admits an unmatched relation.  Gain/coverage and the canonical recipe
// key break ties without changing that kind order.
static int Cec_TranCandHeuristicCompare( const void * p0, const void * p1 )
{
    Cec_TranCand_t const * pC0 = (Cec_TranCand_t const *)p0;
    Cec_TranCand_t const * pC1 = (Cec_TranCand_t const *)p1;
    if ( pC0->nKind != pC1->nKind )
        return pC0->nKind - pC1->nKind;
    if ( pC0->nGates != pC1->nGates )
        return pC0->nGates - pC1->nGates;
    if ( pC0->fExactTemplate != pC1->fExactTemplate )
        return pC1->fExactTemplate - pC0->fExactTemplate;
    // The resub engine yields exact covers in decreasing sampled coverage /
    // residual-reduction order.  CI overlap is the next safe tie-break; it is
    // never used as a semantic filter.
    if ( pC0->nResubRank != pC1->nResubRank )
        return pC0->nResubRank - pC1->nResubRank;
    if ( pC0->nCiOverlap != pC1->nCiOverlap )
        return pC1->nCiOverlap - pC0->nCiOverlap;
    if ( pC0->fDivRescue != pC1->fDivRescue )
        return pC0->fDivRescue - pC1->fDivRescue;
    if ( pC0->Gain != pC1->Gain )
        return pC1->Gain - pC0->Gain;
    if ( pC0->iOut != pC1->iOut )
        return pC0->iOut - pC1->iOut;
    return pC0->nGates ? memcmp( pC0->Recipe, pC1->Recipe,
        sizeof(int) * 2 * pC0->nGates ) : 0;
}

// Group candidates by MFFC-ranked target and sort each root's alternatives by
// local gain.  Every layer is proved even after another alternative succeeds;
// the exact-cost portfolio at commit time then compares this order's winner
// with the q=1-primary winner and prevents a globally worse replacement.
// qStrictAll is grouped by target and gain-sorted within each group.  Store
// each [begin,end) range and the maximum direct/normal/rescue widths.  Layer
// lookup scans the small per-root range, exposing the cheap direct lane first,
// then legacy constructed candidates, then diverse-rescue candidates.  The
// metadata remains O(number of roots).
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

// The exact q=1 frontier is a conservative portfolio member.  It includes
// ordinary non-resub candidates and candidates explicitly generated by the
// legacy/direct/boundary q=1 path, but never admits a root which exists only
// because q>1 explored additional choices.  Comparing its cleanup cost with
// the full gain portfolio gives large q a strict q=1 bundle fallback.
// Exact dry-run size for one proof-stage subset, using the same winner
// selection and cleanup as the unified commit.  In particular, evaluate both
// the local-gain portfolio and the q=1-primary fallback, because the real
// commit may choose either one after exact cleanup.
// Counterfactual size profiles use the same per-target winner selection and
// cleanup as the real commit.  With only three candidate kinds, the six
// proper nonempty subsets are enough to recover exact Shapley contributions;
// the empty size is the input and the full size is the actual committed
// result.  Additional subsets expose the marginal utility of raw resub ranks
// above one, CEGAR waves after wave one, and the two sources currently folded
// into the existing kind (global lookup versus zero-gate resub recipes).
// Split the exact cleanup gain by both proof stage and candidate kind.  The
// combinational characteristic function starts from the input network.  The
// sequential characteristic function starts from the full combinational
// bundle, so its Shapley values add up to the incremental temporal reduction
// instead of double-counting reductions already certified combinationally.
// Select the best proved recipe for each target, then commit all selected
// targets together.  Different proved alternatives of one target form one
// equivalence class, so only the highest exact-gain representative is needed.
static int Cec_TranRootCompare( const void * p0, const void * p1 )
{
    Cec_TranRoot_t const * pR0 = (Cec_TranRoot_t const *)p0;
    Cec_TranRoot_t const * pR1 = (Cec_TranRoot_t const *)p1;
    if ( pR0->nMffc != pR1->nMffc )
        return pR1->nMffc - pR0->nMffc;
    return pR1->iObj - pR0->iObj;
}

static void Cec_TranMffcScratchClear( char * pMark, Vec_Int_t * vMarked )
{
    int i, iObj;
    Vec_IntForEachEntry( vMarked, iObj, i )
        pMark[iObj] = 0;
    Vec_IntClear( vMarked );
}

static inline int Cec_TranMffcIsBoundary( int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary )
{
    return iObj != iRoot &&
        ((pCovered && pCovered[iObj]) || (pUsed && pUsed[iObj]) ||
         (vBoundary && Vec_IntFind((Vec_Int_t *)vBoundary, iObj) >= 0));
}

// Dereference and restore one root using scratch reference counts.  Testing a
// fanin's original ref count in isolation is incorrect for reconvergent MFFCs:
// removing an earlier parent can make a later shared fanin reach zero.  The
// paired traversals below reproduce Gia_NodeDeref_rec/Gia_NodeRef_rec while
// honoring virtual-selection and candidate-support cutpoints.
static int Cec_TranMffcDeref_rec( Gia_Man_t * p, int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, int * pRefs,
    char * pMark, Vec_Int_t * vMarked )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    int iFan, Count = 1;
    assert( Gia_ObjIsAnd(pObj) );
    assert( !pMark[iObj] );
    pMark[iObj] = 1;
    Vec_IntPush( vMarked, iObj );
    iFan = Gia_ObjFaninId0p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) )
    {
        assert( pRefs[iFan] > 0 );
        if ( --pRefs[iFan] == 0 )
            Count += Cec_TranMffcDeref_rec( p, iFan, iRoot, pCovered,
                pUsed, vBoundary, pRefs, pMark, vMarked );
    }
    iFan = Gia_ObjFaninId1p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) )
    {
        assert( pRefs[iFan] > 0 );
        if ( --pRefs[iFan] == 0 )
            Count += Cec_TranMffcDeref_rec( p, iFan, iRoot, pCovered,
                pUsed, vBoundary, pRefs, pMark, vMarked );
    }
    return Count;
}

static int Cec_TranMffcRef_rec( Gia_Man_t * p, int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, int * pRefs )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    int iFan, Count = 1;
    assert( Gia_ObjIsAnd(pObj) );
    iFan = Gia_ObjFaninId0p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) &&
         pRefs[iFan]++ == 0 )
        Count += Cec_TranMffcRef_rec( p, iFan, iRoot, pCovered, pUsed,
            vBoundary, pRefs );
    iFan = Gia_ObjFaninId1p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) &&
         pRefs[iFan]++ == 0 )
        Count += Cec_TranMffcRef_rec( p, iFan, iRoot, pCovered, pUsed,
            vBoundary, pRefs );
    return Count;
}

static void Cec_TranMarkDynamicMffcWithRefs( Gia_Man_t * p, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, int * pRefs,
    char * pMark, Vec_Int_t * vMarked )
{
    int nDeref, nRef;
    assert( pRefs != NULL );
    assert( Gia_ObjIsAnd(Gia_ManObj(p, iRoot)) );
    Cec_TranMffcScratchClear( pMark, vMarked );
    nDeref = Cec_TranMffcDeref_rec( p, iRoot, iRoot, pCovered, pUsed,
        vBoundary, pRefs, pMark, vMarked );
    nRef = Cec_TranMffcRef_rec( p, iRoot, iRoot, pCovered, pUsed,
        vBoundary, pRefs );
    assert( nDeref == nRef && nDeref == Vec_IntSize(vMarked) );
}

static void Cec_TranMarkDynamicMffc( Gia_Man_t * p, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, char * pMark, Vec_Int_t * vMarked )
{
    Gia_Obj_t * pObj;
    int * pRefs;
    int i, iFan;
    assert( p->pRefs != NULL );
    assert( Gia_ObjIsAnd(Gia_ManObj(p, iRoot)) );
    Cec_TranMffcScratchClear( pMark, vMarked );
    pRefs = ABC_ALLOC( int, Gia_ManObjNum(p) );
    memcpy( pRefs, p->pRefs, sizeof(int) * Gia_ManObjNum(p) );
    // Covered objects have already been removed by earlier virtual choices.
    // Remove their structural fanin references from this scratch snapshot so
    // later roots see the true marginal MFFC.
    if ( pCovered )
    {
        Gia_ManForEachAnd( p, pObj, i )
            if ( pCovered[i] )
            {
                iFan = Gia_ObjFaninId0p( p, pObj );
                assert( pRefs[iFan] > 0 );
                pRefs[iFan]--;
                iFan = Gia_ObjFaninId1p( p, pObj );
                assert( pRefs[iFan] > 0 );
                pRefs[iFan]--;
            }
    }
    Cec_TranMarkDynamicMffcWithRefs( p, iRoot, pCovered, pUsed,
        vBoundary, pRefs, pMark, vMarked );
    ABC_FREE( pRefs );
}

static int Cec_TranMffcSelfTest()
{
    Gia_Man_t * p = Gia_ManStart( 16 );
    Vec_Int_t * vMarked = Vec_IntAlloc( 8 );
    Vec_Int_t * vBoundary = Vec_IntAlloc( 1 );
    Vec_Int_t * vPool;
    char * pMark, * pCovered, * pUsed;
    int iA, iB, iC, iX, iU, iV, iRoot, nStatic;
    iA = Gia_ManAppendCi( p );
    iB = Gia_ManAppendCi( p );
    iC = Gia_ManAppendCi( p );
    iX = Gia_ManAppendAnd( p, iA, iB );
    iU = Gia_ManAppendAnd( p, iX, iC );
    iV = Gia_ManAppendAnd( p, iX, Abc_LitNot(iC) );
    iRoot = Gia_ManAppendAnd( p, iU, iV );
    Gia_ManAppendCo( p, iRoot );
    Gia_ManCreateRefs( p );
    pMark = ABC_CALLOC( char, Gia_ManObjNum(p) );
    pCovered = ABC_CALLOC( char, Gia_ManObjNum(p) );
    pUsed = ABC_CALLOC( char, Gia_ManObjNum(p) );

    // The shared node X starts with ref=2 but reaches zero only after both U
    // and V are dereferenced.  A static ref==1 traversal incorrectly misses X.
    nStatic = Gia_NodeMffcSize( p, Gia_ManObj(p, Abc_Lit2Var(iRoot)) );
    Cec_TranMarkDynamicMffc( p, Abc_Lit2Var(iRoot), NULL, NULL, NULL,
        pMark, vMarked );
    assert( nStatic == 4 && Vec_IntSize(vMarked) == nStatic );

    // Candidate support is a hard boundary and therefore keeps X alive.
    Vec_IntPush( vBoundary, Abc_Lit2Var(iX) );
    Cec_TranMarkDynamicMffc( p, Abc_Lit2Var(iRoot), NULL, NULL,
        vBoundary, pMark, vMarked );
    assert( Vec_IntSize(vMarked) == 3 &&
        Vec_IntFind(vMarked, Abc_Lit2Var(iX)) < 0 );

    // Removing U virtually drops one reference of X.  Replacing V can then
    // remove X too; marking U as used instead must stop at X.
    pCovered[Abc_Lit2Var(iU)] = 1;
    Cec_TranMarkDynamicMffc( p, Abc_Lit2Var(iV), pCovered, NULL, NULL,
        pMark, vMarked );
    assert( Vec_IntSize(vMarked) == 2 &&
        Vec_IntFind(vMarked, Abc_Lit2Var(iX)) >= 0 );
    pCovered[Abc_Lit2Var(iU)] = 0;
    pUsed[Abc_Lit2Var(iX)] = 1;
    Cec_TranMarkDynamicMffc( p, Abc_Lit2Var(iV), NULL, pUsed, NULL,
        pMark, vMarked );
    assert( Vec_IntSize(vMarked) == 1 );
    pUsed[Abc_Lit2Var(iX)] = 0;

    // X is reconvergent and therefore lies in the exact MFFC even though the
    // lightweight ref==1 routing mask leaves it visible.  The A/B switch must
    // include X only when exact-MFFC internal divisors are enabled.
    vPool = Cec_TranCollectDivPool( p, Abc_Lit2Var(iRoot), 0, 0, 1,
        NULL, NULL, pMark, vMarked );
    assert( Vec_IntFind(vPool, Abc_Lit2Var(iX)) >= 0 );
    Vec_IntFree( vPool );
    vPool = Cec_TranCollectDivPool( p, Abc_Lit2Var(iRoot), 0, 0, 0,
        NULL, NULL, pMark, vMarked );
    assert( Vec_IntFind(vPool, Abc_Lit2Var(iX)) < 0 );
    Vec_IntFree( vPool );

    ABC_FREE( pMark );
    ABC_FREE( pCovered );
    ABC_FREE( pUsed );
    Vec_IntFree( vMarked );
    Vec_IntFree( vBoundary );
    Gia_ManStop( p );
    return 1;
}

static void Cec_TranCandCollectSupport( Cec_TranCand_t const * pCand,
    Vec_Int_t * vSupport )
{
    int i, Code, iObj;
    Vec_IntClear( vSupport );
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) )
            continue;
        iObj = Abc_Lit2Var( Code );
        if ( iObj && Vec_IntFind(vSupport, iObj) < 0 )
            Vec_IntPush( vSupport, iObj );
    }
}

// This mask is only a divisor-routing heuristic, not an MFFC computation.
// Following the initial ref==1 tree reaches the external boundary without
// excluding reconvergent internal nodes that are legal replacement supports.
// Candidate gain and selection always use the exact deref/ref MFFC above.
static void Cec_TranMarkDivExclusion_rec( Gia_Man_t * p, int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    char * pMark, Vec_Int_t * vMarked )
{
    Gia_Obj_t * pObj;
    int iFan;
    if ( Cec_TranMffcIsBoundary(iObj, iRoot, pCovered, pUsed, NULL) ||
         pMark[iObj] )
        return;
    pMark[iObj] = 1;
    Vec_IntPush( vMarked, iObj );
    pObj = Gia_ManObj( p, iObj );
    if ( !Gia_ObjIsAnd(pObj) )
        return;
    iFan = Gia_ObjFaninId0p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         Gia_ObjRefNumId(p, iFan) == 1 )
        Cec_TranMarkDivExclusion_rec( p, iFan, iRoot, pCovered, pUsed,
            pMark, vMarked );
    iFan = Gia_ObjFaninId1p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         Gia_ObjRefNumId(p, iFan) == 1 )
        Cec_TranMarkDivExclusion_rec( p, iFan, iRoot, pCovered, pUsed,
            pMark, vMarked );
}

static int Cec_TranCandDynamicGain( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, char const * pCovered,
    char const * pUsed, char * pMffc, Vec_Int_t * vMffc,
    Vec_Int_t * vSupport )
{
    int i, iObj;
    if ( pCovered[pCand->iTarget] || pUsed[pCand->iTarget] )
        return -1;
    Cec_TranCandCollectSupport( pCand, vSupport );
    Vec_IntForEachEntry( vSupport, iObj, i )
        if ( pCovered[iObj] )
            return -1;
    // The current recipe creates references to its support too.  Treat that
    // support as a boundary while computing this candidate's kill-set; this
    // is what makes an earlier equivalent inside the static MFFC legal.
    Cec_TranMarkDynamicMffc( p, pCand->iTarget, pCovered, pUsed,
        vSupport, pMffc, vMffc );
    Vec_IntForEachEntry( vSupport, iObj, i )
        if ( pMffc[iObj] )
            return -1;
    return Vec_IntSize(vMffc) - pCand->nGates;
}

static int Cec_TranCandFrozenGainWithRefs( Gia_Man_t * p,
    Cec_TranFrozenHash_t const * pHash, Cec_TranCand_t const * pCand,
    char const * pCovered, char const * pUsed, int * pRefs,
    char * pMffc, Vec_Int_t * vMffc, Vec_Int_t * vBoundary )
{
    int i, iObj, nNew;
    if ( pCovered[pCand->iTarget] || pUsed[pCand->iTarget] )
        return -1;
    Cec_TranCandCollectSupport( pCand, vBoundary );
    Vec_IntForEachEntry( vBoundary, iObj, i )
        if ( pCovered[iObj] )
            return -1;
    nNew = Cec_TranFrozenRecipeCost( p, pHash, pCand,
        pCovered, vBoundary );
    Cec_TranMarkDynamicMffcWithRefs( p, pCand->iTarget,
        pCovered, pUsed, vBoundary, pRefs, pMffc, vMffc );
    // A target used as its own replacement is the only boundary which the
    // MFFC traversal deliberately cannot cut.  Reject it as a cycle.
    Vec_IntForEachEntry( vBoundary, iObj, i )
        if ( pMffc[iObj] )
            return -1;
    return Vec_IntSize(vMffc) - nNew;
}

// Collect physical divisor nodes by increasing TFI distance.  The routing mask
// skips only the initial exclusive tree; reconvergent nodes deeper inside the
// exact MFFC remain legal because replacement support keeps them alive.  Exact
// dynamic gain later recomputes the kill-set with that support as a boundary.
// PI and RO objects are legal CIs, and all retained nodes precede the target.
static Vec_Int_t * Cec_TranCollectDivPool( Gia_Man_t * p, int iTarget,
    int nDepthMax, int nNodesMax, int fUseMffcDivs, char const * pCovered,
    char const * pUsed, char * pMffc, Vec_Int_t * vMffc )
{
    Vec_Int_t * vPool = Vec_IntAlloc( nNodesMax ? nNodesMax : 64 );
    Vec_Int_t * vFront = Vec_IntAlloc( 32 );
    Vec_Int_t * vNext = Vec_IntAlloc( 32 );
    Gia_Obj_t * pObj, * pFan;
    int d, i, k, iObj, iFan, fFull = 0;
    Cec_TranMffcScratchClear( pMffc, vMffc );
    if ( fUseMffcDivs )
        Cec_TranMarkDivExclusion_rec( p, iTarget, iTarget, pCovered, pUsed,
            pMffc, vMffc );
    else
        Cec_TranMarkDynamicMffc( p, iTarget, pCovered, pUsed, NULL,
            pMffc, vMffc );
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

// Rank a physical divisor by the number of opposite-label simulation pairs
// it separates.  If O0/O1 and I0/I1 are the off/on-set counts in the two
// divisor cofactors, O0*I1 + O1*I0 is exactly the number of off/on pairs cut
// by this divisor.  The score is phase-independent and is therefore a cheap
// proxy for the reduction in the residual dependency ambiguity.
typedef struct Cec_TranDivRank_t_ Cec_TranDivRank_t;
struct Cec_TranDivRank_t_
{
    word Score;
    int  CiOverlap;
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
    if ( pR1->CiOverlap != pR2->CiOverlap )
        return pR2->CiOverlap - pR1->CiOverlap;
    return pR1->iPos - pR2->iPos;
}

static Cec_TranDivRank_t * Cec_TranRankDivReservoir( Cec_TranSim_t * pSim,
    int iTarget, Vec_Int_t * vReservoir )
{
    Gia_Man_t * p = pSim->pGia;
    Cec_TranDivRank_t * pRanks = ABC_ALLOC( Cec_TranDivRank_t,
        Vec_IntSize(vReservoir) );
    word * pTarget = Cec_TranSimObj( pSim, iTarget );
    word * pDiv;
    word nOff0, nOff1, nOn0, nOn1;
    Vec_Int_t * vRootSupp = Vec_IntAlloc( 32 );
    Vec_Int_t * vDivSupp = Vec_IntAlloc( 32 );
    int i, k, s, iObj, RootNode = iTarget;
    Gia_ManCollectCis( p, &RootNode, 1, vRootSupp );
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
        Vec_IntClear( vDivSupp );
        Gia_ManCollectCis( p, &iObj, 1, vDivSupp );
        pRanks[i].CiOverlap = 0;
        Vec_IntForEachEntry( vDivSupp, iObj, k )
            pRanks[i].CiOverlap += Vec_IntFind(vRootSupp, iObj) >= 0;
        pRanks[i].iPos = i;
    }
    qsort( pRanks, Vec_IntSize(vReservoir),
        sizeof(Cec_TranDivRank_t), Cec_TranDivRankCompare );
    Vec_IntFree( vRootSupp );
    Vec_IntFree( vDivSupp );
    return pRanks;
}

// Ranking must choose the actual iterator input, not merely annotate an
// already-truncated BFS prefix.  Rewrite the reservoir in rank order and only
// then shrink it to B.  B=0 intentionally keeps the complete allowed TFI.
static void Cec_TranSelectRankedDivPool( Vec_Int_t * vReservoir,
    Cec_TranDivRank_t * pRanks, int nPoolMax )
{
    Vec_Int_t * vRanked = Vec_IntAlloc( Vec_IntSize(vReservoir) );
    int i, nKeep = nPoolMax ?
        Abc_MinInt(nPoolMax, Vec_IntSize(vReservoir)) :
        Vec_IntSize(vReservoir);
    for ( i = 0; i < nKeep; i++ )
        Vec_IntPush( vRanked, Vec_IntEntry(vReservoir, pRanks[i].iPos) );
    Vec_IntClear( vReservoir );
    Vec_IntAppend( vReservoir, vRanked );
    // pRanks is already sorted in exactly the order copied into vReservoir.
    // Normalize its positions so the selected pool and its rank metadata can
    // be reused by constructed discovery without ranking the same divisors a
    // second time.
    for ( i = 0; i < nKeep; i++ )
        pRanks[i].iPos = i;
    Vec_IntFree( vRanked );
}

// A zero-gate existing replacement does not need the resub cover engine.
// Scan all structural routes for an exact full-signature match and return the
// first local/diverse/global divisor (including complemented phase).  This is
// both broader than selecting 2B first and much cheaper than initializing the
// unate/pair machinery for a direct literal answer.
// Pool zero is byte-for-byte the former BFS prefix, preserving the strong
// first candidate.  Pools one through three first draw from boundary, local,
// and global routes respectively.  Later pools mix all unused routes.  Every
// alternate keeps a small set of informative BFS anchors so the dependency
// engine can combine new information with strong local divisors.
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
    abctime *   timeAttemptLast;
    int *       fAttemptUniqueLast;
    int         nAttemptCap;
};

static void Cec_TranDepScratchStart( Cec_TranDepScratch_t * p,
    int nSlots, int nDivsMax, int nChoices )
{
    p->vDivs = Vec_PtrAlloc( nDivsMax + 2 );
    p->vRecipes = Vec_WecAlloc( nChoices );
    p->pOff = ABC_ALLOC( word, nSlots );
    p->pOn  = ABC_ALLOC( word, nSlots );
    p->nAttemptsLast = 0;
    p->timeInitLast = p->timeSearchLast = 0;
    p->nAttemptCap = nChoices;
    p->timeAttemptLast = ABC_CALLOC( abctime, nChoices );
    p->fAttemptUniqueLast = ABC_CALLOC( int, nChoices );
}

static void Cec_TranDepScratchStop( Cec_TranDepScratch_t * p )
{
    Vec_PtrFree( p->vDivs );
    Vec_WecFree( p->vRecipes );
    ABC_FREE( p->pOff );
    ABC_FREE( p->pOn );
    ABC_FREE( p->timeAttemptLast );
    ABC_FREE( p->fAttemptUniqueLast );
}

static int Cec_TranCandFromDependency( Cec_TranSim_t * pSim,
    Cec_TranRoot_t const * pRoot, Vec_Int_t * vPool, word * pCare,
    int fStrict, Vec_Ptr_t * vDivs, Vec_Int_t * vRecipe,
    Cec_TranCand_t * pCand )
{
    int RawRecipe[2 * CEC_TRAN_RECIPE_NODES_MAX];
    int i, Code, RawOut, RawKind, RawGates;
    int nArray = Vec_IntSize(vRecipe);
    int nVars = Vec_PtrSize(vDivs);
    memset( pCand, 0, sizeof(*pCand) );
    pCand->iTarget = pRoot->iObj;
    pCand->nMffc = pRoot->nMffc;
    pCand->Gain = -1;
    pCand->fStrict = fStrict;
    pCand->nGates = nArray / 2;
    assert( pCand->nGates <= CEC_TRAN_RECIPE_NODES_MAX );
    if ( pCand->nGates )
        pCand->Recipe = Cec_TranRecipeAlloc( 2 * pCand->nGates );
    for ( i = 0; i < 2 * pCand->nGates; i++ )
        pCand->Recipe[i] = Cec_TranRecipeCodeFromResub(
            Vec_IntEntry(vRecipe, i), nVars, vPool );
    pCand->iOut = Cec_TranRecipeCodeFromResub(
        Vec_IntEntryLast(vRecipe), nVars, vPool );
    pCand->nKind = pCand->nGates ? CEC_TRAN_CAND_CONSTR :
        (Abc_Lit2Var(pCand->iOut) == 0 ?
            CEC_TRAN_CAND_CONST : CEC_TRAN_CAND_EXIST);
    if ( !Cec_TranRecipeStructurallyValid(pSim, pCand) )
    {
        Cec_TranCandRecipeRelease( pCand );
        memset( pCand, 0, sizeof(*pCand) );
        return 0;
    }
    RawGates = pCand->nGates;
    RawOut = pCand->iOut;
    RawKind = pCand->nKind;
    if ( RawGates )
        memcpy( RawRecipe, pCand->Recipe, sizeof(int) * 2 * RawGates );
    Cec_TranCandCanonicalizeRecipe( pCand );
    // Canonicalization is an optimization, never a semantic pruning rule.
    // If a future identity/compaction change alters the function, restore
    // and audit the raw recipe before deciding whether to reject it.
    if ( !Cec_TranRecipeStructurallyValid(pSim, pCand) ||
         !Cec_TranRecipeMatchesRoot(pSim, pCand, pCare) )
    {
        Cec_TranCandRecipeRelease( pCand );
        pCand->nGates = RawGates;
        pCand->iOut = RawOut;
        pCand->nKind = RawKind;
        if ( RawGates )
        {
            pCand->Recipe = Cec_TranRecipeAlloc( 2 * RawGates );
            memcpy( pCand->Recipe, RawRecipe,
                sizeof(int) * 2 * RawGates );
        }
        if ( !Cec_TranRecipeStructurallyValid(pSim, pCand) ||
             !Cec_TranRecipeMatchesRoot(pSim, pCand, pCare) )
        {
            Cec_TranCandRecipeRelease( pCand );
            memset( pCand, 0, sizeof(*pCand) );
            return 0;
        }
    }
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
    return 1;
}

static void * Cec_TranDependencyIteratorStart( Cec_TranSim_t * pSim,
    Cec_ParTran_t * pPars, Cec_TranRoot_t const * pRoot,
    Vec_Int_t * vPool, word * pCare, Cec_TranDepScratch_t * pScratch,
    int * pCursor )
{
    Vec_Ptr_t * vDivs = pScratch->vDivs;
    word Target, Care;
    int s, i, iObj, nLimit;
    Vec_PtrClear( vDivs );
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        Target = Cec_TranSimLit( pSim,
            Abc_Var2Lit(pRoot->iObj, 0), s );
        Care = pCare ? pCare[s] : ~(word)0;
        pScratch->pOff[s] = ~Target & Care;
        pScratch->pOn[s]  =  Target & Care;
    }
    Vec_PtrPushTwo( vDivs, pScratch->pOff, pScratch->pOn );
    Vec_IntForEachEntry( vPool, iObj, i )
        Vec_PtrPush( vDivs, Cec_TranSimObj(pSim, iObj) );
    // Simulation-guided resubstitution uses N* = min(|MFFC|, N): searching
    // beyond the removable cone cannot improve the root replacement budget.
    nLimit = pPars->fUseConstr ?
        Abc_MinInt( pPars->nDepNodesMax, pRoot->nMffc ) : 0;
    return Abc_ResubIteratorResumeStart( Vec_PtrArray(vDivs),
        Vec_PtrSize(vDivs), pSim->nSlots, nLimit, Vec_IntSize(vPool),
        0, 0, pCursor );
}

static int Cec_TranDependencyIteratorNext( Cec_TranSim_t * pSim,
    Cec_TranRoot_t const * pRoot, Vec_Int_t * vPool, word * pCare,
    Cec_TranDepScratch_t * pScratch, void * pIter,
    Cec_TranCand_t * pCand, int * pAttempt, int * pfExhausted )
{
    Vec_Int_t Recipe = {0};
    // Each route has its own iterator and therefore its own divisor-number
    // space.  pScratch->vDivs is only construction scratch and is overwritten
    // when the next route is initialized; using its final size here would
    // misclassify a recipe divisor as an internal gate.  Candidate decoding
    // only needs the current route's divisor count, not the truth-table
    // pointers, so provide a route-local header.
    Vec_Ptr_t Divs = {Vec_IntSize(vPool) + 2,
        Vec_IntSize(vPool) + 2, NULL};
    int * pArray = NULL, nArray, fInvalid;
    (void)pScratch;
    memset( pCand, 0, sizeof(*pCand) );
    nArray = Abc_ResubIteratorNext( pIter, &pArray, pAttempt,
        pfExhausted, &fInvalid );
    if ( *pfExhausted )
        return 0;
    if ( fInvalid )
        return -1;
    Recipe.nSize = Recipe.nCap = nArray;
    Recipe.pArray = pArray;
    if ( !Cec_TranCandFromDependency(pSim, pRoot, vPool, pCare, 1,
            &Divs, &Recipe, pCand) )
        return -1;
    if ( pCand->nGates == 0 )
    {
        Cec_TranCandRecipeRelease( pCand );
        return 0;
    }
    return 1;
}

static int Cec_TranCandCiOverlap( Cec_TranCand_t const * pCand,
    Vec_Int_t * vSupport, int const * pCiKeys,
    int const * pCiScores, int nCiMask )
{
    int i, iObj, k, Overlap = 0;
    Vec_IntClear( vSupport );
    Cec_TranCandCollectSupport( pCand, vSupport );
    Vec_IntForEachEntry( vSupport, iObj, i )
    {
        k = (int)(((unsigned)iObj * 0x9E3779B1u) & (unsigned)nCiMask);
        while ( pCiKeys[k] && pCiKeys[k] != iObj + 1 )
            k = (k + 1) & nCiMask;
        if ( pCiKeys[k] )
            Overlap += pCiScores[k];
    }
    return Overlap;
}

// Remove divisors already consumed by the current virtual bundle.
static void Cec_TranFilterCoveredDivPool( Vec_Int_t * vPool,
    char const * pCovered )
{
    int i, iObj, nKeep = 0;
    if ( pCovered == NULL )
        return;
    Vec_IntForEachEntry( vPool, iObj, i )
        if ( !pCovered[iObj] )
            Vec_IntWriteEntry( vPool, nKeep++, iObj );
    Vec_IntShrink( vPool, nKeep );
}

// Constant and Existing are independent lanes.  Constants contain exactly
// const0/const1.  Sequential Existing replacements are restricted to the same
// legal TFI divisor pool used by Build: global equivalences have already had
// their opportunity in the preceding &scorr pass.
static void Cec_TranCollectRootDirectTfi( Gia_Man_t * p,
    Cec_TranSim_t * pSim, Cec_ParTran_t * pPars,
    Cec_TranRoot_t const * pRoot, Vec_Int_t * vPool,
    Cec_TranCandVec_t const * pKnown, Cec_TranCandVec_t * pExist,
    Cec_TranDiscStat_t * pStat, Cec_TranProf_t * pProf )
{
    Cec_TranCand_t Cand;
    int f, i, iObj, iStart = pExist->nSize;
    for ( f = 0; f < 2; f++ )
    {
        pStat->nConstants++;
        pStat->nSigChecks++;
        if ( !Cec_TranSigMatchesRoot(pSim, pRoot->iObj,
                Abc_Var2Lit(0, f), NULL) )
        {
            pStat->nSigRejected++;
            continue;
        }
        pStat->nSigMatched++;
        Cand = Cec_TranCandCreateLiteral( pRoot->iObj,
            Abc_Var2Lit(0, f), pRoot->nMffc,
            CEC_TRAN_CAND_CONST, 1 );
        Cand.Gain = pRoot->nMffc;
        if ( !Cec_TranCandVecContains(pKnown, &Cand) )
            Cec_TranCandVecPush( pExist, Cand );
    }
    if ( pPars->fUseExisting )
        Vec_IntForEachEntry( vPool, iObj, i )
            for ( f = 0; f < 2; f++ )
            {
                int iLit = Abc_Var2Lit( iObj, f );
                pStat->nExisting++;
                pStat->nSigChecks++;
                if ( !Cec_TranSigMatchesRoot(pSim, pRoot->iObj, iLit, NULL) )
                {
                    pStat->nSigRejected++;
                    continue;
                }
                pStat->nSigMatched++;
                Cand = Cec_TranCandCreateLiteral( pRoot->iObj, iLit,
                    pRoot->nMffc, CEC_TRAN_CAND_EXIST, 1 );
                Cand.Gain = pRoot->nMffc;
                if ( !Cec_TranCandVecContains(pKnown, &Cand) &&
                     !Cec_TranCandVecContains(pExist, &Cand) )
                    Cec_TranCandVecPush( pExist, Cand );
            }
    Cec_TranCandVecEvalSortTail( p, pExist, iStart, pProf );
    Cec_TranDiscFinishRoot( pStat, 0, pExist->nSize - iStart );
}

// Root-only constructed discovery uses one paper-style TFI divisor pool.  A
// lightweight local iterator yields candidates in gate-count/template/coverage
// order; q bounds the per-root frontier.  Only its five scalar cursors survive
// this call; all heavyweight resub scratch is shared by the pass.
static void Cec_TranCollectRootConstructedIter( Gia_Man_t * p,
    Cec_TranSim_t * pSim, Cec_ParTran_t * pPars,
    Cec_TranRoot_t * pRoot, Cec_TranRootCursor_t * pCursor, int iWave,
    Cec_TranCandVec_t const * pKnown,
    char const * pCovered, char const * pUsed,
    char * pMffc, Vec_Int_t * vMffc, Vec_Int_t * vPool,
    Cec_TranDivRank_t const * pRanks,
    Cec_TranCandVec_t const * pExist,
    Cec_TranCandVec_t * pConstr, Cec_TranDepScratch_t * pDep,
    Cec_TranDiscStat_t * pStat, Cec_TranProf_t * pProf )
{
    int i, iAttempt, fExhausted = 0, fUnlimited;
    int nCiHash = 128, nCiMask;
    int IterStatus;
    int iConstrStart = pConstr->nSize;
    int nBudget, iProfWave = Abc_MinInt(iWave, 63);
    Vec_Int_t * vCandSupport = Vec_IntAlloc( 16 );
    int * pCiKeys, * pCiScores;
    void * pIter = NULL;
    Cec_TranCand_t Cand;
    abctime clk, clkAll, timePart;
    (void)p;
    (void)pCovered;
    (void)pUsed;
    (void)pMffc;
    (void)vMffc;
    // In legacy mode q is this call's frontier and q=0 drains the iterator.
    // In micro-batch mode -j is this call's frontier while q is the cumulative
    // number of accepted Build candidates allowed before the snapshot's one
    // selection/commit point.  The last call may therefore be smaller than j.
    fUnlimited = pPars->nRootProofBatch == 0 &&
        pPars->nRootConstrTop == 0;
    nBudget = Cec_TranRootBuildBudget( pPars, pCursor );
    pStat->nConstructed++;
    pStat->nSigChecks++;
    if ( pCursor->fExhausted || (!fUnlimited && nBudget <= 0) ||
         Vec_IntSize(vPool) == 0 )
    {
        pStat->nSigRejected++;
        Vec_IntFree( vCandSupport );
        return;
    }
    assert( pRanks != NULL );
    clkAll = Abc_Clock();
    while ( nCiHash < 2 * Vec_IntSize(vPool) )
        nCiHash <<= 1;
    nCiMask = nCiHash - 1;
    pCiKeys = ABC_CALLOC( int, nCiHash );
    pCiScores = ABC_CALLOC( int, nCiHash );
    for ( i = 0; i < Vec_IntSize(vPool); i++ )
    {
        int iObj = Vec_IntEntry(vPool, pRanks[i].iPos);
        int iHash = (int)(((unsigned)iObj * 0x9E3779B1u) &
            (unsigned)nCiMask);
        while ( pCiKeys[iHash] )
            iHash = (iHash + 1) & nCiMask;
        pCiKeys[iHash] = iObj + 1;
        pCiScores[iHash] = pRanks[i].CiOverlap;
    }
    pProf->timeRootDivPool += Abc_Clock() - clkAll;
    clk = Abc_Clock();
    pIter = Cec_TranDependencyIteratorStart( pSim,
        pPars, pRoot, vPool, NULL, pDep, pCursor->State );
    pCursor->nPages++;
    timePart = Abc_Clock() - clk;
    pProf->timeRootDepInit += timePart;
    pProf->timeRootWaveConstruct[iProfWave] += timePart;
    pProf->nRootResubIterInit++;
    pProf->nRootResubIterLive++;
    pProf->nRootResubIterLiveMax = Abc_MaxInt(
        pProf->nRootResubIterLiveMax, pProf->nRootResubIterLive );
    pProf->nRootWaveDepCalls[iProfWave]++;
    while ( fUnlimited || pConstr->nSize - iConstrStart < nBudget )
    {
        clk = Abc_Clock();
        iAttempt = 0;
        pProf->nRootResubIterNext++;
        IterStatus = Cec_TranDependencyIteratorNext(pSim, pRoot,
            vPool, NULL, pDep, pIter, &Cand, &iAttempt, &fExhausted);
        timePart = Abc_Clock() - clk;
        pProf->timeRootDepSearch += timePart;
        pProf->timeRootWaveConstruct[iProfWave] += timePart;
        if ( IterStatus <= 0 )
        {
            if ( IterStatus < 0 )
                pProf->nRootResubInvalid++;
            if ( fExhausted )
            {
                pCursor->fExhausted = 1;
                pProf->nRootResubIterExhausted++;
                break;
            }
            continue;
        }
        Cand.nResubRank = ++pCursor->nBuildYield;
        Cand.fExactTemplate = iAttempt != 5;
        Cand.fDivRescue = 0;
        Cand.fPrimaryFrontier = pCursor->nBuildYield == 1;
        Cand.nWave = iWave;
        Cand.Gain = Cand.nMffc - Cand.nGates;
        Cand.nCiOverlap = Cec_TranCandCiOverlap( &Cand,
            vCandSupport, pCiKeys, pCiScores, nCiMask );
        if ( Cand.Gain > 0 &&
             !Cec_TranCandVecContains(pKnown, &Cand) &&
             !Cec_TranCandVecContains(pExist, &Cand) &&
             !Cec_TranCandVecContains(pConstr, &Cand) )
        {
            Cec_TranCandVecPush( pConstr, Cand );
            pCursor->nBuildAccepted++;
            pProf->nRootWaveRecipes[iProfWave]++;
            pStat->nSigMatched++;
        }
        else
            pStat->nSigRejected++;
        Cec_TranCandRecipeRelease( &Cand );
    }
    if ( !fUnlimited && !fExhausted &&
         pConstr->nSize - iConstrStart >= nBudget )
        pProf->nRootResubIterCapped++;
    if ( pConstr->nSize == iConstrStart )
        pStat->nSigRejected++;
    Cec_TranDiscFinishRoot( pStat, 0, pConstr->nSize - iConstrStart );
    Abc_ResubIteratorResumeStop( pIter, pCursor->State );
    assert( pProf->nRootResubIterLive > 0 );
    pProf->nRootResubIterLive--;
    ABC_FREE( pCiKeys );
    ABC_FREE( pCiScores );
    Vec_IntFree( vCandSupport );
}

static int Cec_TranCandRootHeuristicCompare( const void * p0, const void * p1 )
{
    Cec_TranCand_t const * pC0 = (Cec_TranCand_t const *)p0;
    Cec_TranCand_t const * pC1 = (Cec_TranCand_t const *)p1;
    if ( pC0->nMffc != pC1->nMffc )
        return pC1->nMffc - pC0->nMffc;
    if ( pC0->iTarget != pC1->iTarget )
        return pC1->iTarget - pC0->iTarget;
    return Cec_TranCandHeuristicCompare( p0, p1 );
}

static void Cec_TranRootDiscoverOne( Gia_Man_t * p, Cec_TranSim_t * pSim,
    Cec_ParTran_t * pPars, Cec_TranRoot_t * pRoot,
    Cec_TranRootCursor_t * pCursor, int iWave,
    Cec_TranCandVec_t const * pKnown, char const * pSolved,
    char const * pCovered, char const * pUsed,
    char * pMffc, Vec_Int_t * vMffc, Cec_TranDepScratch_t * pDep,
    Cec_TranDiscStat_t * pDisc, Cec_TranProf_t * pProf,
    Cec_TranCandVec_t * pOut )
{
    Cec_TranCandVec_t Exist = {0}, Build = {0};
    Vec_Int_t * vPool;
    Cec_TranDivRank_t * pRanks = NULL;
    int i, nReservoirMax;
    abctime clk = Abc_Clock(), timePart;
    Cec_TranCandVecClear( pOut );
    // The heavyweight iterator manager is local to this call.  A later
    // no-commit wave restores only this root's scalar cursor onto the shared
    // manager, preserving exact continuation with bounded resident memory.
    (void)pSolved;
    nReservoirMax = pPars->nConstrBaseMax ?
        Abc_MaxInt(4 * pPars->nConstrBaseMax,
            pPars->nConstrBaseMax + 32) : 0;
    vPool = Cec_TranCollectDivPool( p, pRoot->iObj,
        pPars->nConstrMax, nReservoirMax,
        pPars->fUseMffcDivs,
        pCovered, pUsed, pMffc, vMffc );
    Cec_TranFilterCoveredDivPool( vPool, pCovered );
    if ( Vec_IntSize(vPool) )
    {
        pRanks = Cec_TranRankDivReservoir( pSim, pRoot->iObj, vPool );
        Cec_TranSelectRankedDivPool( vPool, pRanks,
            pPars->nConstrBaseMax );
    }
    timePart = Abc_Clock() - clk;
    pProf->timeRootDivPool += timePart;
    clk = Abc_Clock();
    // Under SEQ proof micro-batching Direct belongs only to the first batch.
    // The snapshot is immutable until the q horizon, so no later Constant or
    // Existing relation can become newly visible.  Legacy mode keeps its old
    // behavior, including the harmless Known-filtered rescan on later waves.
    if ( !pPars->fBuildOnly &&
         (pPars->nRootProofBatch == 0 || iWave == 0) )
        Cec_TranCollectRootDirectTfi( p, pSim, pPars, pRoot, vPool,
            pKnown, &Exist, pDisc, pProf );
    for ( i = 0; i < Exist.nSize; i++ )
        Exist.pArray[i].nWave = iWave;
    pProf->timeRootDirect += Abc_Clock() - clk;
    if ( pPars->fUseConstr )
        Cec_TranCollectRootConstructedIter( p, pSim, pPars, pRoot,
            pCursor, iWave,
            pKnown, pCovered, pUsed, pMffc, vMffc, vPool, pRanks,
            &Exist, &Build,
            pDep, pDisc, pProf );
    for ( i = 0; i < Exist.nSize; i++ )
        if ( !Cec_TranCandVecContains(pOut, Exist.pArray + i) )
            Cec_TranCandVecPush( pOut, Exist.pArray[i] );
    for ( i = 0; i < Build.nSize; i++ )
        if ( !Cec_TranCandVecContains(pOut, Build.pArray + i) )
            Cec_TranCandVecPush( pOut, Build.pArray[i] );
    if ( pOut->nSize > 1 )
        qsort( pOut->pArray, pOut->nSize, sizeof(Cec_TranCand_t),
            Cec_TranCandHeuristicCompare );
    Cec_TranCandVecStop( &Exist );
    Cec_TranCandVecStop( &Build );
    ABC_FREE( pRanks );
    Vec_IntFree( vPool );
}

static int Cec_TranRootRefreshPotential( Gia_Man_t * p,
    Cec_TranRoot_t * pRoots, int nRoots, char const * pCovered,
    char const * pUsed, char * pMffc, Vec_Int_t * vMffc,
    Cec_TranProf_t * pProf )
{
    int r, nPositive = 0, nOld;
    for ( r = 0; r < nRoots; r++ )
    {
        nOld = pRoots[r].nMffc;
        if ( pCovered[pRoots[r].iObj] || pUsed[pRoots[r].iObj] )
        {
            if ( pProf && nOld > 0 )
                pProf->nDirtyRootFreed++;
            pRoots[r].nMffc = 0;
            continue;
        }
        Cec_TranMarkDynamicMffc( p, pRoots[r].iObj, pCovered, pUsed,
            NULL, pMffc, vMffc );
        pRoots[r].nMffc = Vec_IntSize( vMffc );
        if ( pProf && nOld > 0 && pRoots[r].nMffc != nOld )
            pProf->nDirtyMffcChanged++;
        nPositive += pRoots[r].nMffc > 0;
    }
    qsort( pRoots, nRoots, sizeof(Cec_TranRoot_t), Cec_TranRootCompare );
    return nPositive;
}

static void Cec_TranRootPrepareSeqFrontier( Gia_Man_t * p,
    Cec_TranRoot_t * pRoots, int nRoots, Cec_TranCandVec_t const * pCands,
    char const * pCovered, char const * pUsed, char * pMffc,
    Vec_Int_t * vMffc, Vec_Int_t * vSupport,
    int fRefreshRoots, Cec_TranCandVec_t * pSeq, Cec_TranProf_t * pProf )
{
    int r, i, k, iObj, Gain, fSupportFreed;
    Cec_TranCandVecClear( pSeq );
    for ( i = 0; i < pCands->nSize; i++ )
        if ( pCands->pArray[i].nStatus == CEC_TRAN_STATE_CANDIDATE &&
             (pCovered[pCands->pArray[i].iTarget] ||
              pUsed[pCands->pArray[i].iTarget]) )
            pProf->nDirtyRootFreed++;
    // Root potential depends only on the permanent snapshot and the virtual
    // covered/used sets.  SEQ proof micro-batches change neither, so the first
    // batch computes and sorts it once and later batches safely reuse it.
    // The legacy -j0 path continues to request its historical refresh on every
    // call so this optimization cannot perturb existing scheduling behavior.
    if ( fRefreshRoots )
        Cec_TranRootRefreshPotential( p, pRoots, nRoots, pCovered, pUsed,
            pMffc, vMffc, pProf );
    for ( r = 0; r < nRoots && pRoots[r].nMffc > 0; r++ )
    {
        for ( i = 0; i < pCands->nSize; i++ )
        {
            Cec_TranCand_t Cand = pCands->pArray[i];
            if ( Cand.iTarget != pRoots[r].iObj ||
                 Cand.nStatus != CEC_TRAN_STATE_CANDIDATE )
                continue;
            if ( pCovered[Cand.iTarget] || pUsed[Cand.iTarget] )
            {
                pProf->nDirtyRootFreed++;
                continue;
            }
            Cec_TranCandCollectSupport( &Cand, vSupport );
            fSupportFreed = 0;
            Vec_IntForEachEntry( vSupport, iObj, k )
                fSupportFreed |= pCovered[iObj] != 0;
            if ( fSupportFreed )
            {
                pProf->nDirtySupportFreed++;
                continue;
            }
            Gain = Cec_TranCandDynamicGain( p, &Cand, pCovered, pUsed,
                pMffc, vMffc, vSupport );
            if ( Gain <= 0 )
            {
                pProf->nDirtyMffcChanged++;
                continue;
            }
            if ( Gain != Cand.Gain || Vec_IntSize(vMffc) != Cand.nMffc )
                pProf->nDirtyMffcChanged++;
            Cand.Gain = Gain;
            Cand.nMffc = pRoots[r].nMffc;
            Cec_TranCandVecPush( pSeq, Cand );
        }
    }
    if ( pSeq->nSize > 1 )
        qsort( pSeq->pArray, pSeq->nSize, sizeof(Cec_TranCand_t),
            Cec_TranCandRootHeuristicCompare );
}

// The conflict graph is stored by object incidence instead of materializing
// every edge.  An even incidence is a removable/MFFC membership and an odd
// incidence is replacement support.  Two vertices conflict on MFFC/MFFC or
// MFFC/support incidence; shared read-only support is intentionally legal.
typedef struct Cec_TranConflictGraph_t_ Cec_TranConflictGraph_t;
struct Cec_TranConflictGraph_t_
{
    Vec_Wec_t * vUsers;
    Vec_Int_t * vMffcBeg;
    Vec_Int_t * vMffcData;
    Vec_Int_t * vSuppBeg;
    Vec_Int_t * vSuppData;
    unsigned *  pSeen;
    unsigned    TravId;
    int         nVertices;
};

static void Cec_TranConflictGraphStart( Cec_TranConflictGraph_t * pGraph,
    int nObjs )
{
    memset( pGraph, 0, sizeof(Cec_TranConflictGraph_t) );
    pGraph->vUsers = Vec_WecStart( nObjs );
    pGraph->vMffcBeg = Vec_IntAlloc( 64 );
    pGraph->vMffcData = Vec_IntAlloc( 256 );
    pGraph->vSuppBeg = Vec_IntAlloc( 64 );
    pGraph->vSuppData = Vec_IntAlloc( 256 );
}

static void Cec_TranConflictGraphAdd( Cec_TranConflictGraph_t * pGraph,
    Vec_Int_t * vMffc, Vec_Int_t * vSupport )
{
    int iVertex = pGraph->nVertices++;
    int i, iObj;
    Vec_IntPush( pGraph->vMffcBeg, Vec_IntSize(pGraph->vMffcData) );
    Vec_IntForEachEntry( vMffc, iObj, i )
    {
        Vec_IntPush( pGraph->vMffcData, iObj );
        Vec_IntPush( Vec_WecEntry(pGraph->vUsers, iObj),
            Abc_Var2Lit(iVertex, 0) );
    }
    Vec_IntPush( pGraph->vSuppBeg, Vec_IntSize(pGraph->vSuppData) );
    Vec_IntForEachEntry( vSupport, iObj, i )
    {
        Vec_IntPush( pGraph->vSuppData, iObj );
        Vec_IntPush( Vec_WecEntry(pGraph->vUsers, iObj),
            Abc_Var2Lit(iVertex, 1) );
    }
}

static void Cec_TranConflictGraphFinalize( Cec_TranConflictGraph_t * pGraph )
{
    Vec_IntPush( pGraph->vMffcBeg, Vec_IntSize(pGraph->vMffcData) );
    Vec_IntPush( pGraph->vSuppBeg, Vec_IntSize(pGraph->vSuppData) );
    pGraph->pSeen = ABC_CALLOC( unsigned, pGraph->nVertices );
}

static void Cec_TranConflictGraphStop( Cec_TranConflictGraph_t * pGraph )
{
    Vec_WecFree( pGraph->vUsers );
    Vec_IntFree( pGraph->vMffcBeg );
    Vec_IntFree( pGraph->vMffcData );
    Vec_IntFree( pGraph->vSuppBeg );
    Vec_IntFree( pGraph->vSuppData );
    ABC_FREE( pGraph->pSeen );
    memset( pGraph, 0, sizeof(Cec_TranConflictGraph_t) );
}

static void Cec_TranConflictGraphCollectList(
    Cec_TranConflictGraph_t * pGraph, Vec_Int_t * vUsers,
    int iVertex, int fRequireMffc, Vec_Int_t * vNeighbors )
{
    int i, User, iOther;
    Vec_IntForEachEntry( vUsers, User, i )
    {
        if ( fRequireMffc && Abc_LitIsCompl(User) )
            continue;
        iOther = Abc_Lit2Var( User );
        if ( iOther == iVertex || pGraph->pSeen[iOther] == pGraph->TravId )
            continue;
        pGraph->pSeen[iOther] = pGraph->TravId;
        Vec_IntPush( vNeighbors, iOther );
    }
}

static void Cec_TranConflictGraphNeighbors(
    Cec_TranConflictGraph_t * pGraph, int iVertex,
    Vec_Int_t * vNeighbors )
{
    int i, iObj;
    Vec_IntClear( vNeighbors );
    if ( ++pGraph->TravId == 0 )
    {
        memset( pGraph->pSeen, 0,
            sizeof(unsigned) * pGraph->nVertices );
        pGraph->TravId = 1;
    }
    pGraph->pSeen[iVertex] = pGraph->TravId;
    for ( i = Vec_IntEntry(pGraph->vMffcBeg, iVertex);
          i < Vec_IntEntry(pGraph->vMffcBeg, iVertex + 1); i++ )
    {
        iObj = Vec_IntEntry( pGraph->vMffcData, i );
        Cec_TranConflictGraphCollectList( pGraph,
            Vec_WecEntry(pGraph->vUsers, iObj), iVertex, 0, vNeighbors );
    }
    for ( i = Vec_IntEntry(pGraph->vSuppBeg, iVertex);
          i < Vec_IntEntry(pGraph->vSuppBeg, iVertex + 1); i++ )
    {
        iObj = Vec_IntEntry( pGraph->vSuppData, i );
        Cec_TranConflictGraphCollectList( pGraph,
            Vec_WecEntry(pGraph->vUsers, iObj), iVertex, 1, vNeighbors );
    }
}

typedef struct Cec_TranWaveHeap_t_ Cec_TranWaveHeap_t;
struct Cec_TranWaveHeap_t_
{
    int * pHeap;
    int * pPos;
    long long * pLoss;
    int   nSize;
    Cec_TranCandVec_t const * pVertices;
};

static int Cec_TranWaveHeapBetter( Cec_TranWaveHeap_t const * pHeap,
    int iV0, int iV1 )
{
    Cec_TranCand_t const * pC0 = pHeap->pVertices->pArray + iV0;
    Cec_TranCand_t const * pC1 = pHeap->pVertices->pArray + iV1;
    // Compare Gain(c)^2 / (Gain(c) + Loss(c)) without division.  long double
    // avoids overflowing a 64-bit cross product on large proved pools while
    // the deterministic tie-breaks below keep equal priorities stable.
    long double Left = (long double)pC0->Gain * pC0->Gain *
        (pC1->Gain + pHeap->pLoss[iV1]);
    long double Right = (long double)pC1->Gain * pC1->Gain *
        (pC0->Gain + pHeap->pLoss[iV0]);
    if ( Left != Right )
        return Left > Right;
    if ( pC0->Gain != pC1->Gain )
        return pC0->Gain > pC1->Gain;
    if ( pC0->nMffc != pC1->nMffc )
        return pC0->nMffc > pC1->nMffc;
    if ( pC0->iTarget != pC1->iTarget )
        return pC0->iTarget > pC1->iTarget;
    return iV0 < iV1;
}

static void Cec_TranWaveHeapSwap( Cec_TranWaveHeap_t * pHeap,
    int i, int k )
{
    int Temp = pHeap->pHeap[i];
    pHeap->pHeap[i] = pHeap->pHeap[k];
    pHeap->pHeap[k] = Temp;
    pHeap->pPos[pHeap->pHeap[i]] = i;
    pHeap->pPos[pHeap->pHeap[k]] = k;
}

static void Cec_TranWaveHeapUp( Cec_TranWaveHeap_t * pHeap, int i )
{
    int Parent;
    while ( i > 0 )
    {
        Parent = (i - 1) >> 1;
        if ( !Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[i],
                pHeap->pHeap[Parent]) )
            break;
        Cec_TranWaveHeapSwap( pHeap, i, Parent );
        i = Parent;
    }
}

static void Cec_TranWaveHeapDown( Cec_TranWaveHeap_t * pHeap, int i )
{
    int Child;
    while ( (Child = 2 * i + 1) < pHeap->nSize )
    {
        if ( Child + 1 < pHeap->nSize &&
             Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[Child + 1],
                pHeap->pHeap[Child]) )
            Child++;
        if ( !Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[Child],
                pHeap->pHeap[i]) )
            break;
        Cec_TranWaveHeapSwap( pHeap, i, Child );
        i = Child;
    }
}

static void Cec_TranWaveHeapStart( Cec_TranWaveHeap_t * pHeap,
    Cec_TranCandVec_t const * pVertices, long long * pLoss )
{
    int i;
    memset( pHeap, 0, sizeof(Cec_TranWaveHeap_t) );
    pHeap->nSize = pVertices->nSize;
    pHeap->pHeap = ABC_ALLOC( int, pHeap->nSize );
    pHeap->pPos = ABC_ALLOC( int, pHeap->nSize );
    pHeap->pLoss = pLoss;
    pHeap->pVertices = pVertices;
    for ( i = 0; i < pHeap->nSize; i++ )
        pHeap->pHeap[i] = pHeap->pPos[i] = i;
    for ( i = pHeap->nSize / 2; i-- > 0; )
        Cec_TranWaveHeapDown( pHeap, i );
}

static void Cec_TranWaveHeapRemove( Cec_TranWaveHeap_t * pHeap,
    int iVertex )
{
    int i = pHeap->pPos[iVertex];
    if ( i < 0 )
        return;
    pHeap->pPos[iVertex] = -1;
    pHeap->nSize--;
    if ( i == pHeap->nSize )
        return;
    pHeap->pHeap[i] = pHeap->pHeap[pHeap->nSize];
    pHeap->pPos[pHeap->pHeap[i]] = i;
    if ( i > 0 && Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[i],
            pHeap->pHeap[(i - 1) >> 1]) )
        Cec_TranWaveHeapUp( pHeap, i );
    else
        Cec_TranWaveHeapDown( pHeap, i );
}

static int Cec_TranWaveHeapPop( Cec_TranWaveHeap_t * pHeap )
{
    int iVertex = pHeap->pHeap[0];
    Cec_TranWaveHeapRemove( pHeap, iVertex );
    return iVertex;
}

static void Cec_TranWaveHeapStop( Cec_TranWaveHeap_t * pHeap )
{
    ABC_FREE( pHeap->pHeap );
    ABC_FREE( pHeap->pPos );
    memset( pHeap, 0, sizeof(Cec_TranWaveHeap_t) );
}

// Compute the opportunity loss of one candidate in the current induced
// conflict graph.  Conflicting candidates are compressed by root: because at
// most one candidate of a root can be committed, that root contributes only
// the largest gain among its active conflicting candidates.
static long long Cec_TranConflictGraphRootLoss(
    Cec_TranConflictGraph_t * pGraph, Cec_TranCandVec_t const * pVertices,
    int iVertex, char const * pActive, Vec_Int_t * vNeighbors,
    int * pRootBest, unsigned * pRootSeen, unsigned * pRootTravId,
    int * pnActiveNeighbors )
{
    long long Loss = 0;
    int i, iOther, iRoot, Gain, nActive = 0;
    if ( ++*pRootTravId == 0 )
    {
        memset( pRootSeen, 0,
            sizeof(unsigned) * Vec_WecSize(pGraph->vUsers) );
        *pRootTravId = 1;
    }
    Cec_TranConflictGraphNeighbors( pGraph, iVertex, vNeighbors );
    Vec_IntForEachEntry( vNeighbors, iOther, i )
    {
        if ( !pActive[iOther] )
            continue;
        nActive++;
        iRoot = pVertices->pArray[iOther].iTarget;
        Gain = pVertices->pArray[iOther].Gain;
        assert( iRoot >= 0 && iRoot < Vec_WecSize(pGraph->vUsers) );
        assert( Gain > 0 );
        if ( pRootSeen[iRoot] != *pRootTravId )
        {
            pRootSeen[iRoot] = *pRootTravId;
            pRootBest[iRoot] = Gain;
            Loss += Gain;
        }
        else if ( pRootBest[iRoot] < Gain )
        {
            Loss += Gain - pRootBest[iRoot];
            pRootBest[iRoot] = Gain;
        }
    }
    if ( pnActiveNeighbors )
        *pnActiveNeighbors = nActive;
    return Loss;
}

// Dynamic root-compressed weighted-loss GWMIN.  The priority is
//
//        Gain(c)^2 / (Gain(c) + Loss(c)),
//
// where Loss(c) sums the best conflicting gain once per distinct root in the
// current induced graph.  Removing a closed neighborhood can only decrease
// the loss of its remaining neighbors, so only those heap entries are
// recomputed and promoted.
static long long Cec_TranConflictGraphGwmin(
    Cec_TranConflictGraph_t * pGraph, Cec_TranCandVec_t const * pVertices,
    char * pChosen, long long * pnEdges, int * pFirstGain )
{
    Cec_TranWaveHeap_t Heap;
    Vec_Int_t * vNeighbors = Vec_IntAlloc( 64 );
    Vec_Int_t * vRemoved = Vec_IntAlloc( 64 );
    Vec_Int_t * vDirty = Vec_IntAlloc( 64 );
    long long * pLoss = ABC_ALLOC( long long, pVertices->nSize );
    char * pActive = ABC_ALLOC( char, pVertices->nSize );
    char * pDirty = ABC_CALLOC( char, pVertices->nSize );
    int * pRootBest = ABC_ALLOC( int, Vec_WecSize(pGraph->vUsers) );
    unsigned * pRootSeen = ABC_CALLOC( unsigned,
        Vec_WecSize(pGraph->vUsers) );
    unsigned RootTravId = 0;
    long long SumDegree = 0, Weight = 0;
    int i, k, iVertex, iOther, nActiveNeighbors;
    memset( pChosen, 0, pVertices->nSize );
    memset( pActive, 1, pVertices->nSize );
    *pFirstGain = 0;
    for ( i = 0; i < pVertices->nSize; i++ )
    {
        pLoss[i] = Cec_TranConflictGraphRootLoss( pGraph, pVertices, i,
            pActive, vNeighbors, pRootBest, pRootSeen, &RootTravId,
            &nActiveNeighbors );
        SumDegree += nActiveNeighbors;
    }
    *pnEdges = SumDegree / 2;
    Cec_TranWaveHeapStart( &Heap, pVertices, pLoss );
    while ( Heap.nSize )
    {
        iVertex = Cec_TranWaveHeapPop( &Heap );
        assert( pActive[iVertex] );
        if ( Weight == 0 )
            *pFirstGain = pVertices->pArray[iVertex].Gain;
        pActive[iVertex] = 0;
        pChosen[iVertex] = 1;
        Weight += pVertices->pArray[iVertex].Gain;
        Vec_IntClear( vRemoved );
        Vec_IntPush( vRemoved, iVertex );
        Cec_TranConflictGraphNeighbors( pGraph, iVertex, vNeighbors );
        Vec_IntForEachEntry( vNeighbors, iOther, i )
            if ( pActive[iOther] )
            {
                pActive[iOther] = 0;
                Cec_TranWaveHeapRemove( &Heap, iOther );
                Vec_IntPush( vRemoved, iOther );
            }
        Vec_IntClear( vDirty );
        Vec_IntForEachEntry( vRemoved, iOther, i )
        {
            Cec_TranConflictGraphNeighbors( pGraph, iOther, vNeighbors );
            Vec_IntForEachEntry( vNeighbors, iVertex, k )
                if ( pActive[iVertex] && !pDirty[iVertex] )
                {
                    pDirty[iVertex] = 1;
                    Vec_IntPush( vDirty, iVertex );
                }
        }
        Vec_IntForEachEntry( vDirty, iVertex, i )
        {
            long long OldLoss = pLoss[iVertex];
            pLoss[iVertex] = Cec_TranConflictGraphRootLoss( pGraph,
                pVertices, iVertex, pActive, vNeighbors, pRootBest,
                pRootSeen, &RootTravId, NULL );
            assert( pLoss[iVertex] <= OldLoss );
            pDirty[iVertex] = 0;
            Cec_TranWaveHeapUp( &Heap, Heap.pPos[iVertex] );
        }
    }
    Cec_TranWaveHeapStop( &Heap );
    Vec_IntFree( vNeighbors );
    Vec_IntFree( vRemoved );
    Vec_IntFree( vDirty );
    ABC_FREE( pLoss );
    ABC_FREE( pActive );
    ABC_FREE( pDirty );
    ABC_FREE( pRootBest );
    ABC_FREE( pRootSeen );
    return Weight;
}

static int Cec_TranRootConsumeProved( Gia_Man_t * p,
    Cec_TranCandVec_t * pProved, char * pCovered, char * pUsed,
    char * pSolved, char * pMffc, Vec_Int_t * vMffc, Vec_Int_t * vSupport,
    Cec_TranCandVec_t * pSelected, Cec_TranProf_t * pProf )
{
    Cec_TranFrozenHash_t FrozenHash;
    Cec_TranConflictGraph_t Graph;
    Cec_TranCandVec_t Vertices = {0};
    Vec_Int_t * vProvedIds = Vec_IntAlloc( 64 );
    Gia_Obj_t * pObj;
    int * pRefs = ABC_ALLOC( int, Gia_ManObjNum(p) );
    char * pChosen;
    long long nEdges = 0, SelectedWeight;
    int i, k, iObj, iFan, iProved, Gain;
    int nSelected = 0, nGainEvals = 0, nInitialProved = 0;
    int nInitialPositive = 0, InitialMaxGain = 0, FirstGain = 0;

    // This is the one structural refresh for the frozen commit wave.
    memcpy( pRefs, p->pRefs, sizeof(int) * Gia_ManObjNum(p) );
    Gia_ManForEachAnd( p, pObj, i )
        if ( pCovered[i] )
        {
            iFan = Gia_ObjFaninId0p( p, pObj );
            assert( pRefs[iFan] > 0 );
            pRefs[iFan]--;
            iFan = Gia_ObjFaninId1p( p, pObj );
            assert( pRefs[iFan] > 0 );
            pRefs[iFan]--;
        }
    Cec_TranFrozenHashStart( p, &FrozenHash );
    Cec_TranConflictGraphStart( &Graph, Gia_ManObjNum(p) );
    for ( i = 0; i < pProved->nSize; i++ )
    {
        Cec_TranCand_t Cand = pProved->pArray[i];
        if ( Cand.nStatus != CEC_TRAN_STATE_PROVED_COMB &&
             Cand.nStatus != CEC_TRAN_STATE_PROVED_SEQ )
            continue;
        nInitialProved++;
        if ( pCovered[Cand.iTarget] || pUsed[Cand.iTarget] )
        {
            pProf->nDirtyRootFreed++;
            continue;
        }
        Gain = Cec_TranCandFrozenGainWithRefs( p, &FrozenHash, &Cand,
            pCovered, pUsed, pRefs, pMffc, vMffc, vSupport );
        nGainEvals++;
        if ( Gain <= 0 )
        {
            pProf->nDirtySupportFreed++;
            continue;
        }
        nInitialPositive++;
        InitialMaxGain = Abc_MaxInt( InitialMaxGain, Gain );
        if ( Gain != Cand.Gain || Vec_IntSize(vMffc) != Cand.nMffc )
            pProf->nDirtyMffcChanged++;
        Cand.Gain = Gain;
        Cand.nMffc = Vec_IntSize( vMffc );
        Cand.fPrimaryFrontier = 1;
        pProved->pArray[i].Gain = Gain;
        pProved->pArray[i].nMffc = Cand.nMffc;
        Cec_TranCandVecPush( &Vertices, Cand );
        Vec_IntPush( vProvedIds, i );
        Cec_TranConflictGraphAdd( &Graph, vMffc, vSupport );
    }
    Cec_TranConflictGraphFinalize( &Graph );
    pChosen = ABC_CALLOC( char, Vertices.nSize );
    SelectedWeight = Vertices.nSize ?
        Cec_TranConflictGraphGwmin( &Graph, &Vertices,
            pChosen, &nEdges, &FirstGain ) : 0;

    // Apply the independent-set decision as metadata only.  No selected
    // candidate is re-evaluated on a partially modified graph in this wave.
    for ( i = 0; i < Vertices.nSize; i++ )
        if ( pChosen[i] )
        {
            Cec_TranCand_t Cand = Vertices.pArray[i];
            int Lane = Cand.nProofLane ? Cand.nProofLane - 1 :
                (Cand.nStatus == CEC_TRAN_STATE_PROVED_COMB ? 0 : 1);
            int Phase = Cand.nProofLane ? Cand.nProofPhase : Lane;
            int Kind = Cand.nProofLane ? Cand.nProofKind : Cand.nKind;
            Cand.nStatus = CEC_TRAN_STATE_SELECTED;
            Cec_TranCandVecPush( pSelected, Cand );
            iProved = Vec_IntEntry( vProvedIds, i );
            pProved->pArray[iProved].nStatus = CEC_TRAN_STATE_SELECTED;
            for ( k = Vec_IntEntry(Graph.vMffcBeg, i);
                  k < Vec_IntEntry(Graph.vMffcBeg, i + 1); k++ )
            {
                iObj = Vec_IntEntry( Graph.vMffcData, k );
                assert( !pCovered[iObj] );
                pCovered[iObj] = pSolved[iObj] = 1;
            }
            for ( k = Vec_IntEntry(Graph.vSuppBeg, i);
                  k < Vec_IntEntry(Graph.vSuppBeg, i + 1); k++ )
            {
                iObj = Vec_IntEntry( Graph.vSuppData, k );
                assert( !pCovered[iObj] );
                pUsed[iObj] = 1;
            }
            pProf->nStageKindSelected[Phase][Kind]++;
            pProf->nStageKindMarginalAndGain[Phase][Kind] += Cand.Gain;
            pProf->nLaneKindSelected[Lane][Kind]++;
            nSelected++;
        }
    assert( (nSelected == 0) == (SelectedWeight == 0) );
    Abc_Print( 1, "stran-root commit selection: policy=commit-wave-root-loss-gwmin initial-proved=%d initial-positive=%d initial-max-gain=%d first-gain=%d rounds=%d gain-evals=%d graph-vertices=%d graph-edges=%lld selected-weight=%lld refreshes=1.\n",
        nInitialProved, nInitialPositive, InitialMaxGain, FirstGain,
        nSelected, nGainEvals, Vertices.nSize, nEdges, SelectedWeight );
    ABC_FREE( pChosen );
    ABC_FREE( pRefs );
    Cec_TranFrozenHashStop( &FrozenHash );
    Cec_TranConflictGraphStop( &Graph );
    Cec_TranCandVecStop( &Vertices );
    Vec_IntFree( vProvedIds );
    return nSelected;
}

static int Cec_TranCommitWaveSelfTest()
{
    Cec_TranConflictGraph_t Graph;
    Cec_TranCandVec_t Vertices = {0};
    Cec_TranCand_t Cand;
    Vec_Int_t * vMffc = Vec_IntAlloc( 2 );
    Vec_Int_t * vSupport = Vec_IntAlloc( 1 );
    Vec_Int_t * vNeighbors = Vec_IntAlloc( 8 );
    char Chosen[5] = {0}, Active[5] = {1, 1, 1, 1, 1};
    int RootBest[10] = {0};
    unsigned RootSeen[10] = {0}, RootTravId = 0;
    long long nEdges = 0, Weight, Loss;
    int i, FirstGain, nActiveNeighbors;
    Cec_TranConflictGraphStart( &Graph, 10 );
    for ( i = 0; i < 5; i++ )
    {
        memset( &Cand, 0, sizeof(Cand) );
        Cand.iTarget = i == 2 ? 2 : i + 1;
        Cand.Gain = i == 0 ? 20 : i == 1 ? 15 :
            i == 2 ? 14 : i == 3 ? 8 : 7;
        Cand.nMffc = 1;
        Cec_TranCandVecPush( &Vertices, Cand );
        Vec_IntClear( vMffc );
        Vec_IntClear( vSupport );
        if ( i == 0 )
            Vec_IntPush( vMffc, 1 );
        else if ( i == 1 || i == 2 )
            Vec_IntPush( vMffc, 2 ), Vec_IntPush( vSupport, 1 );
        else if ( i == 3 )
            Vec_IntPush( vMffc, 3 ), Vec_IntPush( vSupport, 1 );
        else
            Vec_IntPush( vMffc, 4 ), Vec_IntPush( vSupport, 2 );
        Cec_TranConflictGraphAdd( &Graph, vMffc, vSupport );
    }
    Cec_TranConflictGraphFinalize( &Graph );
    Loss = Cec_TranConflictGraphRootLoss( &Graph, &Vertices, 0,
        Active, vNeighbors, RootBest, RootSeen, &RootTravId,
        &nActiveNeighbors );
    // v0 sees three conflicting candidates, but v1 and v2 belong to the same
    // root.  Its loss is therefore max(15,14)+8, not 15+14+8.
    assert( nActiveNeighbors == 3 && Loss == 23 );
    Weight = Cec_TranConflictGraphGwmin( &Graph, &Vertices,
        Chosen, &nEdges, &FirstGain );
    // Root-loss GWMIN selects v0 first.  Removing its neighborhood also
    // removes both root-2 alternatives; v4 survives, drops from loss 15 to 0,
    // and is promoted into the independent set.
    assert( nEdges == 6 && Weight == 27 && FirstGain == 20 );
    assert( Chosen[0] && !Chosen[1] && !Chosen[2] &&
        !Chosen[3] && Chosen[4] );
    Cec_TranConflictGraphStop( &Graph );
    Cec_TranCandVecStop( &Vertices );
    Vec_IntFree( vMffc );
    Vec_IntFree( vSupport );
    Vec_IntFree( vNeighbors );
    return 1;
}

// Helper experiments deliberately have no selection heuristic or size cap.
// With helper reuse enabled, every unique, still-valid retained certificate is
// materialized into the temporary proof graph.  With it disabled, none is
// seeded.  Retention and future commit eligibility are identical in both
// modes, so the switch isolates only the inductive value of H.
static void Cec_TranPrepareHelpers( Gia_Man_t * p,
    Cec_TranCandVec_t const * pRetained,
    Cec_TranCandVec_t const * pObligations, int fUseHelpers, int fVerbose,
    Cec_TranProf_t * pProf, Cec_TranCandVec_t * pActive )
{
    Cec_TranCandVec_t Unique = {0};
    Vec_Int_t * vSupport = Vec_IntAlloc( 16 );
    int nObjs = Gia_ManObjNum(p);
    char * pEndpoints = ABC_CALLOC( char, nObjs );
    char * pClasses = ABC_CALLOC( char, nObjs );
    int i, k, iObj, nEndpoints = 0, nGates = 0;
    int nClasses = 0, nEstimate;
    Cec_TranCandVecClear( pActive );
    for ( i = 0; i < pRetained->nSize; i++ )
    {
        Cec_TranCand_t Cand = pRetained->pArray[i];
        if ( !Cec_TranCandVecContains(&Unique, &Cand) )
            Cec_TranCandVecPush( &Unique, Cand );
        else
            pProf->nHelperDedup++;
    }
    if ( fUseHelpers )
        for ( i = 0; i < Unique.nSize; i++ )
            Cec_TranCandVecPush( pActive, Unique.pArray[i] );
    for ( i = 0; i < pActive->nSize; i++ )
    {
        Cec_TranCand_t Cand = pActive->pArray[i];
        if ( !pClasses[Cand.iTarget] )
            pClasses[Cand.iTarget] = 1, nClasses++;
        if ( !pEndpoints[Cand.iTarget] )
            pEndpoints[Cand.iTarget] = 1, nEndpoints++;
        Cec_TranCandCollectSupport( &Cand, vSupport );
        Vec_IntForEachEntry( vSupport, iObj, k )
            if ( !pEndpoints[iObj] )
                pEndpoints[iObj] = 1, nEndpoints++;
        nGates += Cand.nGates;
    }
    nEstimate = Gia_ManObjNum(p) + nGates +
        4 * (pActive->nSize + pObligations->nSize);
    pProf->nHelperRetained = Abc_MaxInt(
        pProf->nHelperRetained, Unique.nSize );
    pProf->nHelperInjected += pActive->nSize;
    pProf->nHelperInactive += Unique.nSize - pActive->nSize;
    pProf->nHelperClasses += nClasses;
    pProf->nHelperEndpoints = Abc_MaxInt(pProf->nHelperEndpoints, nEndpoints);
    pProf->nHelperMaterialGates += nGates;
    if ( fVerbose )
        Abc_Print( 1, "stran-root helper batch: enabled=%s retained=%d active=%d inactive=%d classes=%d endpoints=%d materialized-gates=%d obligations=%d relation-total=%d estimated-srm-nodes=%d.\n",
            fUseHelpers ? "yes" : "no", Unique.nSize, pActive->nSize,
            Unique.nSize - pActive->nSize, nClasses, nEndpoints,
            nGates, pObligations->nSize,
            pActive->nSize + pObligations->nSize, nEstimate );
    Cec_TranCandVecStop( &Unique );
    Vec_IntFree( vSupport );
    ABC_FREE( pEndpoints );
    ABC_FREE( pClasses );
}

// Deterministic structural tests for the root pipeline changes which are too
// small to justify external fixtures: rank-before-B selection, TFI-only
// Existing lookup, zero-gain filtering, H/O proof-graph separation, proof
// history remap, and the temporary/permanent AIG boundary.
static int Cec_TranPipelineSelfTest()
{
    Cec_ParTran_t Pars;
    Cec_TranRoot_t Root;
    Cec_TranDiscStat_t Disc = {0};
    Cec_TranProf_t Prof = {0};
    Cec_TranCandVec_t Known = {0}, Direct = {0}, Cands = {0};
    Cec_TranCandVec_t Seq = {0}, Carry = {0}, History = {0}, Active = {0};
    Cec_TranCand_t DirectCand, ZeroGain;
    Cec_TranDivRank_t Ranks[3] = {{30, 0, 2}, {20, 0, 0}, {10, 0, 1}};
    Gia_Man_t * p = Gia_ManStart( 16 ), * pBatch;
    Cec_TranPatDb_t * pDb;
    Cec_TranSim_t * pSim;
    Vec_Int_t * vPool = Vec_IntAlloc( 3 );
    Vec_Int_t * vMffc = Vec_IntAlloc( 8 );
    Vec_Int_t * vSupport = Vec_IntAlloc( 8 );
    Vec_Int_t * vPairs, * vCombPairs, * vQueries, * vMap;
    char * pMffc, * pCovered, * pUsed;
    int i, iX, iY, iN1, iN2, nObjBefore, fFound = 0;
    Vec_IntPush( vPool, 11 );
    Vec_IntPush( vPool, 22 );
    Vec_IntPush( vPool, 33 );
    Cec_TranSelectRankedDivPool( vPool, Ranks, 2 );
    assert( Vec_IntSize(vPool) == 2 &&
        Vec_IntEntry(vPool, 0) == 33 && Vec_IntEntry(vPool, 1) == 11 );
    Vec_IntClear( vPool );

    iX = Gia_ManAppendCi( p );
    iY = Gia_ManAppendCi( p );
    iN1 = Gia_ManAppendAnd( p, iX, iY );
    iN2 = Gia_ManAppendAnd( p, iX, iY );
    Gia_ManAppendCo( p, iN2 );
    Gia_ManAppendCo( p, iN2 );
    Gia_ManSetRegNum( p, 1 );
    Gia_ManCreateRefs( p );
    Cec_ManTranSetDefaultParams( &Pars );
    Pars.nSimWords = 1;
    Pars.nSimFrames = 2;
    pDb = Cec_TranPatDbStart( p, 0 );
    pSim = Cec_TranSimStart( p, &Pars, pDb );
    Root.iObj = Abc_Lit2Var(iN2);
    Root.nMffc = Gia_NodeMffcSize( p, Gia_ManObj(p, Root.iObj) );
    Vec_IntPush( vPool, Abc_Lit2Var(iN1) );
    Cec_TranCollectRootDirectTfi( p, pSim, &Pars, &Root, vPool,
        &Known, &Direct, &Disc, &Prof );
    for ( i = 0; i < Direct.nSize; i++ )
        fFound |= Direct.pArray[i].nKind == CEC_TRAN_CAND_EXIST &&
            Direct.pArray[i].iOut == iN1;
    assert( fFound );
    Cec_TranCandVecClear( &Direct );
    Vec_IntClear( vPool );
    Cec_TranCollectRootDirectTfi( p, pSim, &Pars, &Root, vPool,
        &Known, &Direct, &Disc, &Prof );
    for ( i = 0; i < Direct.nSize; i++ )
        assert( Direct.pArray[i].nKind != CEC_TRAN_CAND_EXIST );

    pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
    pCovered = ABC_CALLOC( char, Gia_ManObjNum(p) );
    pUsed = ABC_CALLOC( char, Gia_ManObjNum(p) );
    memset( &ZeroGain, 0, sizeof(ZeroGain) );
    ZeroGain.iTarget = Root.iObj;
    ZeroGain.iDiv0 = iX;
    ZeroGain.iDiv1 = iY;
    ZeroGain.nMffc = Root.nMffc;
    ZeroGain.Gain = 0;
    ZeroGain.nGates = 1;
    ZeroGain.Recipe = Cec_TranRecipeAlloc( 2 );
    ZeroGain.Recipe[0] = iX;
    ZeroGain.Recipe[1] = iY;
    ZeroGain.iOut = Cec_TranRecipeGateCode( 0, 0 );
    ZeroGain.nKind = CEC_TRAN_CAND_CONSTR;
    ZeroGain.nStatus = CEC_TRAN_STATE_CANDIDATE;
    Cec_TranCandVecPush( &Cands, ZeroGain );
    Cec_TranRootPrepareSeqFrontier( p, &Root, 1, &Cands,
        pCovered, pUsed, pMffc, vMffc, vSupport, 1, &Seq, &Prof );
    assert( Seq.nSize == 0 );

    DirectCand = Cec_TranCandCreateLiteral( Root.iObj, iN1,
        Root.nMffc, CEC_TRAN_CAND_EXIST, 1 );
    DirectCand.nProofStage = 2;
    DirectCand.nProofLane = 2;
    DirectCand.nProofPhase = 1;
    DirectCand.nProofKind = CEC_TRAN_CAND_EXIST;
    DirectCand.nStatus = CEC_TRAN_STATE_PROVED_SEQ;
    Cec_TranCandVecPush( &Carry, DirectCand );
    vMap = Vec_IntStartFull( Gia_ManObjNum(p) );
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        Vec_IntWriteEntry( vMap, i, Abc_Var2Lit(i, 0) );
    Cec_TranRemapProofHistory( p, vMap, &Carry, &History, &Prof );
    assert( History.nSize == 1 &&
        History.pArray[0].nStatus == CEC_TRAN_STATE_PROVED_SEQ &&
        History.pArray[0].nProofLane == 2 &&
        History.pArray[0].nProofPhase == 1 &&
        History.pArray[0].nProofKind == CEC_TRAN_CAND_EXIST );
    Cec_TranPrepareHelpers( p, &History, &Cands, 1, 0, &Prof, &Active );
    assert( Active.nSize == History.nSize );
    Cec_TranPrepareHelpers( p, &History, &Cands, 0, 0, &Prof, &Active );
    assert( Active.nSize == 0 );

    nObjBefore = Gia_ManObjNum(p);
    pBatch = Cec_TranBuildRootBatch( p, History.pArray, 1,
        Cands.pArray, 1, 1, &vPairs, &vCombPairs, &vQueries,
        NULL, NULL );
    assert( Vec_IntSize(vPairs) == 4 &&
        Vec_IntSize(vCombPairs) == 2 && Vec_IntSize(vQueries) == 1 );
    assert( Gia_ManObjNum(p) == nObjBefore );
    Gia_ManStop( pBatch );
    Vec_IntFree( vPairs );
    Vec_IntFree( vCombPairs );
    Vec_IntFree( vQueries );
    Vec_IntFree( vMap );
    Cec_TranSimStop( pSim );
    Cec_TranPatDbStop( pDb );
    Cec_TranCandRecipeRelease( &ZeroGain );
    Cec_TranCandVecStop( &Known );
    Cec_TranCandVecStop( &Direct );
    Cec_TranCandVecStop( &Cands );
    Cec_TranCandVecStop( &Seq );
    Cec_TranCandVecStop( &Carry );
    Cec_TranCandVecStop( &History );
    Cec_TranCandVecStop( &Active );
    Vec_IntFree( vPool );
    Vec_IntFree( vMffc );
    Vec_IntFree( vSupport );
    ABC_FREE( pMffc );
    ABC_FREE( pCovered );
    ABC_FREE( pUsed );
    Gia_ManStop( p );
    return 1;
}

// Prove the complete selected frontier on one immutable snapshot.  COMB-only
// closure stops after CBS; the SEQ phase sends every CBS-unproved submitted
// relation to one shared correspondence fixed point.
static int Cec_TranRootProvePortfolio( Gia_Man_t * p,
    Cec_TranCandVec_t const * pHelpers, Cec_TranCandVec_t * pPortfolio,
    Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, Cec_TranCandVec_t * pProved, int fCombOnly,
    int iPhase )
{
    Vec_Int_t * vStatus;
    Vec_Str_t * vStage;
    Cec_TranCand_t Cand;
    int i, iStage, nNew = 0;
    if ( pPortfolio->nSize == 0 )
        return 0;
    qsort( pPortfolio->pArray, pPortfolio->nSize, sizeof(Cec_TranCand_t),
        Cec_TranCandRootHeuristicCompare );
    for ( i = 0; i < pPortfolio->nSize; i++ )
    {
        pProf->nStageKindSubmitted[iPhase][pPortfolio->pArray[i].nKind]++;
        pProf->nLaneKindSubmitted[0][pPortfolio->pArray[i].nKind]++;
    }
    vStatus = Cec_TranProveRootBatch( p,
        pHelpers ? pHelpers->pArray : NULL,
        pHelpers ? pHelpers->nSize : 0,
        pPortfolio->pArray, pPortfolio->nSize,
        pPars, pProf, fCombOnly, &vStage );
    for ( i = 0; i < pPortfolio->nSize; i++ )
    {
        iStage = Vec_StrEntry( vStage, i );
        // A COMB-only closure pass stops before correspondence.  Candidates
        // rejected by CBS are therefore not SEQ submissions in this pass.
        if ( !fCombOnly && iStage != 1 )
            pProf->nLaneKindSubmitted[1][pPortfolio->pArray[i].nKind]++;
        if ( !Vec_IntEntry(vStatus, i) )
            continue;
        assert( iStage == 1 || iStage == 2 );
        Cand = pPortfolio->pArray[i];
        Cand.nProofStage = iStage;
        Cand.nProofLane = iStage;
        Cand.nProofPhase = iPhase;
        Cand.nProofKind = Cand.nKind;
        Cand.nStatus = iStage == 1 ?
            CEC_TRAN_STATE_PROVED_COMB : CEC_TRAN_STATE_PROVED_SEQ;
        pProf->nStageKindProved[iPhase][Cand.nKind]++;
        pProf->nLaneKindProved[iStage - 1][Cand.nKind]++;
        if ( Cec_TranCandVecContains(pProved, &Cand) )
            continue;
        Cec_TranCandVecPush( pProved, Cand );
        nNew++;
    }
    Vec_IntFree( vStatus );
    Vec_StrFree( vStage );
    return nNew;
}

static Gia_Man_t * Cec_TranCommitSelectedRootOnly( Gia_Man_t * p,
    Cec_TranCandVec_t * pSelected, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, Cec_TranCandVec_t const * pCarry,
    Cec_TranCandVec_t * pHistory )
{
    Gia_Man_t * pDup, * pClean;
    Gia_Obj_t * pObj;
    Vec_Int_t * vSelected, * vDupToClean, * vOldToClean;
    long long Marginal = 0;
    int i, iLit, iMapped, Gain, fProved = 1;
    abctime clk;
    if ( pSelected->nSize == 0 )
    {
        Cec_TranCandVecClear( pHistory );
        for ( i = 0; i < pCarry->nSize; i++ )
            Cec_TranCandVecPush( pHistory, pCarry->pArray[i] );
        return p;
    }
    vSelected = Vec_IntAlloc( pSelected->nSize );
    for ( i = 0; i < pSelected->nSize; i++ )
        Vec_IntPush( vSelected, i ), Marginal += pSelected->pArray[i].Gain;
    clk = Abc_Clock();
    pDup = Cec_TranDupRootBundle( p, pSelected->pArray, vSelected );
    pProf->timeRootBundleDup += Abc_Clock() - clk;
    clk = Abc_Clock();
    pClean = Cec_TranCleanupKeepRegs( pDup, &vDupToClean );
    pProf->timeRootCleanup += Abc_Clock() - clk;
    vOldToClean = Vec_IntStartFull( Gia_ManObjNum(p) );
    Gia_ManForEachObj( p, pObj, i )
    {
        iLit = Cec_TranMapLitByValue( p, Abc_Var2Lit(i, 0) );
        if ( iLit < 0 || Abc_Lit2Var(iLit) >= Vec_IntSize(vDupToClean) )
            continue;
        iMapped = Vec_IntEntry( vDupToClean, Abc_Lit2Var(iLit) );
        if ( iMapped >= 0 )
            Vec_IntWriteEntry( vOldToClean, i,
                Abc_LitNotCond(iMapped, Abc_LitIsCompl(iLit)) );
    }
    Cec_TranRemapProofHistory( pClean, vOldToClean, pCarry,
        pHistory, pProf );
    clk = Abc_Clock();
    Gain = Cec_TranGain( p, pClean );
    pProf->timeRootExactAudit += Abc_Clock() - clk;
    assert( Gain > 0 && Gain >= Marginal );
    assert( Gia_ManRegNum(p) == Gia_ManRegNum(pClean) );
    if ( pPars->fShadow )
    {
        clk = Abc_Clock();
        fProved = Cec_TranProveWhole( p, pDup, pPars, pProf );
        pProf->timeShadow += Abc_Clock() - clk;
    }
    assert( fProved );
    pProf->nRootBundleAndGain = Gain;
    pProf->nRootBundleRegGain = Gia_ManRegNum(p) - Gia_ManRegNum(pClean);
    pProf->nRootBundleCommits = pSelected->nSize;
    Gia_ManStop( p );
    Gia_ManStop( pDup );
    Vec_IntFree( vSelected );
    Vec_IntFree( vDupToClean );
    Vec_IntFree( vOldToClean );
    return pClean;
}

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

        // The simulation is only a structural/signature guard for certificates
        // remapped through cleanup.  This loop performs no candidate discovery
        // and makes no proof calls.
        pDb = Cec_TranPatDbStart( p, 0 );
        Gia_ManCreateRefs( p );
        pSim = Cec_TranSimStart( p, pPars, pDb );
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
        if ( Proved.nSize )
            nSelected = Cec_TranRootConsumeProved( p, &Proved,
                pCovered, pUsed, pSolved, pMffc, vMffc, vSupport,
                &Selected, &Prof );
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
    int nRootWaves, int iPhase )
{
    static char const * pStage[2] = { "COMB", "SEQ" };
    static char const * pLane[2] = { "CBS", "SCORR" };
    static char const * pKind[3] = { "CONSTANT", "EXISTING", "BUILD" };
    abctime Times[19] = { p->timeRootSimSig, p->timeRootRefresh,
        p->timeRootDirect, p->timeRootDivCi, p->timeRootResubInit,
        p->timeRootResubEnumCanon, p->timeRootCbsGraph,
        p->timeRootCbsScreen, p->timeRootCbsSolve, p->timeRootScorrGraph,
        p->timeRootScorrBmc, p->timeRootScorrIndSat,
        p->timeRootScorrResim, p->timeRootScorrOther, p->timeRootPostSelect,
        p->timeRootBundleDup, p->timeRootCleanup, p->timeRootExactAudit,
        p->timeShadow };
    char const * Names[19] = { "simulation/signatures", "root/MFFC/dirty-refresh",
        "direct constant/existing generation", "divisor-reservoir/CI-ranking",
        "resub-initialization", "resub-enumeration/canonicalization",
        "CBS-graph/build", "CBS-screen", "CBS-solve",
        "shared-scorr-graph/SRM", "shared-scorr-BMC/base",
        "shared-scorr-induction/SAT", "shared-scorr-resimulation/refinement",
        "shared-scorr-fixed-point/other", "post-fixed-point-selection/waves",
        "final-bundle-duplication", "cleanup", "exact-gain-audit", "shadow-audit" };
    int i, s, k, SumSelected = 0, SumProved[2] = {0};
    int SumLaneSelected = 0, SumLaneProved[2] = {0};
    abctime SumTime = 0, Unprofiled;
    long long SumMarginal = 0;
    Abc_Print( 1, "stran-root time profile: total=%.6f sec.\n",
        Cec_TranTimeSec(p->timeTotal) );
    for ( i = 0; i < 19; i++ )
    {
        Abc_Print( 1, "  %-42s %.6f sec %6.2f%%\n", Names[i],
            Cec_TranTimeSec(Times[i]), p->timeTotal ?
            100.0 * Times[i] / p->timeTotal : 0.0 );
        SumTime += Times[i];
    }
    Unprofiled = p->timeTotal > SumTime ? p->timeTotal - SumTime : 0;
    Abc_Print( 1, "stran-root experiment-time profile: schema=5 total-sec=%.6f sim-sec=%.6f root-refresh-sec=%.6f direct-discovery-sec=%.6f divisor-discovery-sec=%.6f resub-init-sec=%.6f resub-enum-sec=%.6f cbs-graph-sec=%.6f cbs-screen-sec=%.6f cbs-solve-sec=%.6f scorr-graph-sec=%.6f scorr-bmc-sec=%.6f scorr-induction-sec=%.6f scorr-resim-sec=%.6f scorr-other-sec=%.6f selection-repair-sec=%.6f bundle-sec=%.6f cleanup-sec=%.6f exact-audit-sec=%.6f shadow-sec=%.6f unprofiled-sec=%.6f\n",
        Cec_TranTimeSec(p->timeTotal), Cec_TranTimeSec(p->timeRootSimSig),
        Cec_TranTimeSec(p->timeRootRefresh), Cec_TranTimeSec(p->timeRootDirect),
        Cec_TranTimeSec(p->timeRootDivCi), Cec_TranTimeSec(p->timeRootResubInit),
        Cec_TranTimeSec(p->timeRootResubEnumCanon), Cec_TranTimeSec(p->timeRootCbsGraph),
        Cec_TranTimeSec(p->timeRootCbsScreen), Cec_TranTimeSec(p->timeRootCbsSolve),
        Cec_TranTimeSec(p->timeRootScorrGraph), Cec_TranTimeSec(p->timeRootScorrBmc),
        Cec_TranTimeSec(p->timeRootScorrIndSat), Cec_TranTimeSec(p->timeRootScorrResim),
        Cec_TranTimeSec(p->timeRootScorrOther), Cec_TranTimeSec(p->timeRootPostSelect),
        Cec_TranTimeSec(p->timeRootBundleDup), Cec_TranTimeSec(p->timeRootCleanup),
        Cec_TranTimeSec(p->timeRootExactAudit), Cec_TranTimeSec(p->timeShadow),
        Cec_TranTimeSec(Unprofiled) );
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
    Abc_Print( 1, "stran-root experiment-summary profile: schema=5 phase=%s selected-roots=%d marginal-and=%lld final-and-gain=%lld final-reg-gain=%lld and-before=%d and-after=%d reg-before=%d reg-after=%d\n",
        iPhase ? "seq" : "comb", SumSelected, SumMarginal, p->nRootBundleAndGain,
        p->nRootBundleRegGain, nAndBefore, nAndAfter, nRegBefore, nRegAfter );
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
    Cec_TranCandVec_t * pHistory )
{
    Cec_TranProf_t Prof = {0};
    Cec_TranDiscStat_t Disc = {0};
    Cec_TranCandVec_t Known = {0}, RootCands = {0}, Page = {0};
    Cec_TranCandVec_t ProofCands = {0};
    Cec_TranCandVec_t BatchProved = {0}, Proved = {0}, Selected = {0};
    Cec_TranCandVec_t HistoryLive = {0}, Active = {0}, Carry = {0};
    Cec_TranRoot_t * pRoots;
    Cec_TranRootCursor_t * pCursors;
    Cec_TranSim_t * pSim;
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
    int nFrontierRefreshes = 0, nFrontierRefreshReuses = 0;
    long long nFrontierCandidates = 0, nKnownCandidateScansAvoided = 0;
    int iPhase = fCombOnly ? 0 : 1;
    int nCandCalls = 0, nCandSum = 0, nCandMax = 0;
    int nCandHist[10] = {0};
    int nAndBefore = Gia_ManAndNum( p ), nRegBefore = Gia_ManRegNum( p );
    abctime clkTotal = Abc_Clock(), clk;
    pDb = Cec_TranPatDbStart( p, 0 );
    Gia_ManCreateRefs( p );
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
    clk = Abc_Clock();
    pSim = Cec_TranSimStart( p, pPars, pDb );
    Prof.timeRootSimSig += Abc_Clock() - clk;
    Abc_ResubPrepareManager( pSim->nSlots );
    Cec_TranDepScratchStart( &Dep, pSim->nSlots,
        pPars->nConstrBaseMax ? pPars->nConstrBaseMax : 64, 1 );
    Abc_Print( 1, "stran-root: round=%d phase=%s snapshot=immutable scheduler=serial-root-iterator/all-candidates selection=%s candidates=%s q-build-per-root=%d proof-build-batch-per-root=%d helpers=%s divisor-route=ranked-TFI-only existing=TFI-pool mffc-divisors=%s.\n",
        iRound + 1, fCombOnly ? "comb" : "seq",
        fMicroBatch ? "deferred-q-horizon-root-loss-gwmin" :
            "commit-wave-root-loss-gwmin",
        pPars->fBuildOnly ? "build-only" : "constant/existing/build",
        pPars->nRootConstrTop, pPars->nRootProofBatch,
        pPars->fUseHelpers ? "on" : "off",
        pPars->fUseMffcDivs ? "on" : "off" );
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
             !Cec_TranRecipeStructurallyValid(pSim, &Cand) ||
             !Cec_TranRecipeMatchesRoot(pSim, &Cand, NULL) )
        {
            Prof.nHistoryTriedInvalidated++;
            continue;
        }
        Cand.nProofStage = pHistory->pArray[i].nProofStage;
        Cand.nStatus = Cand.nProofStage == 1 ?
            CEC_TRAN_STATE_PROVED_COMB : CEC_TRAN_STATE_PROVED_SEQ;
        Gain = Cec_TranCandDynamicGain( p, &Cand, pCovered, pUsed,
            pMffc, vMffc, vSupport );
        Cand.Gain = Gain;
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

    // Every wave visits every live root.  Each root owns its heavyweight
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
            if ( fMicroBatch && pPars->fUseConstr &&
                 Cec_TranRootBuildHorizonReached(pPars,
                    pCursors + pRoots[r].iObj) )
            {
                nHorizonRoots++;
                continue;
            }
            Cec_TranRootDiscoverOne( p, pSim, pPars, pRoots + r,
                pCursors + pRoots[r].iObj, iWave, &Known, pSolved,
                pCovered, pUsed, pMffc, vMffc, &Dep, &Disc, &Prof,
                &RootCands );
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
        }
        // In micro-batch mode only Page can contain fresh obligations.  Every
        // older Known entry is already PROVED or TRIED_SEQ, and scanning it
        // again cannot change the frontier on this immutable snapshot.  Keep
        // the legacy Known scan byte-for-byte when -j is disabled.
        {
            Cec_TranCandVec_t const * pFrontier =
                fMicroBatch ? &Page : &Known;
            int fRefreshRoots = !fMicroBatch || nFrontierRefreshes == 0;
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
            }

    // Keep every still-live old certificate and every newly proved relation
    // that was not consumed by this commit.  Selected relations map to their
    // replacement and are deliberately removed from the carry set.
    for ( i = 0; i < HistoryLive.nSize; i++ )
        if ( !Cec_TranCandVecContains(&Selected, HistoryLive.pArray + i) )
            Cec_TranCandVecPush( &Carry, HistoryLive.pArray[i] );

    // All proof and discovery data refer to the one immutable snapshot.  Tear
    // them down before the sole bundle duplication stops that snapshot.
    Cec_TranDepScratchStop( &Dep );
    Abc_ResubPrepareManager( 0 );
    Cec_TranSimStop( pSim );
    Cec_TranPatDbStop( pDb );
    pSim = NULL;
    pDb = NULL;
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
            nRegBefore, Gia_ManRegNum(p), Abc_MinInt(nWaves, 64), iPhase );
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
    if ( fMicroBatch )
        Abc_Print( 1, "stran-root immutable frontier reuse: refresh-calls=%d refresh-reuses=%d page-candidates=%lld known-candidate-scans-avoided=%lld.\n",
            nFrontierRefreshes, nFrontierRefreshReuses,
            nFrontierCandidates, nKnownCandidateScansAvoided );
    Abc_Print( 1, "stran-root cross-wave proof reuse: generation-skipped=%d remapped=%d invalidated=%d retained=%d.\n",
        Prof.nQueueTriedSkipped, Prof.nHistoryTriedRemapped,
        Prof.nHistoryTriedInvalidated, pHistory->nSize );
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

Gia_Man_t * Cec_ManSequentialTransduction( Gia_Man_t * pGia, Cec_ParTran_t * pPars )
{
    Cec_ParTran_t PassPars;
    Cec_TranCandVec_t ProofHistory = {0};
    Gia_Man_t * p = Gia_ManDup( pGia );
    Gia_Man_t * pNext;
    int iRound, nAndInitial = Gia_ManAndNum(p);
    int nCombPasses = 0, nCombCommits = 0;
    int nSeqPasses = 0, nSeqCommits = 0;
    if ( pPars->fRootExhaustive )
        pPars->nGainMin = 0;

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
        PassPars.nRootProofBatch = 0;
        pNext = Cec_ManSequentialRootPass( p, &PassPars,
            0, 1, &ProofHistory );
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
        pNext = Cec_ManSequentialRootPass( p, &PassPars,
            iRound, 0, &ProofHistory );
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
    return p;
}

ABC_NAMESPACE_IMPL_END
