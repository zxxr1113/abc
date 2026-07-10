/**CFile****************************************************************

  FileName    [cecCorrDyn.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Dynamic SRM manager for &scorr.]

  Author      [Xiran Zhao]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Jun 2026.]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

struct Cec_DynSrm_t_
{
    Gia_Man_t *      pAig;          // host AIG; owned by caller
    Cec_IncrMgr_t *  pIncr;         // active-list manager; owned by caller
    Gia_Man_t *      pCore;         // persistent SRM core without COs
    Cbs_Man_t *      pCbs;          // resident circuit-SAT manager on pCore (-D direct solving)
    Tas_Man_t *      pTas;          // resident TAS manager on pCore (-D direct solving)
    int              nCoreObjsAtReset; // real post-build pCore size after the last cold (re)build, for compaction (0 until that build finishes)
    int              fUseAdaptive;  // use timing-guided cold rebuilds in addition to the hard bloat guard
    int              nCompactMult;
    int              fForceRebuild;
    Vec_Int_t *      vSpecLits;     // cached core literals, indexed by frame/object
    Vec_Int_t *      vOutLits;      // core literals selected as current SAT outputs
    Vec_Int_t *      vCopyTouched;  // core ANDs copied into the current view
    Vec_Int_t *      vPiMap;        // host obj id -> PI index
    Vec_Int_t *      vRoMap;        // host obj id -> RO index
    // Phase-2 measurement (behavior-preserving): per-key stamp used to count the
    // union of true-value (no repr substitution) cones of the active pairs.
    int *            pTrueMark;     // size = nFramesTotal * nObjs; 0 = unvisited
    int              nTrueStamp;    // current visit stamp
    int              nObjs;
    int              nPis;
    int              nRegs;
    int              nFramesTotal;
    int              nCoreCiNum;
    int              nBuilds;
    int              nBuildsActive;
    int              nBuildsFull;
    int              nCoreResets;
    int              nCoreCompactions;
    int              nIncrFallbackResets;
    int              nDynActiveResets;
    int              nAdaptiveResets;
    int              nAdaptiveBurstResets;
    int              nAdaptiveBurstLeft;
    int              nBuildsSinceReset;
    int              nLastBuildReset;
    int              nLastResetReason;
    int              nForceResetReason;
    int              nLastResetSpan;
    int              nAdaptResetSamples;
    int              nAdaptReuseSamples;
    int              nCoreBuilds;
    int              nViewBuilds;
    int              nCacheFullClears;
    int              nCacheLocalClears;
    int              nCacheLocalEntries;
    int              nOutLitsLast;
    int              nOutLitsMax;
    int              nCoreObjsLast;
    int              nCoreObjsMax;
    int              nViewObjsLast;
    int              nViewObjsMax;
    int              nCoreDeltaLast;
    int              nCoreDeltaMax;
    int              nCoreBloatLastPermil;
    int              nCoreBloatMaxPermil;
    ABC_INT64_T      nOutLitsActiveSum;
    ABC_INT64_T      nOutLitsFullSum;
    ABC_INT64_T      nCoreObjsActiveSum;
    ABC_INT64_T      nCoreObjsFullSum;
    ABC_INT64_T      nSolveIters;
    ABC_INT64_T      nSolveCalls;
    ABC_INT64_T      nSolveReal;
    ABC_INT64_T      nSolveTriv;
    ABC_INT64_T      nSolveFail;
    ABC_INT64_T      nSolveFailIters;
    ABC_INT64_T      nFailCoreObjSum;
    ABC_INT64_T      nFailOutLitSum;
    int              nFailCoreObjMax;
    int              nFailOutLitMax;
    double           dAdaptResetCost;
    double           dAdaptReuseCost;
    double           dAdaptLastCost;
    abctime          tBuildLast;
    abctime          tBuildEnsureLast;
    abctime          tBuildInvalidateLast;
    abctime          tBuildEmitLast;
    abctime          tBuildTrueConeLast;
    abctime          tBuildTotal;
    abctime          tBuildResetTotal;
    abctime          tBuildReuseTotal;
    abctime          tBuildEnsureTotal;
    abctime          tBuildInvalidateTotal;
    abctime          tBuildEmitTotal;
    abctime          tBuildTrueConeTotal;
    abctime          tViewLast;
    abctime          tViewTotal;
    abctime          tSolveLast;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// Active-pair selection mirrors -i exactly: a pair is active iff an endpoint is
// in the alias-aware TFO (or, in ring mode, the ring edge itself changed).  The
// earlier "pending" set that force-re-emitted still-merged SAT pairs has been
// removed: per md/scorr_i_correctness_bug_report.md the alias-aware TFO is the
// real fix, and the retry/pending protection was shown to be both unnecessary
// (alias-only passes -d) and incomplete.  -d (incr-oracle) certifies soundness.
static int Cec_DynSrmActiveConst( Cec_DynSrm_t * p, int * pTfoMark, int ObjId )
{
    (void)p;
    return pTfoMark != NULL && pTfoMark[ObjId];
}

static int Cec_DynSrmActivePair( Cec_DynSrm_t * p, int * pTfoMark, int fRings, int iPrev, int iObj )
{
    if ( pTfoMark == NULL )
        return 0;
    if ( !fRings )
        return pTfoMark[iPrev] || pTfoMark[iObj];
    return pTfoMark[iPrev] || pTfoMark[iObj] ||
           Cec_IncrMgrRingEdgeChanged( p->pIncr, iPrev, iObj );
}

static int Cec_DynSrmEmitModeAccept( int fActive, Cec_IncrEmitMode_t Mode )
{
    return Mode == CEC_EMIT_ALL ||
           (Mode == CEC_EMIT_ACTIVE  &&  fActive) ||
           (Mode == CEC_EMIT_SKIPPED && !fActive);
}

static int Cec_DynSrmCacheIndex( Cec_DynSrm_t * p, int f, int ObjId )
{
    assert( f >= 0 && f < p->nFramesTotal );
    assert( ObjId >= 0 && ObjId < p->nObjs );
    return f * p->nObjs + ObjId;
}

static int Cec_DynSrmCacheRead( Cec_DynSrm_t * p, int f, Gia_Obj_t * pObj )
{
    return Vec_IntEntry( p->vSpecLits, Cec_DynSrmCacheIndex(p, f, Gia_ObjId(p->pAig, pObj)) );
}

static void Cec_DynSrmCacheWrite( Cec_DynSrm_t * p, int f, Gia_Obj_t * pObj, int Lit )
{
    Vec_IntWriteEntry( p->vSpecLits, Cec_DynSrmCacheIndex(p, f, Gia_ObjId(p->pAig, pObj)), Lit );
}

static int Cec_DynSrmHostPiLit( Cec_DynSrm_t * p, int f, Gia_Obj_t * pObj )
{
    int ObjId = Gia_ObjId( p->pAig, pObj );
    int iPi = Vec_IntEntry( p->vPiMap, ObjId );
    assert( iPi >= 0 && iPi < p->nPis );
    assert( f >= 0 && f < p->nFramesTotal );
    return Gia_ManCiLit( p->pCore, p->nRegs + f * p->nPis + iPi );
}

static int Cec_DynSrmHostRoLit( Cec_DynSrm_t * p, Gia_Obj_t * pObj )
{
    int ObjId = Gia_ObjId( p->pAig, pObj );
    int iRo = Vec_IntEntry( p->vRoMap, ObjId );
    assert( iRo >= 0 && iRo < p->nRegs );
    return Gia_ManCiLit( p->pCore, iRo );
}

static void Cec_DynSrmResetCore( Cec_DynSrm_t * p )
{
    if ( p->pCbs )       // stop resident solver before its pCore is freed
        Cbs_ManStop( p->pCbs );
    p->pCbs = NULL;
    if ( p->pTas )
        Tas_ManStop( p->pTas );
    p->pTas = NULL;
    if ( p->pCore )
        Gia_ManStop( p->pCore );
    p->pCore = NULL;
    p->nCoreObjsAtReset = 0;
    Vec_IntFreeP( &p->vSpecLits );
    Vec_IntFreeP( &p->vOutLits );
    Vec_IntFreeP( &p->vCopyTouched );
    Vec_IntFreeP( &p->vPiMap );
    Vec_IntFreeP( &p->vRoMap );
    ABC_FREE( p->pTrueMark );
    p->nTrueStamp = 0;
    p->nObjs = p->nPis = p->nRegs = p->nFramesTotal = p->nCoreCiNum = 0;
}

// pCore is append-only (strash never frees stale nodes from earlier rounds'
// reductions), so under long refinement it grows unboundedly and the resident
// solver's per-round sync/solve walks an ever-larger graph.  At a quiescent
// point (start of a build) cold-rebuild once it exceeds a multiple of its
// post-build size; the rebuilt core re-materializes only the live active cones.
#define CEC_DYN_COMPACT_MULT                 4
#define CEC_DYN_ADAPT_BLOAT_PERMIL        3000
#define CEC_DYN_ADAPT_WORSE_PERMIL        1500
#define CEC_DYN_ADAPT_RESET_BETTER_PERMIL  750
#define CEC_DYN_ADAPT_MIN_REUSE_SAMPLES     8
#define CEC_DYN_ADAPT_MIN_CALLS            16
#define CEC_DYN_ADAPT_MIN_BUILDS_SINCE_RESET 2
#define CEC_DYN_ADAPT_FAST_GROW_SPAN        4
#define CEC_DYN_ADAPT_BURST_ROUNDS          2
#define CEC_DYN_ADAPT_FAST_COMPACT_SPAN     2

enum {
    CEC_DYN_RESET_NONE    = 0,
    CEC_DYN_RESET_SHAPE   = 1,
    CEC_DYN_RESET_COMPACT = 2,
    CEC_DYN_RESET_ADAPT   = 3,
    CEC_DYN_RESET_BURST   = 4,
    CEC_DYN_RESET_IFALLBACK = 5,
    CEC_DYN_RESET_DACTIVE = 6
};

static const char * Cec_DynSrmResetReasonName( int Reason )
{
    if ( Reason == CEC_DYN_RESET_SHAPE )
        return "shape";
    if ( Reason == CEC_DYN_RESET_COMPACT )
        return "compact";
    if ( Reason == CEC_DYN_RESET_ADAPT )
        return "adapt";
    if ( Reason == CEC_DYN_RESET_BURST )
        return "burst";
    if ( Reason == CEC_DYN_RESET_IFALLBACK )
        return "ifallback";
    if ( Reason == CEC_DYN_RESET_DACTIVE )
        return "dactive";
    return "reuse";
}

static int Cec_DynSrmCurrentBloatPermil( Cec_DynSrm_t * p )
{
    if ( p->nCoreObjsAtReset <= 0 || p->pCore == NULL )
        return 1000;
    return (int)((ABC_INT64_T)1000 * Gia_ManObjNum(p->pCore) / p->nCoreObjsAtReset);
}

static int Cec_DynSrmShouldCompact( Cec_DynSrm_t * p )
{
    // 64-bit multiply: nCoreObjsAtReset can reach tens of millions (the growth
    // case this guards), so nCompactMult * it must not overflow int.
    return p->nCoreObjsAtReset > 0 &&
           Gia_ManObjNum(p->pCore) > (ABC_INT64_T)p->nCompactMult * p->nCoreObjsAtReset;
}

static int Cec_DynSrmShouldAdaptiveReset( Cec_DynSrm_t * p )
{
    int nBloat;
    if ( !p->fUseAdaptive )
        return CEC_DYN_RESET_NONE;
    if ( p->nAdaptiveBurstLeft > 0 )
    {
        p->nAdaptiveBurstLeft--;
        p->nAdaptiveBurstResets++;
        return CEC_DYN_RESET_BURST;
    }
    if ( p->nBuildsSinceReset < CEC_DYN_ADAPT_MIN_BUILDS_SINCE_RESET )
        return CEC_DYN_RESET_NONE;
    if ( p->nBuildsSinceReset > CEC_DYN_ADAPT_FAST_GROW_SPAN )
        return CEC_DYN_RESET_NONE;
    if ( p->nAdaptResetSamples == 0 || p->nAdaptReuseSamples < CEC_DYN_ADAPT_MIN_REUSE_SAMPLES )
        return CEC_DYN_RESET_NONE;
    nBloat = Cec_DynSrmCurrentBloatPermil( p );
    if ( nBloat < CEC_DYN_ADAPT_BLOAT_PERMIL )
        return CEC_DYN_RESET_NONE;
    if ( 1000.0 * p->dAdaptReuseCost > (double)CEC_DYN_ADAPT_WORSE_PERMIL * p->dAdaptResetCost )
        return CEC_DYN_RESET_ADAPT;
    return CEC_DYN_RESET_NONE;
}

static void Cec_DynSrmEnsureCore( Cec_DynSrm_t * p, int nFrames, int fScorr )
{
    Gia_Obj_t * pObj;
    int f, i, nFramesTotal = nFrames + fScorr;
    int ResetReason = CEC_DYN_RESET_NONE;
    int fSameShape = ( p->pCore != NULL &&
         p->nObjs == Gia_ManObjNum(p->pAig) &&
         p->nPis == Gia_ManPiNum(p->pAig) &&
         p->nRegs == Gia_ManRegNum(p->pAig) &&
         p->nFramesTotal == nFramesTotal );
    p->nLastBuildReset = 0;
    p->nLastResetReason = CEC_DYN_RESET_NONE;
    if ( !fSameShape )
        ResetReason = CEC_DYN_RESET_SHAPE;
    else if ( p->fForceRebuild )
        ResetReason = p->nForceResetReason;
    else if ( Cec_DynSrmShouldCompact(p) )
        ResetReason = CEC_DYN_RESET_COMPACT;
    else
        ResetReason = Cec_DynSrmShouldAdaptiveReset( p );
    if ( fSameShape && ResetReason == CEC_DYN_RESET_NONE )
        return;
    p->fForceRebuild = 0;
    p->nForceResetReason = CEC_DYN_RESET_NONE;
    if ( ResetReason == CEC_DYN_RESET_COMPACT )            // reusable shape but bloated: cold-rebuild
        p->nCoreCompactions++;
    if ( ResetReason == CEC_DYN_RESET_IFALLBACK )
        p->nIncrFallbackResets++;
    if ( ResetReason == CEC_DYN_RESET_DACTIVE )
        p->nDynActiveResets++;
    if ( ResetReason == CEC_DYN_RESET_ADAPT )
        p->nAdaptiveResets++;
    p->nLastResetSpan = p->nBuildsSinceReset;
    Cec_DynSrmResetCore( p );
    p->nLastBuildReset = 1;
    p->nLastResetReason = ResetReason;
    p->nBuildsSinceReset = 0;
    p->nObjs = Gia_ManObjNum( p->pAig );
    p->nPis = Gia_ManPiNum( p->pAig );
    p->nRegs = Gia_ManRegNum( p->pAig );
    p->nFramesTotal = nFramesTotal;
    p->vSpecLits = Vec_IntStartFull( p->nFramesTotal * p->nObjs );
    p->vOutLits = Vec_IntAlloc( 1000 );
    p->vCopyTouched = Vec_IntAlloc( 1000 );
    p->vPiMap = Vec_IntStartFull( p->nObjs );
    p->vRoMap = Vec_IntStartFull( p->nObjs );
    p->pTrueMark = ABC_CALLOC( int, p->nFramesTotal * p->nObjs );
    p->nTrueStamp = 0;
    p->pCore = Gia_ManStart( Abc_MaxInt( p->nFramesTotal * p->nObjs, 1000 ) );
    p->pCore->pName = Abc_UtilStrsav( p->pAig->pName );
    p->pCore->pSpec = Abc_UtilStrsav( p->pAig->pSpec );
    Gia_ManHashAlloc( p->pCore );
    Gia_ManForEachRo( p->pAig, pObj, i )
    {
        Vec_IntWriteEntry( p->vRoMap, Gia_ObjId(p->pAig, pObj), i );
        Gia_ManAppendCi( p->pCore );
    }
    Gia_ManForEachPi( p->pAig, pObj, i )
        Vec_IntWriteEntry( p->vPiMap, Gia_ObjId(p->pAig, pObj), i );
    for ( f = 0; f < p->nFramesTotal; f++ )
        Gia_ManForEachPi( p->pAig, pObj, i )
            Gia_ManAppendCi( p->pCore );
    p->nCoreCiNum = Gia_ManCiNum( p->pCore );
    assert( p->nCoreCiNum == p->nRegs + p->nFramesTotal * p->nPis );
    // leave nCoreObjsAtReset == 0 (set by ResetCore): only the CIs exist here, the
    // live cones are materialized later in BuildCore, so the real post-build size
    // is recorded there.
    p->nCoreResets++;
}

static void Cec_DynSrmInvalidateCache( Cec_DynSrm_t * p, int * pTfoMask )
{
    int f, i, Counter = 0;
    assert( p->vSpecLits != NULL );
    if ( pTfoMask == NULL )
    {
        Vec_IntFill( p->vSpecLits, p->nFramesTotal * p->nObjs, -1 );
        p->nCacheFullClears++;
        return;
    }
    for ( i = 0; i < p->nObjs; i++ )
    {
        if ( !pTfoMask[i] )
            continue;
        for ( f = 0; f < p->nFramesTotal; f++ )
        {
            Vec_IntWriteEntry( p->vSpecLits, Cec_DynSrmCacheIndex(p, f, i), -1 );
            Counter++;
        }
    }
    p->nCacheLocalClears++;
    p->nCacheLocalEntries += Counter;
}

static int Cec_DynSrmSpecLit( Cec_DynSrm_t * p, Gia_Obj_t * pObj, int f, int nPrefix );
static int Cec_DynSrmSpecLitInit( Cec_DynSrm_t * p, Gia_Obj_t * pObj, int f, int nPrefix );

static int Cec_DynSrmRealLit( Cec_DynSrm_t * p, Gia_Obj_t * pObj, int f, int nPrefix )
{
    if ( Gia_ObjIsAnd(pObj) )
    {
        int iLit0 = Cec_DynSrmSpecLit( p, Gia_ObjFanin0(pObj), f, nPrefix );
        int iLit1 = Cec_DynSrmSpecLit( p, Gia_ObjFanin1(pObj), f, nPrefix );
        iLit0 = Abc_LitNotCond( iLit0, Gia_ObjFaninC0(pObj) );
        iLit1 = Abc_LitNotCond( iLit1, Gia_ObjFaninC1(pObj) );
        return Gia_ManHashAnd( p->pCore, iLit0, iLit1 );
    }
    if ( Gia_ObjIsPi(p->pAig, pObj) )
        return Cec_DynSrmHostPiLit( p, f, pObj );
    if ( f == 0 )
    {
        assert( Gia_ObjIsRo(p->pAig, pObj) );
        return Cec_DynSrmSpecLit( p, pObj, f, nPrefix );
    }
    assert( Gia_ObjIsRo(p->pAig, pObj) );
    pObj = Gia_ObjRoToRi( p->pAig, pObj );
    {
        int iLit = Cec_DynSrmSpecLit( p, Gia_ObjFanin0(pObj), f-1, nPrefix );
        return Abc_LitNotCond( iLit, Gia_ObjFaninC0(pObj) );
    }
}

static int Cec_DynSrmSpecLit( Cec_DynSrm_t * p, Gia_Obj_t * pObj, int f, int nPrefix )
{
    Gia_Obj_t * pRepr;
    int iLit;
    if ( Gia_ObjIsConst0(pObj) )
        return 0;
    iLit = Cec_DynSrmCacheRead( p, f, pObj );
    if ( iLit >= 0 )
        return iLit;
    if ( Gia_ObjIsPi(p->pAig, pObj) )
    {
        iLit = Cec_DynSrmHostPiLit( p, f, pObj );
        Cec_DynSrmCacheWrite( p, f, pObj, iLit );
        return iLit;
    }
    if ( f >= nPrefix && (pRepr = Gia_ObjReprObj(p->pAig, Gia_ObjId(p->pAig, pObj))) )
    {
        iLit = Cec_DynSrmSpecLit( p, pRepr, f, nPrefix );
        iLit = Abc_LitNotCond( iLit, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
        Cec_DynSrmCacheWrite( p, f, pObj, iLit );
        return iLit;
    }
    if ( f == 0 && Gia_ObjIsRo(p->pAig, pObj) )
    {
        iLit = Cec_DynSrmHostRoLit( p, pObj );
        Cec_DynSrmCacheWrite( p, f, pObj, iLit );
        return iLit;
    }
    assert( Gia_ObjIsCand(pObj) );
    iLit = Cec_DynSrmRealLit( p, pObj, f, nPrefix );
    Cec_DynSrmCacheWrite( p, f, pObj, iLit );
    return iLit;
}

static int Cec_DynSrmRealLitInit( Cec_DynSrm_t * p, Gia_Obj_t * pObj, int f, int nPrefix )
{
    if ( Gia_ObjIsAnd(pObj) )
    {
        int iLit0 = Cec_DynSrmSpecLitInit( p, Gia_ObjFanin0(pObj), f, nPrefix );
        int iLit1 = Cec_DynSrmSpecLitInit( p, Gia_ObjFanin1(pObj), f, nPrefix );
        iLit0 = Abc_LitNotCond( iLit0, Gia_ObjFaninC0(pObj) );
        iLit1 = Abc_LitNotCond( iLit1, Gia_ObjFaninC1(pObj) );
        return Gia_ManHashAnd( p->pCore, iLit0, iLit1 );
    }
    if ( Gia_ObjIsPi(p->pAig, pObj) )
        return Cec_DynSrmHostPiLit( p, f, pObj );
    if ( f == 0 )
    {
        assert( Gia_ObjIsRo(p->pAig, pObj) );
        return Cec_DynSrmSpecLitInit( p, pObj, f, nPrefix );
    }
    assert( Gia_ObjIsRo(p->pAig, pObj) );
    pObj = Gia_ObjRoToRi( p->pAig, pObj );
    {
        int iLit = Cec_DynSrmSpecLitInit( p, Gia_ObjFanin0(pObj), f-1, nPrefix );
        return Abc_LitNotCond( iLit, Gia_ObjFaninC0(pObj) );
    }
}

// BMC/init SRM semantics differ from the inductive SRM in one important way:
// frame-0 ROs are fixed to the all-zero initial state.  The core still keeps
// RO CIs first to preserve the CEX-input layout expected by resimulation, but
// these CIs are intentionally unused in init-mode cones.
static int Cec_DynSrmSpecLitInit( Cec_DynSrm_t * p, Gia_Obj_t * pObj, int f, int nPrefix )
{
    Gia_Obj_t * pRepr;
    int iLit;
    if ( Gia_ObjIsConst0(pObj) )
        return 0;
    iLit = Cec_DynSrmCacheRead( p, f, pObj );
    if ( iLit >= 0 )
        return iLit;
    if ( Gia_ObjIsPi(p->pAig, pObj) )
    {
        iLit = Cec_DynSrmHostPiLit( p, f, pObj );
        Cec_DynSrmCacheWrite( p, f, pObj, iLit );
        return iLit;
    }
    if ( f >= nPrefix && (pRepr = Gia_ObjReprObj(p->pAig, Gia_ObjId(p->pAig, pObj))) )
    {
        iLit = Cec_DynSrmSpecLitInit( p, pRepr, f, nPrefix );
        iLit = Abc_LitNotCond( iLit, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
        Cec_DynSrmCacheWrite( p, f, pObj, iLit );
        return iLit;
    }
    if ( f == 0 && Gia_ObjIsRo(p->pAig, pObj) )
    {
        Cec_DynSrmCacheWrite( p, f, pObj, 0 );
        return 0;
    }
    assert( Gia_ObjIsCand(pObj) );
    iLit = Cec_DynSrmRealLitInit( p, pObj, f, nPrefix );
    Cec_DynSrmCacheWrite( p, f, pObj, iLit );
    return iLit;
}

static int Cec_DynSrmCopyLit_rec( Gia_Man_t * pCore, Gia_Man_t * pView, Vec_Int_t * vTouched, int iLit )
{
    Gia_Obj_t * pObj;
    int iObj, iLitCopy, iLit0, iLit1;
    if ( iLit < 2 )
        return iLit;
    iObj = Abc_Lit2Var( iLit );
    pObj = Gia_ManObj( pCore, iObj );
    if ( Gia_ObjIsCi(pObj) )
    {
        assert( Gia_ManCiIdToId(pView, Gia_ObjCioId(pObj)) == iObj );
        return iLit;
    }
    iLitCopy = Gia_ObjCopyArray( pCore, iObj );
    if ( iLitCopy >= 0 )
        return Abc_LitNotCond( iLitCopy, Abc_LitIsCompl(iLit) );
    assert( Gia_ObjIsAnd(pObj) );
    iLit0 = Cec_DynSrmCopyLit_rec( pCore, pView, vTouched, Gia_ObjFaninLit0p(pCore, pObj) );
    iLit1 = Cec_DynSrmCopyLit_rec( pCore, pView, vTouched, Gia_ObjFaninLit1p(pCore, pObj) );
    iLitCopy = Gia_ManHashAnd( pView, iLit0, iLit1 );
    Gia_ObjSetCopyArray( pCore, iObj, iLitCopy );
    Vec_IntPush( vTouched, iObj );
    return Abc_LitNotCond( iLitCopy, Abc_LitIsCompl(iLit) );
}

static Gia_Man_t * Cec_DynSrmBuildView( Cec_DynSrm_t * p )
{
    Gia_Man_t * pView;
    Gia_Obj_t * pObj;
    int i, iLit, iLitCopy;
    pView = Gia_ManStart( Abc_MaxInt( p->nCoreCiNum + 100 * Vec_IntSize(p->vOutLits) + 100, 1000 ) );
    pView->pName = Abc_UtilStrsav( p->pAig->pName );
    pView->pSpec = Abc_UtilStrsav( p->pAig->pSpec );
    Gia_ManHashAlloc( pView );
    Vec_IntFillExtra( &p->pCore->vCopies, Gia_ManObjNum(p->pCore), -1 );
    Vec_IntClear( p->vCopyTouched );
    Gia_ManForEachCi( p->pCore, pObj, i )
        Gia_ManAppendCi( pView );
    Vec_IntForEachEntry( p->vOutLits, iLit, i )
    {
        iLitCopy = Cec_DynSrmCopyLit_rec( p->pCore, pView, p->vCopyTouched, iLit );
        Gia_ManAppendCo( pView, iLitCopy );
    }
    Vec_IntForEachEntry( p->vCopyTouched, iLit, i )
        Gia_ObjSetCopyArray( p->pCore, iLit, -1 );
    Vec_IntClear( p->vCopyTouched );
    Gia_ManHashStop( pView );
    p->nViewBuilds++;
    p->nViewObjsLast = Gia_ManObjNum( pView );
    p->nViewObjsMax = Abc_MaxInt( p->nViewObjsMax, p->nViewObjsLast );
    return pView;
}

static const char * Cec_DynSrmModeName( Cec_IncrEmitMode_t Mode )
{
    if ( Mode == CEC_EMIT_ACTIVE )
        return "active";
    if ( Mode == CEC_EMIT_SKIPPED )
        return "skipped";
    return "full";
}

static void Cec_DynSrmRecordBuildStats( Cec_DynSrm_t * p,
    Cec_IncrEmitMode_t Mode, int nCoreObjsBefore, int nCoreResetsBefore,
    abctime tBuild, abctime tEnsure, abctime tInvalidate, abctime tEmit,
    abctime tTrueCone )
{
    int fReset = p->nCoreResets > nCoreResetsBefore;
    int ResetReason = fReset ? p->nLastResetReason : CEC_DYN_RESET_NONE;
    p->nBuildsSinceReset++;
    if ( Mode == CEC_EMIT_ACTIVE )
    {
        p->nOutLitsActiveSum += p->nOutLitsLast;
        p->nCoreObjsActiveSum += p->nCoreObjsLast;
    }
    else if ( Mode == CEC_EMIT_ALL )
    {
        p->nBuildsFull++;
        p->nOutLitsFullSum += p->nOutLitsLast;
        p->nCoreObjsFullSum += p->nCoreObjsLast;
    }
    p->nCoreDeltaLast = Abc_MaxInt( 0, p->nCoreObjsLast - nCoreObjsBefore );
    p->nCoreDeltaMax = Abc_MaxInt( p->nCoreDeltaMax, p->nCoreDeltaLast );
    if ( p->nCoreObjsAtReset > 0 )
    {
        p->nCoreBloatLastPermil =
            (int)((ABC_INT64_T)1000 * p->nCoreObjsLast / p->nCoreObjsAtReset);
        p->nCoreBloatMaxPermil =
            Abc_MaxInt( p->nCoreBloatMaxPermil, p->nCoreBloatLastPermil );
    }
    if ( tBuild )
    {
        p->tBuildLast = tBuild;
        p->tBuildEnsureLast = tEnsure;
        p->tBuildInvalidateLast = tInvalidate;
        p->tBuildEmitLast = tEmit;
        p->tBuildTrueConeLast = tTrueCone;
        p->tBuildTotal += tBuild;
        if ( fReset )
            p->tBuildResetTotal += tBuild;
        else
            p->tBuildReuseTotal += tBuild;
        p->tBuildEnsureTotal += tEnsure;
        p->tBuildInvalidateTotal += tInvalidate;
        p->tBuildEmitTotal += tEmit;
        p->tBuildTrueConeTotal += tTrueCone;
    }
    if ( Cec_ScorrProfOn )
        Abc_Print( 1, "  [dyn-build b=%d mode=%s reset=%d reason=%s out=%d core=%d delta=%d bloat=%.3f time=%.3f ensure=%.3f inv=%.3f emit=%.3f true=%.3f]\n",
            p->nBuilds, Cec_DynSrmModeName(Mode), fReset, Cec_DynSrmResetReasonName(ResetReason),
            p->nOutLitsLast, p->nCoreObjsLast, p->nCoreDeltaLast,
            0.001 * p->nCoreBloatLastPermil,
            1.0e-6 * tBuild, 1.0e-6 * tEnsure, 1.0e-6 * tInvalidate,
            1.0e-6 * tEmit, 1.0e-6 * tTrueCone );
}

Cec_DynSrm_t * Cec_DynSrmAlloc( Gia_Man_t * pAig, Cec_IncrMgr_t * pIncr, int fUseAdaptive )
{
    Cec_DynSrm_t * p = ABC_CALLOC( Cec_DynSrm_t, 1 );
    p->pAig = pAig;
    p->pIncr = pIncr;
    p->fUseAdaptive = fUseAdaptive;
    p->nCompactMult = CEC_DYN_COMPACT_MULT;
    return p;
}

void Cec_DynSrmSetParams( Cec_DynSrm_t * p, Cec_ParCor_t * pPars )
{
    if ( p == NULL || pPars == NULL )
        return;
    p->nCompactMult = Abc_MaxInt( 1, pPars->nDynSrmCompactMult );
}

void Cec_DynSrmForceRebuild( Cec_DynSrm_t * p, int fIncrFallback )
{
    if ( p == NULL )
        return;
    p->fForceRebuild = 1;
    if ( fIncrFallback )
        p->nForceResetReason = CEC_DYN_RESET_IFALLBACK;
    else if ( p->nForceResetReason != CEC_DYN_RESET_IFALLBACK )
        p->nForceResetReason = CEC_DYN_RESET_DACTIVE;
}

void Cec_DynSrmFree( Cec_DynSrm_t * p )
{
    if ( p == NULL )
        return;
    Cec_DynSrmResetCore( p );
    ABC_FREE( p );
}

void Cec_DynSrmPrintStats( Cec_DynSrm_t * p )
{
    ABC_INT64_T nActive = p ? p->nBuildsActive : 0;
    ABC_INT64_T nFull = p ? p->nBuildsFull : 0;
    if ( p == NULL )
        return;
    Abc_Print( 1, "DynSRM: builds = %d, active_builds = %d\n",
        p->nBuilds, p->nBuildsActive );
    Abc_Print( 1, "DynSRM: core_resets = %d, compactions = %d, core_builds = %d, view_builds = %d, out_lits_last/max = %d/%d, core_objs_last/max = %d/%d, view_objs_last/max = %d/%d\n",
        p->nCoreResets, p->nCoreCompactions, p->nCoreBuilds, p->nViewBuilds,
        p->nOutLitsLast, p->nOutLitsMax,
        p->nCoreObjsLast, p->nCoreObjsMax,
        p->nViewObjsLast, p->nViewObjsMax );
    Abc_Print( 1, "DynSRM: force_resets ifallback/dactive = %d/%d, compact_mult = %d\n",
        p->nIncrFallbackResets, p->nDynActiveResets, p->nCompactMult );
    Abc_Print( 1, "DynSRM: adapt enable/resets/burst/span = %d/%d/%d/%d, samples reset/reuse = %d/%d, cost reset/reuse/last = %.6f/%.6f/%.6f ns/call\n",
        p->fUseAdaptive, p->nAdaptiveResets, p->nAdaptiveBurstResets,
        p->nLastResetSpan,
        p->nAdaptResetSamples, p->nAdaptReuseSamples,
        p->dAdaptResetCost, p->dAdaptReuseCost, p->dAdaptLastCost );
    Abc_Print( 1, "DynSRM: cache_full_clears = %d, cache_local_clears = %d, cache_local_entries = %d\n",
        p->nCacheFullClears, p->nCacheLocalClears, p->nCacheLocalEntries );
    Abc_Print( 1, "DynSRM: build_modes full/active = %d/%d, avg_out full/active = %.1f/%.1f, avg_core full/active = %.1f/%.1f\n",
        p->nBuildsFull, p->nBuildsActive,
        nFull ? (double)p->nOutLitsFullSum / (double)nFull : 0.0,
        nActive ? (double)p->nOutLitsActiveSum / (double)nActive : 0.0,
        nFull ? (double)p->nCoreObjsFullSum / (double)nFull : 0.0,
        nActive ? (double)p->nCoreObjsActiveSum / (double)nActive : 0.0 );
    Abc_Print( 1, "DynSRM: core_delta_last/max = %d/%d, core_bloat_last/max = %.3f/%.3f\n",
        p->nCoreDeltaLast, p->nCoreDeltaMax,
        0.001 * p->nCoreBloatLastPermil,
        0.001 * p->nCoreBloatMaxPermil );
    Abc_Print( 1, "DynSRM: solve iters/calls = %lld/%lld, cex_real/triv/fail = %lld/%lld/%lld, fail_iters = %lld\n",
        (long long)p->nSolveIters, (long long)p->nSolveCalls,
        (long long)p->nSolveReal, (long long)p->nSolveTriv,
        (long long)p->nSolveFail, (long long)p->nSolveFailIters );
    Abc_Print( 1, "DynSRM: fail_core_avg/max = %.1f/%d, fail_out_avg/max = %.1f/%d\n",
        p->nSolveFail ? (double)p->nFailCoreObjSum / (double)p->nSolveFail : 0.0,
        p->nFailCoreObjMax,
        p->nSolveFail ? (double)p->nFailOutLitSum / (double)p->nSolveFail : 0.0,
        p->nFailOutLitMax );
    if ( p->tBuildTotal || p->tViewTotal )
        Abc_Print( 1, "DynSRM: build_time total/reset/reuse/view = %.3f/%.3f/%.3f/%.3f sec, parts ensure/inv/emit/true = %.3f/%.3f/%.3f/%.3f sec\n",
            1.0e-9 * p->tBuildTotal,
            1.0e-9 * p->tBuildResetTotal,
            1.0e-9 * p->tBuildReuseTotal,
            1.0e-9 * p->tViewTotal,
            1.0e-9 * p->tBuildEnsureTotal,
            1.0e-9 * p->tBuildInvalidateTotal,
            1.0e-9 * p->tBuildEmitTotal,
            1.0e-9 * p->tBuildTrueConeTotal );
}

static void Cec_DynSrmUpdateAdaptCost( double * pCost, int * pSamples, double Value )
{
    if ( *pSamples == 0 )
        *pCost = Value;
    else
        *pCost = 0.75 * *pCost + 0.25 * Value;
    (*pSamples)++;
}

void Cec_DynSrmRecordSolveStats( Cec_DynSrm_t * p,
    int nCalls, int nReal, int nTriv, int nFail, abctime tSat )
{
    int nDen;
    double dCost;
    if ( p == NULL )
        return;
    p->nSolveIters++;
    p->nSolveCalls += nCalls;
    p->nSolveReal += nReal;
    p->nSolveTriv += nTriv;
    p->nSolveFail += nFail;
    if ( nFail > 0 )
    {
        p->nSolveFailIters++;
        p->nFailCoreObjSum += (ABC_INT64_T)nFail * p->nCoreObjsLast;
        p->nFailOutLitSum += (ABC_INT64_T)nFail * p->nOutLitsLast;
        p->nFailCoreObjMax = Abc_MaxInt( p->nFailCoreObjMax, p->nCoreObjsLast );
        p->nFailOutLitMax = Abc_MaxInt( p->nFailOutLitMax, p->nOutLitsLast );
    }
    p->tSolveLast = tSat;
    if ( !p->fUseAdaptive || p->tBuildLast == 0 )
        return;
    nDen = nCalls > 0 ? nCalls : p->nOutLitsLast;
    if ( nDen < CEC_DYN_ADAPT_MIN_CALLS )
        return;
    dCost = (double)(p->tBuildLast + tSat) / (double)nDen;
    p->dAdaptLastCost = dCost;
    if ( p->nLastBuildReset )
    {
        if ( p->nLastResetReason != CEC_DYN_RESET_SHAPE )
        {
            Cec_DynSrmUpdateAdaptCost( &p->dAdaptResetCost, &p->nAdaptResetSamples, dCost );
            if ( p->nAdaptReuseSamples >= CEC_DYN_ADAPT_MIN_REUSE_SAMPLES &&
                 p->nLastResetReason == CEC_DYN_RESET_COMPACT &&
                 p->nLastResetSpan <= CEC_DYN_ADAPT_FAST_COMPACT_SPAN &&
                 1000.0 * dCost < (double)CEC_DYN_ADAPT_RESET_BETTER_PERMIL * p->dAdaptReuseCost )
                p->nAdaptiveBurstLeft = CEC_DYN_ADAPT_BURST_ROUNDS;
        }
    }
    else
        Cec_DynSrmUpdateAdaptCost( &p->dAdaptReuseCost, &p->nAdaptReuseSamples, dCost );
}

void Cec_DynSrmCountActivePairs( Cec_DynSrm_t * p, int fRings, int * pTfoMark,
    int * pnTotal, int * pnActive )
{
    Gia_Man_t * pAig = p->pAig;
    Gia_Obj_t * pObj, * pRepr;
    int i, iPrev, iObj;
    *pnTotal = *pnActive = 0;
    assert( pAig->pReprs != NULL );
    if ( fRings )
    {
        Gia_ManForEachObj1( pAig, pObj, i )
        {
            if ( Gia_ObjIsConst( pAig, i ) )
            {
                (*pnTotal)++;
                (*pnActive) += Cec_DynSrmActiveConst( p, pTfoMark, i );
            }
            else if ( Gia_ObjIsHead( pAig, i ) )
            {
                iPrev = i;
                Gia_ClassForEachObj1( pAig, i, iObj )
                {
                    (*pnTotal)++;
                    (*pnActive) += Cec_DynSrmActivePair( p, pTfoMark, 1, iPrev, iObj );
                    iPrev = iObj;
                }
                iObj = i;
                {
                    (*pnTotal)++;
                    (*pnActive) += Cec_DynSrmActivePair( p, pTfoMark, 1, iPrev, iObj );
                }
            }
        }
    }
    else
    {
        Gia_ManForEachObj1( pAig, pObj, i )
        {
            int idR;
            pRepr = Gia_ObjReprObj( pAig, Gia_ObjId(pAig,pObj) );
            if ( pRepr == NULL )
                continue;
            idR = Gia_ObjId( pAig, pRepr );
            (*pnTotal)++;
            (*pnActive) += Cec_DynSrmActivePair( p, pTfoMark, 0, idR, i );
        }
    }
}

// Phase-2 measurement only (gated on -w; never mutates pCore or classes).
// Marks the union of true-value cones (NO repr substitution) of one host
// endpoint at one frame, counting the distinct (frame,obj) keys a sim-on-SRM
// true-value resim would have to evaluate for this endpoint.
static void Cec_DynSrmTrueConeMark_rec( Cec_DynSrm_t * p, int ObjId, int f, int * pnKeys )
{
    Gia_Obj_t * pObj;
    int Key;
    if ( ObjId == 0 )
        return;
    Key = f * p->nObjs + ObjId;
    if ( p->pTrueMark[Key] == p->nTrueStamp )
        return;
    p->pTrueMark[Key] = p->nTrueStamp;
    (*pnKeys)++;
    pObj = Gia_ManObj( p->pAig, ObjId );
    if ( Gia_ObjIsPi(p->pAig, pObj) )
        return;
    if ( Gia_ObjIsRo(p->pAig, pObj) )
    {
        if ( f == 0 )
            return;
        Cec_DynSrmTrueConeMark_rec( p,
            Gia_ObjFaninId0p(p->pAig, Gia_ObjRoToRi(p->pAig, pObj)), f - 1, pnKeys );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Cec_DynSrmTrueConeMark_rec( p, Gia_ObjFaninId0p(p->pAig, pObj), f, pnKeys );
    Cec_DynSrmTrueConeMark_rec( p, Gia_ObjFaninId1p(p->pAig, pObj), f, pnKeys );
}

// Reports the size of the active pairs' true-value cone versus the full host
// unrolling (design doc 20.2 go/no-go: sim-on-SRM only pays when ratio << 1).
static void Cec_DynSrmReportTrueCone( Cec_DynSrm_t * p, int nFrames, int fRings, int * pTfoMask )
{
    Gia_Man_t * pAig = p->pAig;
    Gia_Obj_t * pObj, * pRepr;
    int i, iPrev, iObj, nKeys = 0;
    ABC_INT64_T nFull;
    if ( p->pTrueMark == NULL )
        return;
    if ( ++p->nTrueStamp == 0 )
    {
        memset( p->pTrueMark, 0, sizeof(int) * p->nFramesTotal * p->nObjs );
        p->nTrueStamp = 1;
    }
    if ( fRings )
    {
        Gia_ManForEachObj1( pAig, pObj, i )
        {
            if ( Gia_ObjIsConst( pAig, i ) )
            {
                if ( Cec_DynSrmActiveConst( p, pTfoMask, i ) )
                    Cec_DynSrmTrueConeMark_rec( p, i, nFrames, &nKeys );
            }
            else if ( Gia_ObjIsHead( pAig, i ) )
            {
                iPrev = i;
                Gia_ClassForEachObj1( pAig, i, iObj )
                {
                    if ( Cec_DynSrmActivePair( p, pTfoMask, 1, iPrev, iObj ) )
                    {
                        Cec_DynSrmTrueConeMark_rec( p, iPrev, nFrames, &nKeys );
                        Cec_DynSrmTrueConeMark_rec( p, iObj,  nFrames, &nKeys );
                    }
                    iPrev = iObj;
                }
                if ( Cec_DynSrmActivePair( p, pTfoMask, 1, iPrev, i ) )
                {
                    Cec_DynSrmTrueConeMark_rec( p, iPrev, nFrames, &nKeys );
                    Cec_DynSrmTrueConeMark_rec( p, i,     nFrames, &nKeys );
                }
            }
        }
    }
    else
    {
        Gia_ManForEachObj1( pAig, pObj, i )
        {
            int idR;
            pRepr = Gia_ObjReprObj( pAig, Gia_ObjId(pAig,pObj) );
            if ( pRepr == NULL )
                continue;
            idR = Gia_ObjId( pAig, pRepr );
            if ( !Cec_DynSrmActivePair( p, pTfoMask, 0, idR, i ) )
                continue;
            if ( !Gia_ObjIsConst(pAig, i) )
                Cec_DynSrmTrueConeMark_rec( p, idR, nFrames, &nKeys );
            Cec_DynSrmTrueConeMark_rec( p, i, nFrames, &nKeys );
        }
    }
    nFull = (ABC_INT64_T)p->nFramesTotal * p->nObjs;
    Abc_Print( 1, "  [dyn-truecone b=%d] active_true_keys=%d full_unroll_keys=%lld ratio=%.4f\n",
        p->nBuilds, nKeys, nFull, nFull ? (double)nKeys / (double)nFull : 0.0 );
}

// Builds (or extends) the persistent COless pCore and selects this round's
// active-pair root literals into p->vOutLits / *pvOutputs.  Shared by the view
// path (Cec_DynSrmBuild) and the -D persistence path (solve pCore directly).
void Cec_DynSrmBuildCore( Cec_DynSrm_t * p, int nFrames, int fScorr,
    Vec_Int_t ** pvOutputs, int fRings, int * pTfoMask, Cec_IncrEmitMode_t Mode )
{
    Gia_Obj_t * pObj, * pRepr;
    int i, iPrev, iObj, iPrevNew, iObjNew, iPrevRaw, iObjRaw;
    int nCoreResetsBefore, nCoreObjsBefore;
    int fMeasure = Cec_ScorrProfOn || p->fUseAdaptive;
    abctime tBuild = fMeasure ? Abc_ClockHr() : 0;
    abctime tStep, tEnsure = 0, tInvalidate = 0, tEmit = 0, tTrueCone = 0;
    assert( p != NULL );
    assert( nFrames > 0 );
    assert( Gia_ManRegNum(p->pAig) > 0 );
    assert( p->pAig->pReprs != NULL );
    assert( Mode == CEC_EMIT_ALL || pTfoMask != NULL );
    p->nBuilds++;
    if ( Mode == CEC_EMIT_ACTIVE )
        p->nBuildsActive++;
    nCoreResetsBefore = p->nCoreResets;
    tStep = fMeasure ? Abc_ClockHr() : 0;
    Cec_DynSrmEnsureCore( p, nFrames, fScorr );
    if ( fMeasure ) tEnsure = Abc_ClockHr() - tStep;
    nCoreObjsBefore = Gia_ManObjNum( p->pCore );
    tStep = fMeasure ? Abc_ClockHr() : 0;
    Cec_DynSrmInvalidateCache( p, Mode == CEC_EMIT_SKIPPED ? NULL : pTfoMask );
    if ( fMeasure ) tInvalidate = Abc_ClockHr() - tStep;
    tStep = fMeasure ? Abc_ClockHr() : 0;
    Gia_ManSetPhase( p->pAig );
    *pvOutputs = Vec_IntAlloc( 1000 );
    Vec_IntClear( p->vOutLits );
    if ( fRings )
    {
        Gia_ManForEachObj1( p->pAig, pObj, i )
        {
            if ( Gia_ObjIsConst( p->pAig, i ) )
            {
                int fActive = Cec_DynSrmActiveConst( p, pTfoMask, i );
                if ( !Cec_DynSrmEmitModeAccept(fActive, Mode) )
                    continue;
                iObjRaw = Cec_DynSrmRealLit( p, pObj, nFrames, 0 );
                iObjNew = Abc_LitNotCond( iObjRaw, Gia_ObjPhase(pObj) );
                if ( iObjNew != 0 )
                {
                    Vec_IntPush( *pvOutputs, 0 );
                    Vec_IntPush( *pvOutputs, i );
                    Vec_IntPush( p->vOutLits, iObjNew );
                }
            }
            else if ( Gia_ObjIsHead( p->pAig, i ) )
            {
                iPrev = i;
                Gia_ClassForEachObj1( p->pAig, i, iObj )
                {
                    int fActive = Cec_DynSrmActivePair( p, pTfoMask, 1, iPrev, iObj );
                    if ( Cec_DynSrmEmitModeAccept(fActive, Mode) )
                    {
                        iPrevRaw = Cec_DynSrmRealLit( p, Gia_ManObj(p->pAig, iPrev), nFrames, 0 );
                        iObjRaw  = Cec_DynSrmRealLit( p, Gia_ManObj(p->pAig, iObj), nFrames, 0 );
                        iPrevNew = Abc_LitNotCond( iPrevRaw, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p->pAig, iPrev)) );
                        iObjNew  = Abc_LitNotCond( iObjRaw,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p->pAig, iObj)) );
                        if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                        {
                            Vec_IntPush( *pvOutputs, iPrev );
                            Vec_IntPush( *pvOutputs, iObj );
                            Vec_IntPush( p->vOutLits, Gia_ManHashAnd(p->pCore, iPrevNew, Abc_LitNot(iObjNew)) );
                        }
                    }
                    iPrev = iObj;
                }
                iObj = i;
                {
                    int fActive = Cec_DynSrmActivePair( p, pTfoMask, 1, iPrev, iObj );
                    if ( Cec_DynSrmEmitModeAccept(fActive, Mode) )
                    {
                        iPrevRaw = Cec_DynSrmRealLit( p, Gia_ManObj(p->pAig, iPrev), nFrames, 0 );
                        iObjRaw  = Cec_DynSrmRealLit( p, Gia_ManObj(p->pAig, iObj), nFrames, 0 );
                        iPrevNew = Abc_LitNotCond( iPrevRaw, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p->pAig, iPrev)) );
                        iObjNew  = Abc_LitNotCond( iObjRaw,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p->pAig, iObj)) );
                        if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                        {
                            Vec_IntPush( *pvOutputs, iPrev );
                            Vec_IntPush( *pvOutputs, iObj );
                            Vec_IntPush( p->vOutLits, Gia_ManHashAnd(p->pCore, iPrevNew, Abc_LitNot(iObjNew)) );
                        }
                    }
                }
            }
        }
    }
    else
    {
        Gia_ManForEachObj1( p->pAig, pObj, i )
        {
            pRepr = Gia_ObjReprObj( p->pAig, Gia_ObjId(p->pAig,pObj) );
            if ( pRepr == NULL )
                continue;
            {
                int idR = Gia_ObjId(p->pAig, pRepr);
                int fActive = Cec_DynSrmActivePair( p, pTfoMask, 0, idR, i );
                if ( !Cec_DynSrmEmitModeAccept(fActive, Mode) )
                    continue;
            }
            iPrevRaw = Gia_ObjIsConst(p->pAig, i)? 0 : Cec_DynSrmRealLit( p, pRepr, nFrames, 0 );
            iObjRaw  = Cec_DynSrmRealLit( p, pObj, nFrames, 0 );
            iPrevNew = iPrevRaw;
            iObjNew  = Abc_LitNotCond( iObjRaw, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                Vec_IntPush( *pvOutputs, Gia_ObjId(p->pAig, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p->pAig, pObj) );
                Vec_IntPush( p->vOutLits, Gia_ManHashXor(p->pCore, iPrevNew, iObjNew) );
            }
        }
    }
    p->nCoreBuilds++;
    p->nOutLitsLast = Vec_IntSize( p->vOutLits );
    p->nOutLitsMax = Abc_MaxInt( p->nOutLitsMax, p->nOutLitsLast );
    p->nCoreObjsLast = Gia_ManObjNum( p->pCore );
    if ( p->nCoreObjsAtReset == 0 )      // first build after a cold (re)set: record the
        p->nCoreObjsAtReset = p->nCoreObjsLast;   // real post-build size as the compaction baseline
    p->nCoreObjsMax = Abc_MaxInt( p->nCoreObjsMax, p->nCoreObjsLast );
    if ( fMeasure ) tEmit = Abc_ClockHr() - tStep;
    if ( Cec_ScorrProfOn && Mode == CEC_EMIT_ACTIVE )
    {
        tStep = Abc_ClockHr();
        Cec_DynSrmReportTrueCone( p, nFrames, fRings, pTfoMask );
        tTrueCone = Abc_ClockHr() - tStep;
    }
    if ( fMeasure ) tBuild = Abc_ClockHr() - tBuild;
    Cec_DynSrmRecordBuildStats( p, Mode, nCoreObjsBefore, nCoreResetsBefore,
        tBuild, tEnsure, tInvalidate, tEmit, tTrueCone );
}

Gia_Man_t * Cec_DynSrmBuild( Cec_DynSrm_t * p, int nFrames, int fScorr,
    Vec_Int_t ** pvOutputs, int fRings, int * pTfoMask, Cec_IncrEmitMode_t Mode )
{
    Gia_Man_t * pView;
    abctime tView;
    Cec_DynSrmBuildCore( p, nFrames, fScorr, pvOutputs, fRings, pTfoMask, Mode );
    tView = Cec_ScorrProfOn ? Abc_ClockHr() : 0;
    pView = Cec_DynSrmBuildView( p );
    if ( Cec_ScorrProfOn )
    {
        p->tViewLast = Abc_ClockHr() - tView;
        p->tViewTotal += p->tViewLast;
        Abc_Print( 1, "  [dyn-view b=%d out=%d view=%d time=%.3f]\n",
            p->nBuilds, Vec_IntSize(p->vOutLits), p->nViewObjsLast,
            1.0e-6 * p->tViewLast );
    }
    return pView;
}

// BMC/init variant of Cec_DynSrmBuildCore.  It mirrors
// Gia_ManCorrSpecReduceInit(): ROs at frame 0 are constants, representatives
// are applied only at frames >= nPrefix, and every BMC endpoint frame in
// [nPrefix, nPrefix+nFrames) emits the current (repr,obj) candidates.
void Cec_DynSrmBuildCoreInit( Cec_DynSrm_t * p, int nFrames, int nPrefix, int fScorr,
    Vec_Int_t ** pvOutputs, int * pTfoMask, Cec_IncrEmitMode_t Mode )
{
    Gia_Obj_t * pObj, * pRepr;
    int f, i, iPrevNew, iObjNew;
    int nCoreResetsBefore, nCoreObjsBefore;
    int fMeasure = Cec_ScorrProfOn || p->fUseAdaptive;
    abctime tBuild = fMeasure ? Abc_ClockHr() : 0;
    abctime tStep, tEnsure = 0, tInvalidate = 0, tEmit = 0;
    assert( p != NULL );
    assert( (!fScorr && nFrames > 1) || (fScorr && nFrames > 0) || nPrefix );
    assert( Gia_ManRegNum(p->pAig) > 0 );
    assert( p->pAig->pReprs != NULL );
    assert( Mode == CEC_EMIT_ALL || pTfoMask != NULL );
    p->nBuilds++;
    if ( Mode == CEC_EMIT_ACTIVE )
        p->nBuildsActive++;
    nCoreResetsBefore = p->nCoreResets;
    tStep = fMeasure ? Abc_ClockHr() : 0;
    Cec_DynSrmEnsureCore( p, nFrames + nPrefix, fScorr );
    if ( fMeasure ) tEnsure = Abc_ClockHr() - tStep;
    nCoreObjsBefore = Gia_ManObjNum( p->pCore );
    tStep = fMeasure ? Abc_ClockHr() : 0;
    Cec_DynSrmInvalidateCache( p, Mode == CEC_EMIT_SKIPPED ? NULL : pTfoMask );
    if ( fMeasure ) tInvalidate = Abc_ClockHr() - tStep;
    tStep = fMeasure ? Abc_ClockHr() : 0;
    Gia_ManSetPhase( p->pAig );
    *pvOutputs = Vec_IntAlloc( 1000 );
    Vec_IntClear( p->vOutLits );
    for ( f = nPrefix; f < nFrames + nPrefix; f++ )
    {
        Gia_ManForEachObj1( p->pAig, pObj, i )
        {
            pRepr = Gia_ObjReprObj( p->pAig, Gia_ObjId(p->pAig,pObj) );
            if ( pRepr == NULL )
                continue;
            {
                int idR = Gia_ObjId(p->pAig, pRepr);
                int fActive = pTfoMask != NULL && (pTfoMask[i] || pTfoMask[idR]);
                if ( !Cec_DynSrmEmitModeAccept(fActive, Mode) )
                    continue;
            }
            iPrevNew = Gia_ObjIsConst(p->pAig, i)? 0 : Cec_DynSrmRealLitInit( p, pRepr, f, nPrefix );
            iObjNew  = Cec_DynSrmRealLitInit( p, pObj, f, nPrefix );
            iObjNew  = Abc_LitNotCond( iObjNew, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                Vec_IntPush( *pvOutputs, Gia_ObjId(p->pAig, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p->pAig, pObj) );
                Vec_IntPush( p->vOutLits, Gia_ManHashXor(p->pCore, iPrevNew, iObjNew) );
            }
        }
    }
    p->nCoreBuilds++;
    p->nOutLitsLast = Vec_IntSize( p->vOutLits );
    p->nOutLitsMax = Abc_MaxInt( p->nOutLitsMax, p->nOutLitsLast );
    p->nCoreObjsLast = Gia_ManObjNum( p->pCore );
    if ( p->nCoreObjsAtReset == 0 )
        p->nCoreObjsAtReset = p->nCoreObjsLast;
    p->nCoreObjsMax = Abc_MaxInt( p->nCoreObjsMax, p->nCoreObjsLast );
    if ( fMeasure )
    {
        tEmit = Abc_ClockHr() - tStep;
        tBuild = Abc_ClockHr() - tBuild;
    }
    Cec_DynSrmRecordBuildStats( p, Mode, nCoreObjsBefore, nCoreResetsBefore,
        tBuild, tEnsure, tInvalidate, tEmit, 0 );
}

Gia_Man_t * Cec_DynSrmBuildInit( Cec_DynSrm_t * p, int nFrames, int nPrefix, int fScorr,
    Vec_Int_t ** pvOutputs, int * pTfoMask, Cec_IncrEmitMode_t Mode )
{
    Cec_DynSrmBuildCoreInit( p, nFrames, nPrefix, fScorr, pvOutputs, pTfoMask, Mode );
    return Cec_DynSrmBuildView( p );
}

// This round's active-pair root literals (used by the main loop for counts).
Vec_Int_t * Cec_DynSrmOutLits( Cec_DynSrm_t * p ) { return p->vOutLits; }

// Solves this round's root literals on the persistent pCore with the resident
// circuit-SAT manager (allocated lazily; re-created after a core reset/compaction
// since its pAig is freed there).  The CI-layout assert guards the CEX CioId ->
// resim-input contract that the discarded view used to enforce in the main loop.
Vec_Int_t * Cec_DynSrmSolve( Cec_DynSrm_t * p, int nConfs, Vec_Str_t ** pvStatus, int fUseTas )
{
    assert( Gia_ManRegNum(p->pCore) == 0 );
    assert( Gia_ManCiNum(p->pCore) == p->nRegs + p->nFramesTotal * p->nPis );
    if ( fUseTas )
    {
        if ( p->pTas == NULL )
            p->pTas = Tas_ManAlloc( p->pCore, nConfs );
        Tas_ManSetConflictNum( p->pTas, nConfs );
        return Tas_ManSolveRoots( p->pTas, p->vOutLits, pvStatus, 0 );
    }
    if ( p->pCbs == NULL )
        p->pCbs = Cbs_ManAlloc( p->pCore );
    Cbs_ManSetConflictNum( p->pCbs, nConfs );
    return Cbs_ManSolveRoots( p->pCbs, p->vOutLits, pvStatus, 0 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
