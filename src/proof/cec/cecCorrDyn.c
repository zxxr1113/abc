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
    Vec_Int_t *      vSpecLits;     // cached core literals, indexed by frame/object
    Vec_Int_t *      vOutLits;      // core literals selected as current SAT outputs
    Vec_Int_t *      vCopyTouched;  // core ANDs copied into the current view
    Vec_Int_t *      vPiMap;        // host obj id -> PI index
    Vec_Int_t *      vRoMap;        // host obj id -> RO index
    Gia_Man_t *      pTrue;         // persistent true-value unrolling (no repr substitution)
    Vec_Int_t *      vTrueLits;     // (frame,host object) -> literal in pTrue
    Vec_Ptr_t *      vTrueInputs;   // packed CEX/random values for pTrue CIs
    unsigned *       pTrueSims;     // object-major bit-parallel values for pTrue
    size_t           nTrueSimsAlloc;
    int              nTrueFrames;
    int              nTrueWords;
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
    int              nCoreResets;
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
    int              nTrueBuilds;
    int              nTrueBatches;
    int              nTrueChanges;
    int              nTrueFallbacks;
    int              nTrueObjsLast;
    abctime          tTrueBuild;
    abctime          tTrueSim;
    abctime          tTrueRefine;
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

static void Cec_DynSrmResetTrue( Cec_DynSrm_t * p )
{
    if ( p->pTrue )
        Gia_ManStop( p->pTrue );
    p->pTrue = NULL;
    Vec_IntFreeP( &p->vTrueLits );
    Vec_PtrFreeP( &p->vTrueInputs );
    ABC_FREE( p->pTrueSims );
    p->nTrueSimsAlloc = 0;
    p->nTrueFrames = p->nTrueWords = 0;
}

static void Cec_DynSrmResetCore( Cec_DynSrm_t * p )
{
    Cec_DynSrmResetTrue( p );
    if ( p->pCore )
        Gia_ManStop( p->pCore );
    p->pCore = NULL;
    Vec_IntFreeP( &p->vSpecLits );
    Vec_IntFreeP( &p->vOutLits );
    Vec_IntFreeP( &p->vCopyTouched );
    Vec_IntFreeP( &p->vPiMap );
    Vec_IntFreeP( &p->vRoMap );
    ABC_FREE( p->pTrueMark );
    p->nTrueStamp = 0;
    p->nObjs = p->nPis = p->nRegs = p->nFramesTotal = p->nCoreCiNum = 0;
}

static int Cec_DynSrmTrueIndex( Cec_DynSrm_t * p, int f, int ObjId )
{
    assert( f >= 0 && f < p->nTrueFrames );
    assert( ObjId >= 0 && ObjId < p->nObjs );
    return f * p->nObjs + ObjId;
}

static void Cec_DynSrmEnsureTrue( Cec_DynSrm_t * p, int nFrames, int nWords )
{
    Gia_Obj_t * pObj;
    int f, i;
    if ( p->pTrue != NULL && p->nTrueFrames == nFrames &&
         p->nTrueWords == nWords )
        return;
    Cec_DynSrmResetTrue( p );
    p->nTrueFrames = nFrames;
    p->nTrueWords = nWords;
    p->vTrueLits = Vec_IntStartFull( p->nTrueFrames * p->nObjs );
    p->vTrueInputs = Vec_PtrAllocSimInfo(
        p->nRegs + p->nTrueFrames * p->nPis, p->nTrueWords );
    p->pTrue = Gia_ManStart( Abc_MaxInt(p->nTrueFrames * p->nObjs, 1000) );
    p->pTrue->pName = Abc_UtilStrsav( p->pAig->pName );
    p->pTrue->pSpec = Abc_UtilStrsav( p->pAig->pSpec );
    Gia_ManHashAlloc( p->pTrue );
    Gia_ManForEachRo( p->pAig, pObj, i )
        Gia_ManAppendCi( p->pTrue );
    for ( f = 0; f < p->nTrueFrames; f++ )
        Gia_ManForEachPi( p->pAig, pObj, i )
            Gia_ManAppendCi( p->pTrue );
    assert( Gia_ManCiNum(p->pTrue) ==
        p->nRegs + p->nTrueFrames * p->nPis );
    p->nTrueBuilds++;
}

static int Cec_DynSrmTrueLit_rec( Cec_DynSrm_t * p, int ObjId, int f )
{
    Gia_Obj_t * pObj;
    int Index, Lit, Lit0, Lit1;
    if ( ObjId == 0 )
        return 0;
    Index = Cec_DynSrmTrueIndex( p, f, ObjId );
    Lit = Vec_IntEntry( p->vTrueLits, Index );
    if ( Lit >= 0 )
        return Lit;
    pObj = Gia_ManObj( p->pAig, ObjId );
    if ( Gia_ObjIsPi(p->pAig, pObj) )
    {
        int iPi = Vec_IntEntry( p->vPiMap, ObjId );
        assert( iPi >= 0 && iPi < p->nPis );
        Lit = Gia_ManCiLit( p->pTrue, p->nRegs + f * p->nPis + iPi );
    }
    else if ( Gia_ObjIsRo(p->pAig, pObj) )
    {
        if ( f == 0 )
        {
            int iRo = Vec_IntEntry( p->vRoMap, ObjId );
            assert( iRo >= 0 && iRo < p->nRegs );
            Lit = Gia_ManCiLit( p->pTrue, iRo );
        }
        else
        {
            Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
            Lit = Cec_DynSrmTrueLit_rec( p,
                Gia_ObjFaninId0p(p->pAig, pRi), f - 1 );
            Lit = Abc_LitNotCond( Lit, Gia_ObjFaninC0(pRi) );
        }
    }
    else
    {
        assert( Gia_ObjIsAnd(pObj) );
        Lit0 = Cec_DynSrmTrueLit_rec( p,
            Gia_ObjFaninId0p(p->pAig, pObj), f );
        Lit1 = Cec_DynSrmTrueLit_rec( p,
            Gia_ObjFaninId1p(p->pAig, pObj), f );
        Lit0 = Abc_LitNotCond( Lit0, Gia_ObjFaninC0(pObj) );
        Lit1 = Abc_LitNotCond( Lit1, Gia_ObjFaninC1(pObj) );
        Lit = Gia_ManHashAnd( p->pTrue, Lit0, Lit1 );
    }
    Vec_IntWriteEntry( p->vTrueLits, Index, Lit );
    return Lit;
}

static void Cec_DynSrmTrueBuildClassCones( Cec_DynSrm_t * p )
{
    Gia_Obj_t * pObj;
    int f, i;
    abctime t = Abc_ClockHr();
    for ( f = 0; f < p->nTrueFrames; f++ )
        Gia_ManForEachObj1( p->pAig, pObj, i )
            if ( Gia_ObjIsConst(p->pAig, i) || Gia_ObjIsClass(p->pAig, i) )
                Cec_DynSrmTrueLit_rec( p, i, f );
    p->nTrueObjsLast = Gia_ManObjNum( p->pTrue );
    p->tTrueBuild += Abc_ClockHr() - t;
}

static void Cec_DynSrmTrueSimulate( Cec_DynSrm_t * p )
{
    Gia_Obj_t * pObj;
    size_t nNeed = (size_t)Gia_ManObjNum(p->pTrue) * p->nTrueWords;
    unsigned * pSim0, * pSim1, * pSim;
    int i, w;
    abctime t = Abc_ClockHr();
    if ( p->nTrueSimsAlloc < nNeed )
    {
        p->pTrueSims = ABC_REALLOC( unsigned, p->pTrueSims, nNeed );
        p->nTrueSimsAlloc = nNeed;
    }
    memset( p->pTrueSims, 0, sizeof(unsigned) * p->nTrueWords );
    Gia_ManForEachCi( p->pTrue, pObj, i )
    {
        pSim = p->pTrueSims + (size_t)Gia_ObjId(p->pTrue, pObj) * p->nTrueWords;
        pSim0 = (unsigned *)Vec_PtrEntry( p->vTrueInputs, i );
        for ( w = 0; w < p->nTrueWords; w++ )
            pSim[w] = pSim0[w];
        pSim[0] &= ~(unsigned)1;
    }
    Gia_ManForEachAnd( p->pTrue, pObj, i )
    {
        pSim0 = p->pTrueSims +
            (size_t)Gia_ObjFaninId0p(p->pTrue, pObj) * p->nTrueWords;
        pSim1 = p->pTrueSims +
            (size_t)Gia_ObjFaninId1p(p->pTrue, pObj) * p->nTrueWords;
        pSim = p->pTrueSims + (size_t)i * p->nTrueWords;
        if ( Gia_ObjFaninC0(pObj) )
        {
            if ( Gia_ObjFaninC1(pObj) )
                for ( w = 0; w < p->nTrueWords; w++ )
                    pSim[w] = ~pSim0[w] & ~pSim1[w];
            else
                for ( w = 0; w < p->nTrueWords; w++ )
                    pSim[w] = ~pSim0[w] & pSim1[w];
        }
        else if ( Gia_ObjFaninC1(pObj) )
            for ( w = 0; w < p->nTrueWords; w++ )
                pSim[w] = pSim0[w] & ~pSim1[w];
        else
            for ( w = 0; w < p->nTrueWords; w++ )
                pSim[w] = pSim0[w] & pSim1[w];
    }
    p->tTrueSim += Abc_ClockHr() - t;
}

static void Cec_DynSrmEnsureCore( Cec_DynSrm_t * p, int nFrames, int fScorr )
{
    Gia_Obj_t * pObj;
    int f, i, nFramesTotal = nFrames + fScorr;
    if ( p->pCore != NULL &&
         p->nObjs == Gia_ManObjNum(p->pAig) &&
         p->nPis == Gia_ManPiNum(p->pAig) &&
         p->nRegs == Gia_ManRegNum(p->pAig) &&
         p->nFramesTotal == nFramesTotal )
        return;
    Cec_DynSrmResetCore( p );
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

Cec_DynSrm_t * Cec_DynSrmAlloc( Gia_Man_t * pAig, Cec_IncrMgr_t * pIncr )
{
    Cec_DynSrm_t * p = ABC_CALLOC( Cec_DynSrm_t, 1 );
    p->pAig = pAig;
    p->pIncr = pIncr;
    return p;
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
    if ( p == NULL )
        return;
    Abc_Print( 1, "DynSRM: builds = %d, active_builds = %d\n",
        p->nBuilds, p->nBuildsActive );
    Abc_Print( 1, "DynSRM: core_resets = %d, core_builds = %d, view_builds = %d, out_lits_last/max = %d/%d, core_objs_last/max = %d/%d, view_objs_last/max = %d/%d\n",
        p->nCoreResets, p->nCoreBuilds, p->nViewBuilds,
        p->nOutLitsLast, p->nOutLitsMax,
        p->nCoreObjsLast, p->nCoreObjsMax,
        p->nViewObjsLast, p->nViewObjsMax );
    Abc_Print( 1, "DynSRM: cache_full_clears = %d, cache_local_clears = %d, cache_local_entries = %d\n",
        p->nCacheFullClears, p->nCacheLocalClears, p->nCacheLocalEntries );
    Abc_Print( 1, "DynSRM-sim: true_builds = %d, batches = %d, changes = %d, fallbacks = %d, true_objs = %d, build/sim/refine = %.3f/%.3f/%.3f sec\n",
        p->nTrueBuilds, p->nTrueBatches, p->nTrueChanges, p->nTrueFallbacks,
        p->nTrueObjsLast, 1.0e-9 * p->tTrueBuild, 1.0e-9 * p->tTrueSim,
        1.0e-9 * p->tTrueRefine );
}

int Cec_DynSrmResimulate( Cec_DynSrm_t * p, Cec_ManSim_t * pSim,
    Vec_Int_t * vCexStore, int nFrames )
{
    Vec_Int_t * vPairs;
    int iStart = 0, f, nChanges = 0;
    assert( p != NULL );
    assert( p->pAig == pSim->pAig );
    assert( nFrames > 0 );
    Cec_DynSrmEnsureTrue( p, nFrames, pSim->pPars->nWords );
    Cec_DynSrmTrueBuildClassCones( p );
    vPairs = Gia_ManCorrCreateRemapping( p->pAig );
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        abctime t;
        Cec_ManStartSimInfo( p->vTrueInputs, p->nRegs );
        iStart = Cec_ManLoadCounterExamples(
            p->vTrueInputs, vCexStore, iStart );
        Gia_ManCorrPerformRemapping( vPairs, p->vTrueInputs );
        Cec_DynSrmTrueSimulate( p );
        t = Abc_ClockHr();
        for ( f = 0; f < p->nTrueFrames; f++ )
            nChanges += Cec_ManSimRefineMappedFrame( pSim, p->pTrueSims,
                p->vTrueLits, f * p->nObjs, p->nTrueWords );
        p->tTrueRefine += Abc_ClockHr() - t;
        p->nTrueBatches++;
    }
    assert( iStart == Vec_IntSize(vCexStore) );
    p->nTrueChanges += nChanges;
    Vec_IntFree( vPairs );
    return nChanges;
}

void Cec_DynSrmRecordSimFallback( Cec_DynSrm_t * p )
{
    if ( p )
        p->nTrueFallbacks++;
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

Gia_Man_t * Cec_DynSrmBuild( Cec_DynSrm_t * p, int nFrames, int fScorr,
    Vec_Int_t ** pvOutputs, int fRings, int * pTfoMask, Cec_IncrEmitMode_t Mode )
{
    Gia_Obj_t * pObj, * pRepr;
    int i, iPrev, iObj, iPrevNew, iObjNew, iPrevRaw, iObjRaw;
    assert( p != NULL );
    assert( nFrames > 0 );
    assert( Gia_ManRegNum(p->pAig) > 0 );
    assert( p->pAig->pReprs != NULL );
    assert( Mode == CEC_EMIT_ALL || pTfoMask != NULL );
    p->nBuilds++;
    if ( Mode == CEC_EMIT_ACTIVE )
        p->nBuildsActive++;
    Cec_DynSrmEnsureCore( p, nFrames, fScorr );
    Cec_DynSrmInvalidateCache( p, Mode == CEC_EMIT_SKIPPED ? NULL : pTfoMask );
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
    p->nCoreObjsMax = Abc_MaxInt( p->nCoreObjsMax, p->nCoreObjsLast );
    if ( Cec_ScorrProfOn && Mode == CEC_EMIT_ACTIVE )
        Cec_DynSrmReportTrueCone( p, nFrames, fRings, pTfoMask );
    return Cec_DynSrmBuildView( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
