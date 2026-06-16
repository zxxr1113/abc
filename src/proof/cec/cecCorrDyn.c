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
    Vec_Int_t *      vPendingPairs; // SAT obligations still merged after resim
    Vec_Int_t *      vPendingNodes; // endpoints of pending obligations
    int *            pPendingMark;  // dense endpoint mark, size = Gia_ManObjNum
    int              nObjs;
    int              nPis;
    int              nRegs;
    int              nFramesTotal;
    int              nCoreCiNum;
    int              nPendingMax;
    int              nPendingAdded;
    int              nPendingCleared;
    int              nPendingPruned;
    int              nPendingActiveMax;
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
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static int Cec_DynSrmObjsStillMerged( Gia_Man_t * p, int iRepr, int iObj, int fRings )
{
    int iReprRoot, iObjRoot;
    if ( !fRings )
        return Gia_ObjHasSameRepr( p, iRepr, iObj );
    if ( iRepr == 0 )
        return Gia_ObjIsConst( p, iObj );
    iReprRoot = Gia_ObjIsHead( p, iRepr ) ? iRepr : Gia_ObjRepr( p, iRepr );
    iObjRoot  = Gia_ObjIsHead( p, iObj  ) ? iObj  : Gia_ObjRepr( p, iObj  );
    return iReprRoot == iObjRoot && iReprRoot != GIA_VOID;
}

static void Cec_DynSrmClearPendingMarks( Cec_DynSrm_t * p )
{
    int i, ObjId;
    Vec_IntForEachEntry( p->vPendingNodes, ObjId, i )
        p->pPendingMark[ObjId] = 0;
    Vec_IntClear( p->vPendingNodes );
}

static void Cec_DynSrmMarkPendingNode( Cec_DynSrm_t * p, int ObjId )
{
    if ( ObjId <= 0 || ObjId >= Gia_ManObjNum(p->pAig) )
        return;
    if ( p->pPendingMark[ObjId] )
        return;
    p->pPendingMark[ObjId] = 1;
    Vec_IntPush( p->vPendingNodes, ObjId );
}

static int Cec_DynSrmPairExists( Vec_Int_t * vPairs, int iRepr, int iObj )
{
    int i, Entry0, Entry1;
    Vec_IntForEachEntryDouble( vPairs, Entry0, Entry1, i )
        if ( Entry0 == iRepr && Entry1 == iObj )
            return 1;
    return 0;
}

static void Cec_DynSrmAddPendingPair( Cec_DynSrm_t * p, int iRepr, int iObj )
{
    if ( Cec_DynSrmPairExists(p->vPendingPairs, iRepr, iObj) )
        return;
    Vec_IntPush( p->vPendingPairs, iRepr );
    Vec_IntPush( p->vPendingPairs, iObj );
    Cec_DynSrmMarkPendingNode( p, iRepr );
    Cec_DynSrmMarkPendingNode( p, iObj );
    p->nPendingAdded++;
    p->nPendingMax = Abc_MaxInt( p->nPendingMax, Vec_IntSize(p->vPendingPairs) / 2 );
}

static int Cec_DynSrmNodePending( Cec_DynSrm_t * p, int ObjId )
{
    return ObjId > 0 && ObjId < Gia_ManObjNum(p->pAig) && p->pPendingMark[ObjId];
}

static int Cec_DynSrmActiveConst( Cec_DynSrm_t * p, int * pTfoMark, int ObjId )
{
    return (pTfoMark && pTfoMark[ObjId]) || Cec_DynSrmNodePending( p, ObjId );
}

static int Cec_DynSrmActivePair( Cec_DynSrm_t * p, int * pTfoMark, int fRings, int iPrev, int iObj )
{
    int fActive;
    if ( !fRings )
    {
        fActive = pTfoMark != NULL && (pTfoMark[iPrev] || pTfoMark[iObj]);
        return fActive || Cec_DynSrmNodePending(p, iPrev) || Cec_DynSrmNodePending(p, iObj);
    }
    fActive = pTfoMark != NULL &&
              (pTfoMark[iPrev] || pTfoMark[iObj] ||
               Cec_IncrMgrRingEdgeChanged( p->pIncr, iPrev, iObj ));
    return fActive || Cec_DynSrmNodePending(p, iPrev) || Cec_DynSrmNodePending(p, iObj);
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
    if ( p->pCore )
        Gia_ManStop( p->pCore );
    p->pCore = NULL;
    Vec_IntFreeP( &p->vSpecLits );
    Vec_IntFreeP( &p->vOutLits );
    Vec_IntFreeP( &p->vCopyTouched );
    Vec_IntFreeP( &p->vPiMap );
    Vec_IntFreeP( &p->vRoMap );
    p->nObjs = p->nPis = p->nRegs = p->nFramesTotal = p->nCoreCiNum = 0;
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
    p->vPendingPairs = Vec_IntAlloc( 64 );
    p->vPendingNodes = Vec_IntAlloc( 64 );
    p->pPendingMark = ABC_CALLOC( int, Gia_ManObjNum(pAig) );
    return p;
}

void Cec_DynSrmFree( Cec_DynSrm_t * p )
{
    if ( p == NULL )
        return;
    Cec_DynSrmResetCore( p );
    Vec_IntFree( p->vPendingPairs );
    Vec_IntFree( p->vPendingNodes );
    ABC_FREE( p->pPendingMark );
    ABC_FREE( p );
}

int Cec_DynSrmPendingNum( Cec_DynSrm_t * p )
{
    return p ? Vec_IntSize(p->vPendingPairs) / 2 : 0;
}

void Cec_DynSrmPrintStats( Cec_DynSrm_t * p )
{
    if ( p == NULL )
        return;
    Abc_Print( 1, "DynSRM: builds = %d, active_builds = %d, pending_add = %d, pending_clear = %d, pending_prune = %d, pending_max = %d, pending_active_max = %d, pending_now = %d\n",
        p->nBuilds, p->nBuildsActive, p->nPendingAdded, p->nPendingCleared,
        p->nPendingPruned, p->nPendingMax, p->nPendingActiveMax,
        Vec_IntSize(p->vPendingPairs) / 2 );
    Abc_Print( 1, "DynSRM: core_resets = %d, core_builds = %d, view_builds = %d, out_lits_last/max = %d/%d, core_objs_last/max = %d/%d, view_objs_last/max = %d/%d\n",
        p->nCoreResets, p->nCoreBuilds, p->nViewBuilds,
        p->nOutLitsLast, p->nOutLitsMax,
        p->nCoreObjsLast, p->nCoreObjsMax,
        p->nViewObjsLast, p->nViewObjsMax );
    Abc_Print( 1, "DynSRM: cache_full_clears = %d, cache_local_clears = %d, cache_local_entries = %d\n",
        p->nCacheFullClears, p->nCacheLocalClears, p->nCacheLocalEntries );
}

int Cec_DynSrmPrunePending( Cec_DynSrm_t * p, int fRings )
{
    Vec_Int_t * vOld;
    int i, iRepr, iObj;
    if ( p == NULL )
        return 0;
    vOld = p->vPendingPairs;
    p->vPendingPairs = Vec_IntAlloc( Vec_IntSize(vOld) );
    Cec_DynSrmClearPendingMarks( p );
    Vec_IntForEachEntryDouble( vOld, iRepr, iObj, i )
    {
        if ( !Cec_DynSrmObjsStillMerged(p->pAig, iRepr, iObj, fRings) )
        {
            p->nPendingCleared++;
            p->nPendingPruned++;
            continue;
        }
        Vec_IntPush( p->vPendingPairs, iRepr );
        Vec_IntPush( p->vPendingPairs, iObj );
        Cec_DynSrmMarkPendingNode( p, iRepr );
        Cec_DynSrmMarkPendingNode( p, iObj );
    }
    Vec_IntFree( vOld );
    return Vec_IntSize( p->vPendingPairs ) / 2;
}

void Cec_DynSrmCountActivePairs( Cec_DynSrm_t * p, int fRings, int * pTfoMark,
    int * pnTotal, int * pnActive, int * pnPendingActive )
{
    Gia_Man_t * pAig = p->pAig;
    Gia_Obj_t * pObj, * pRepr;
    int i, iPrev, iObj, PendingActive = 0;
    *pnTotal = *pnActive = 0;
    assert( pAig->pReprs != NULL );
    if ( fRings )
    {
        Gia_ManForEachObj1( pAig, pObj, i )
        {
            if ( Gia_ObjIsConst( pAig, i ) )
            {
                int fPending = Cec_DynSrmNodePending( p, i );
                (*pnTotal)++;
                (*pnActive) += Cec_DynSrmActiveConst( p, pTfoMark, i );
                PendingActive += fPending;
            }
            else if ( Gia_ObjIsHead( pAig, i ) )
            {
                iPrev = i;
                Gia_ClassForEachObj1( pAig, i, iObj )
                {
                    int fPending = Cec_DynSrmNodePending(p, iPrev) || Cec_DynSrmNodePending(p, iObj);
                    (*pnTotal)++;
                    (*pnActive) += Cec_DynSrmActivePair( p, pTfoMark, 1, iPrev, iObj );
                    PendingActive += fPending;
                    iPrev = iObj;
                }
                iObj = i;
                {
                    int fPending = Cec_DynSrmNodePending(p, iPrev) || Cec_DynSrmNodePending(p, iObj);
                    (*pnTotal)++;
                    (*pnActive) += Cec_DynSrmActivePair( p, pTfoMark, 1, iPrev, iObj );
                    PendingActive += fPending;
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
            PendingActive += Cec_DynSrmNodePending(p, idR) || Cec_DynSrmNodePending(p, i);
        }
    }
    if ( pnPendingActive )
    {
        *pnPendingActive = PendingActive;
        p->nPendingActiveMax = Abc_MaxInt( p->nPendingActiveMax, PendingActive );
    }
}

void Cec_DynSrmClearPending( Cec_DynSrm_t * p )
{
    if ( p == NULL )
        return;
    p->nPendingCleared += Vec_IntSize(p->vPendingPairs) / 2;
    Vec_IntClear( p->vPendingPairs );
    Cec_DynSrmClearPendingMarks( p );
}

int Cec_DynSrmUpdatePending( Cec_DynSrm_t * p, Vec_Str_t * vStatus, Vec_Int_t * vOutputs, int fRings )
{
    int i, Status, iRepr, iObj;
    if ( p == NULL )
        return 0;
    Cec_DynSrmClearPending( p );
    assert( 2 * Vec_StrSize(vStatus) == Vec_IntSize(vOutputs) );
    Vec_StrForEachEntry( vStatus, Status, i )
    {
        if ( Status != 0 )
            continue;
        iRepr = Vec_IntEntry( vOutputs, 2*i );
        iObj  = Vec_IntEntry( vOutputs, 2*i + 1 );
        if ( Cec_DynSrmObjsStillMerged(p->pAig, iRepr, iObj, fRings) )
            Cec_DynSrmAddPendingPair( p, iRepr, iObj );
    }
    return Vec_IntSize( p->vPendingPairs ) / 2;
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
    return Cec_DynSrmBuildView( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
