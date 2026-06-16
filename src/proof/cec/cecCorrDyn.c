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
    Vec_Int_t *      vPendingPairs; // SAT obligations still merged after resim
    Vec_Int_t *      vPendingNodes; // endpoints of pending obligations
    int *            pPendingMark;  // dense endpoint mark, size = Gia_ManObjNum
    int              nPendingMax;
    int              nPendingAdded;
    int              nPendingCleared;
    int              nPendingPruned;
    int              nPendingActiveMax;
    int              nBuilds;
    int              nBuildsActive;
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
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    Vec_Int_t * vXorLits;
    int f, i, iPrev, iObj, iPrevNew, iObjNew, iPrevRaw, iObjRaw;
    assert( p != NULL );
    assert( nFrames > 0 );
    assert( Gia_ManRegNum(p->pAig) > 0 );
    assert( p->pAig->pReprs != NULL );
    assert( Mode == CEC_EMIT_ALL || pTfoMask != NULL );
    p->nBuilds++;
    if ( Mode == CEC_EMIT_ACTIVE )
        p->nBuildsActive++;
    Vec_IntFill( &p->pAig->vCopies, (nFrames+fScorr)*Gia_ManObjNum(p->pAig), -1 );
    Gia_ManSetPhase( p->pAig );
    pNew = Gia_ManStart( nFrames * Gia_ManObjNum(p->pAig) );
    pNew->pName = Abc_UtilStrsav( p->pAig->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pAig->pSpec );
    Gia_ManHashAlloc( pNew );
    Gia_ObjSetCopyF( p->pAig, 0, Gia_ManConst0(p->pAig), 0 );
    Gia_ManForEachRo( p->pAig, pObj, i )
        Gia_ObjSetCopyF( p->pAig, 0, pObj, Gia_ManAppendCi(pNew) );
    Gia_ManForEachRo( p->pAig, pObj, i )
        if ( (pRepr = Gia_ObjReprObj(p->pAig, Gia_ObjId(p->pAig, pObj))) )
            Gia_ObjSetCopyF( p->pAig, 0, pObj, Gia_ObjCopyF(p->pAig, 0, pRepr) );
    for ( f = 0; f < nFrames+fScorr; f++ )
    {
        Gia_ObjSetCopyF( p->pAig, f, Gia_ManConst0(p->pAig), 0 );
        Gia_ManForEachPi( p->pAig, pObj, i )
            Gia_ObjSetCopyF( p->pAig, f, pObj, Gia_ManAppendCi(pNew) );
    }
    *pvOutputs = Vec_IntAlloc( 1000 );
    vXorLits = Vec_IntAlloc( 1000 );
    if ( fRings )
    {
        Gia_ManForEachObj1( p->pAig, pObj, i )
        {
            if ( Gia_ObjIsConst( p->pAig, i ) )
            {
                int fActive = Cec_DynSrmActiveConst( p, pTfoMask, i );
                if ( !Cec_DynSrmEmitModeAccept(fActive, Mode) )
                    continue;
                iObjRaw = Gia_ManCorrSpecReal( pNew, p->pAig, pObj, nFrames, 0 );
                iObjNew = Abc_LitNotCond( iObjRaw, Gia_ObjPhase(pObj) );
                if ( iObjNew != 0 )
                {
                    Vec_IntPush( *pvOutputs, 0 );
                    Vec_IntPush( *pvOutputs, i );
                    Vec_IntPush( vXorLits, iObjNew );
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
                        iPrevRaw = Gia_ManCorrSpecReal( pNew, p->pAig, Gia_ManObj(p->pAig, iPrev), nFrames, 0 );
                        iObjRaw  = Gia_ManCorrSpecReal( pNew, p->pAig, Gia_ManObj(p->pAig, iObj), nFrames, 0 );
                        iPrevNew = Abc_LitNotCond( iPrevRaw, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p->pAig, iPrev)) );
                        iObjNew  = Abc_LitNotCond( iObjRaw,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p->pAig, iObj)) );
                        if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                        {
                            Vec_IntPush( *pvOutputs, iPrev );
                            Vec_IntPush( *pvOutputs, iObj );
                            Vec_IntPush( vXorLits, Gia_ManHashAnd(pNew, iPrevNew, Abc_LitNot(iObjNew)) );
                        }
                    }
                    iPrev = iObj;
                }
                iObj = i;
                {
                    int fActive = Cec_DynSrmActivePair( p, pTfoMask, 1, iPrev, iObj );
                    if ( Cec_DynSrmEmitModeAccept(fActive, Mode) )
                    {
                        iPrevRaw = Gia_ManCorrSpecReal( pNew, p->pAig, Gia_ManObj(p->pAig, iPrev), nFrames, 0 );
                        iObjRaw  = Gia_ManCorrSpecReal( pNew, p->pAig, Gia_ManObj(p->pAig, iObj), nFrames, 0 );
                        iPrevNew = Abc_LitNotCond( iPrevRaw, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p->pAig, iPrev)) );
                        iObjNew  = Abc_LitNotCond( iObjRaw,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p->pAig, iObj)) );
                        if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                        {
                            Vec_IntPush( *pvOutputs, iPrev );
                            Vec_IntPush( *pvOutputs, iObj );
                            Vec_IntPush( vXorLits, Gia_ManHashAnd(pNew, iPrevNew, Abc_LitNot(iObjNew)) );
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
            iPrevRaw = Gia_ObjIsConst(p->pAig, i)? 0 : Gia_ManCorrSpecReal( pNew, p->pAig, pRepr, nFrames, 0 );
            iObjRaw  = Gia_ManCorrSpecReal( pNew, p->pAig, pObj, nFrames, 0 );
            iPrevNew = iPrevRaw;
            iObjNew  = Abc_LitNotCond( iObjRaw, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                Vec_IntPush( *pvOutputs, Gia_ObjId(p->pAig, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p->pAig, pObj) );
                Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, iPrevNew, iObjNew) );
            }
        }
    }
    Vec_IntForEachEntry( vXorLits, iObjNew, i )
        Gia_ManAppendCo( pNew, iObjNew );
    Vec_IntFree( vXorLits );
    Gia_ManHashStop( pNew );
    Vec_IntErase( &p->pAig->vCopies );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
