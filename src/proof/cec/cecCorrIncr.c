/**CFile****************************************************************

  FileName    [cecCorrIncr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Incremental active-list / TFO filter for &scorr.]

  Author      [Xiran Zhao]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 2026.]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// Allocate the manager. Builds static fanout on pAig if not already present;
// fOwnsFanout records that we must release it ourselves on Free.
Cec_IncrMgr_t * Cec_IncrMgrAlloc( Gia_Man_t * pAig, int nFrames )
{
    Cec_IncrMgr_t * p = ABC_CALLOC( Cec_IncrMgr_t, 1 );
    p->pAig      = pAig;
    p->nFrames   = nFrames;
    p->nObjs     = Gia_ManObjNum(pAig);
    p->vReprPrev = Vec_IntStartFull( p->nObjs );
    p->vNextPrev = Vec_IntStart( p->nObjs );
    p->vSeeds    = Vec_IntAlloc( 64 );
    p->vTfoNodes = Vec_IntAlloc( 1024 );
    p->pTfoMark  = ABC_CALLOC( int, p->nObjs );
    p->vBfsCur   = Vec_IntAlloc( 1024 );
    p->vBfsNext  = Vec_IntAlloc( 1024 );
    if ( pAig->vFanout == NULL )
    {
        Gia_ManStaticFanoutStart( pAig );
        p->fOwnsFanout = 1;
    }
    return p;
}

void Cec_IncrMgrFree( Cec_IncrMgr_t * p )
{
    if ( p == NULL ) return;
    if ( p->fOwnsFanout )
        Gia_ManStaticFanoutStop( p->pAig );
    Vec_IntFree( p->vReprPrev );
    Vec_IntFree( p->vNextPrev );
    Vec_IntFree( p->vSeeds );
    Vec_IntFree( p->vTfoNodes );
    Vec_IntFree( p->vBfsCur );
    Vec_IntFree( p->vBfsNext );
    ABC_FREE( p->pTfoMark );
    ABC_FREE( p );
}

// Capture the equivalence-class state whose pairs were just emitted into the
// SRM, so the next iteration can diff against it to find stale pairs.
void Cec_IncrMgrSnapshotClasses( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int i;
    assert( pAig->pReprs != NULL );
    for ( i = 0; i < p->nObjs; i++ )
    {
        Vec_IntWriteEntry( p->vReprPrev, i, Gia_ObjRepr(pAig, i) );
        Vec_IntWriteEntry( p->vNextPrev, i, pAig->pNexts ? Gia_ObjNext(pAig, i) : 0 );
    }
}

// Seeds = nodes whose pReprs changed since the snapshot. pNexts changes are
// handled separately because a ring-link rewrite is an edge-local event, not
// a new fanout cone to re-prove.
int Cec_IncrMgrComputeSeeds( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int i, reprNew, reprOld;
    Vec_IntClear( p->vSeeds );
    for ( i = 1; i < p->nObjs; i++ )
    {
        reprNew = Gia_ObjRepr( pAig, i );
        reprOld = Vec_IntEntry( p->vReprPrev, i );
        if ( reprNew != reprOld )
            Vec_IntPush( p->vSeeds, i );
    }
    return Vec_IntSize( p->vSeeds );
}

int Cec_IncrMgrCountNextChanges( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int i, nChanges = 0;
    if ( pAig->pNexts == NULL )
        return 0;
    for ( i = 1; i < p->nObjs; i++ )
        nChanges += Gia_ObjNext( pAig, i ) != Vec_IntEntry( p->vNextPrev, i );
    return nChanges;
}

// Has the current ring edge (iPrev -> iObj) appeared since the snapshot?
// Explicit edges live in pNexts. The implicit closing edge (tail -> head) does
// not, so we reconstruct whether the same tail/head pair already existed.
int Cec_IncrMgrRingEdgeChanged( Cec_IncrMgr_t * p, int iPrev, int iObj )
{
    Gia_Man_t * pAig;
    int iNextCur, iNextOld;
    if ( p == NULL )
        return 0;
    pAig = p->pAig;
    if ( pAig->pNexts == NULL )
        return 0;
    iNextCur = Gia_ObjNext( pAig, iPrev );
    iNextOld = Vec_IntEntry( p->vNextPrev, iPrev );
    if ( iNextCur == iObj )
        return iNextOld != iObj;
    if ( iNextCur > 0 )
        return 1; // conservative: should not happen for callers below
    // Closing edge: prove if the previous snapshot did not already contain
    // exactly this tail/head pair as a ring's closing edge.
    return iNextOld > 0 ||
           Vec_IntEntry( p->vReprPrev, iPrev ) != iObj ||
           Vec_IntEntry( p->vReprPrev, iObj ) != GIA_VOID ||
           Vec_IntEntry( p->vNextPrev, iObj ) <= 0;
}

// Approximate count of (total, active) candidate pairs before SRM build.
// Mirrors the PO-emission loops below; the SRM may still simplify pairs away,
// so the result is only used to decide whether the active filter is worth it.
void Cec_IncrMgrCountActivePairs( Cec_IncrMgr_t * p, int fRings, int * pTfoMark,
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
                (*pnActive) += pTfoMark == NULL || pTfoMark[i];
            }
            else if ( Gia_ObjIsHead( pAig, i ) )
            {
                iPrev = i;
                Gia_ClassForEachObj1( pAig, i, iObj )
                {
                    (*pnTotal)++;
                    (*pnActive) += pTfoMark == NULL || pTfoMark[iPrev] || pTfoMark[iObj] ||
                                   Cec_IncrMgrRingEdgeChanged( p, iPrev, iObj );
                    iPrev = iObj;
                }
                iObj = i; // closing edge tail -> head
                (*pnTotal)++;
                (*pnActive) += pTfoMark == NULL || pTfoMark[iPrev] || pTfoMark[iObj] ||
                               Cec_IncrMgrRingEdgeChanged( p, iPrev, iObj );
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
            (*pnActive) += pTfoMark == NULL || pTfoMark[i] || pTfoMark[idR];
        }
    }
}

// Forward TFO BFS from seeds across nFrames unrollings. Marks pTfoMark[id]=1
// for every AIG node reachable from a seed within nFrames steps. RI fanouts
// cross to the next frame via Gia_ObjRiToRo. RIs themselves are intentionally
// not marked: SRM emission is keyed on AIG candidates (ANDs/CIs), not COs.
// vTfoNodes records every marked id so we can clear marks in O(|TFO|).
void Cec_IncrMgrComputeTfo( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int * pMark = p->pTfoMark;
    int f, i, k, Id, FanId, RoId;

    Vec_IntForEachEntry( p->vTfoNodes, Id, i )
        pMark[Id] = 0;
    Vec_IntClear( p->vTfoNodes );
    Vec_IntClear( p->vBfsCur );
    Vec_IntClear( p->vBfsNext );

    Vec_IntForEachEntry( p->vSeeds, Id, i )
    {
        if ( !pMark[Id] )
        {
            pMark[Id] = 1;
            Vec_IntPush( p->vTfoNodes, Id );
            Vec_IntPush( p->vBfsCur, Id );
        }
    }

    for ( f = 0; f <= p->nFrames; f++ )
    {
        int head = 0;
        while ( head < Vec_IntSize(p->vBfsCur) )
        {
            Gia_Obj_t * pFan;
            Id = Vec_IntEntry( p->vBfsCur, head++ );
            int nFan = Gia_ObjFanoutNumId( pAig, Id );
            for ( k = 0; k < nFan; k++ )
            {
                FanId = Gia_ObjFanoutId( pAig, Id, k );
                pFan  = Gia_ManObj( pAig, FanId );
                if ( Gia_ObjIsRi(pAig, pFan) )
                {
                    if ( f < p->nFrames )
                    {
                        RoId = Gia_ObjRiToRoId( pAig, FanId );
                        if ( !pMark[RoId] )
                        {
                            pMark[RoId] = 1;
                            Vec_IntPush( p->vTfoNodes, RoId );
                            Vec_IntPush( p->vBfsNext, RoId );
                        }
                    }
                }
                else if ( Gia_ObjIsCo(pFan) )
                {
                    // PO: not a candidate, skip
                }
                else
                {
                    if ( !pMark[FanId] )
                    {
                        pMark[FanId] = 1;
                        Vec_IntPush( p->vTfoNodes, FanId );
                        Vec_IntPush( p->vBfsCur, FanId );
                    }
                }
            }
        }
        Vec_IntClear( p->vBfsCur );
        Vec_IntAppend( p->vBfsCur, p->vBfsNext );
        Vec_IntClear( p->vBfsNext );
        if ( Vec_IntSize(p->vBfsCur) == 0 )
            break;
    }
}

// Variant of Gia_ManCorrSpecReduce that emits a candidate PO (a, b) only when
// pTfoMark[a] || pTfoMark[b]. In ring mode, a new/changed ring edge is also
// emitted even if neither endpoint is in the TFO. Passing pTfoMark==NULL is
// equivalent to the baseline.
Gia_Man_t * Gia_ManCorrSpecReduce_Active( Gia_Man_t * p, int nFrames, int fScorr,
                                          Vec_Int_t ** pvOutputs, int fRings,
                                          int * pTfoMark, Cec_IncrMgr_t * pIncr )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    Vec_Int_t * vXorLits;
    int f, i, iPrev, iObj, iPrevNew, iObjNew;
    assert( nFrames > 0 );
    assert( Gia_ManRegNum(p) > 0 );
    assert( p->pReprs != NULL );
    Vec_IntFill( &p->vCopies, (nFrames+fScorr)*Gia_ManObjNum(p), -1 );
    Gia_ManSetPhase( p );
    pNew = Gia_ManStart( nFrames * Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManHashAlloc( pNew );
    Gia_ObjSetCopyF( p, 0, Gia_ManConst0(p), 0 );
    Gia_ManForEachRo( p, pObj, i )
        Gia_ObjSetCopyF( p, 0, pObj, Gia_ManAppendCi(pNew) );
    Gia_ManForEachRo( p, pObj, i )
        if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
            Gia_ObjSetCopyF( p, 0, pObj, Gia_ObjCopyF(p, 0, pRepr) );
    for ( f = 0; f < nFrames+fScorr; f++ )
    {
        Gia_ObjSetCopyF( p, f, Gia_ManConst0(p), 0 );
        Gia_ManForEachPi( p, pObj, i )
            Gia_ObjSetCopyF( p, f, pObj, Gia_ManAppendCi(pNew) );
    }
    *pvOutputs = Vec_IntAlloc( 1000 );
    vXorLits = Vec_IntAlloc( 1000 );
    if ( fRings )
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( Gia_ObjIsConst( p, i ) )
            {
                if ( pTfoMark && !pTfoMark[i] )
                    continue;
                iObjNew = Gia_ManCorrSpecReal( pNew, p, pObj, nFrames, 0 );
                iObjNew = Abc_LitNotCond( iObjNew, Gia_ObjPhase(pObj) );
                if ( iObjNew != 0 )
                {
                    Vec_IntPush( *pvOutputs, 0 );
                    Vec_IntPush( *pvOutputs, i );
                    Vec_IntPush( vXorLits, iObjNew );
                }
            }
            else if ( Gia_ObjIsHead( p, i ) )
            {
                // Walk every ring edge so iPrev stays aligned with the class
                // order; emit only when an endpoint is in TFO or the edge is
                // new/rewired since the last snapshot.
                iPrev = i;
                Gia_ClassForEachObj1( p, i, iObj )
                {
                    int fEmit = (pTfoMark == NULL) || pTfoMark[iPrev] || pTfoMark[iObj] ||
                                Cec_IncrMgrRingEdgeChanged( pIncr, iPrev, iObj );
                    if ( fEmit )
                    {
                        iPrevNew = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iPrev), nFrames, 0 );
                        iObjNew  = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iObj), nFrames, 0 );
                        iPrevNew = Abc_LitNotCond( iPrevNew, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iPrev)) );
                        iObjNew  = Abc_LitNotCond( iObjNew,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iObj)) );
                        if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                        {
                            Vec_IntPush( *pvOutputs, iPrev );
                            Vec_IntPush( *pvOutputs, iObj );
                            Vec_IntPush( vXorLits, Gia_ManHashAnd(pNew, iPrevNew, Abc_LitNot(iObjNew)) );
                        }
                    }
                    iPrev = iObj;
                }
                // Closing edge tail -> head
                iObj = i;
                {
                    int fEmit = (pTfoMark == NULL) || pTfoMark[iPrev] || pTfoMark[iObj] ||
                                Cec_IncrMgrRingEdgeChanged( pIncr, iPrev, iObj );
                    if ( fEmit )
                    {
                        iPrevNew = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iPrev), nFrames, 0 );
                        iObjNew  = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iObj), nFrames, 0 );
                        iPrevNew = Abc_LitNotCond( iPrevNew, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iPrev)) );
                        iObjNew  = Abc_LitNotCond( iObjNew,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iObj)) );
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
        Gia_ManForEachObj1( p, pObj, i )
        {
            pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
            if ( pRepr == NULL )
                continue;
            if ( pTfoMark )
            {
                int idR = Gia_ObjId(p, pRepr);
                if ( !pTfoMark[i] && !pTfoMark[idR] )
                    continue;
            }
            iPrevNew = Gia_ObjIsConst(p, i)? 0 : Gia_ManCorrSpecReal( pNew, p, pRepr, nFrames, 0 );
            iObjNew  = Gia_ManCorrSpecReal( pNew, p, pObj, nFrames, 0 );
            iObjNew  = Abc_LitNotCond( iObjNew, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pObj) );
                Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, iPrevNew, iObjNew) );
            }
        }
    }
    Vec_IntForEachEntry( vXorLits, iObjNew, i )
        Gia_ManAppendCo( pNew, iObjNew );
    Vec_IntFree( vXorLits );
    Gia_ManHashStop( pNew );
    Vec_IntErase( &p->vCopies );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

// Variant of Gia_ManCorrSpecReduceInit (BMC SRM) with the same active filter.
// The baseline BMC SRM ignores its fRings flag -- topology is always
// (head, member) pairs from pReprs alone, with no ring edges -- so this
// variant only filters on pReprs-derived endpoints. pTfoMark==NULL falls back
// to the baseline.
Gia_Man_t * Gia_ManCorrSpecReduceInit_Active( Gia_Man_t * p, int nFrames, int nPrefix, int fScorr,
                                              Vec_Int_t ** pvOutputs, int * pTfoMark )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    Vec_Int_t * vXorLits;
    int f, i, iPrevNew, iObjNew;
    assert( (!fScorr && nFrames > 1) || (fScorr && nFrames > 0) || nPrefix );
    assert( Gia_ManRegNum(p) > 0 );
    assert( p->pReprs != NULL );
    Vec_IntFill( &p->vCopies, (nFrames+nPrefix+fScorr)*Gia_ManObjNum(p), -1 );
    Gia_ManSetPhase( p );
    pNew = Gia_ManStart( (nFrames+nPrefix) * Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachRo( p, pObj, i )
    {
        Gia_ManAppendCi(pNew);
        Gia_ObjSetCopyF( p, 0, pObj, 0 );
    }
    for ( f = 0; f < nFrames+nPrefix+fScorr; f++ )
    {
        Gia_ObjSetCopyF( p, f, Gia_ManConst0(p), 0 );
        Gia_ManForEachPi( p, pObj, i )
            Gia_ObjSetCopyF( p, f, pObj, Gia_ManAppendCi(pNew) );
    }
    *pvOutputs = Vec_IntAlloc( 1000 );
    vXorLits = Vec_IntAlloc( 1000 );
    for ( f = nPrefix; f < nFrames+nPrefix; f++ )
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
            if ( pRepr == NULL )
                continue;
            if ( pTfoMark )
            {
                int idR = Gia_ObjId(p, pRepr);
                if ( !pTfoMark[i] && !pTfoMark[idR] )
                    continue;
            }
            iPrevNew = Gia_ObjIsConst(p, i)? 0 : Gia_ManCorrSpecReal( pNew, p, pRepr, f, nPrefix );
            iObjNew  = Gia_ManCorrSpecReal( pNew, p, pObj, f, nPrefix );
            iObjNew  = Abc_LitNotCond( iObjNew, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pObj) );
                Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, iPrevNew, iObjNew) );
            }
        }
    }
    Vec_IntForEachEntry( vXorLits, iObjNew, i )
        Gia_ManAppendCo( pNew, iObjNew );
    Vec_IntFree( vXorLits );
    Gia_ManHashStop( pNew );
    Vec_IntErase( &p->vCopies );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
