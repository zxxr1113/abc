/**CFile****************************************************************

  FileName    [cecCorr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Latch/signal correspondence computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecCorr.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

static inline int Cec_ParCorShouldStop( Cec_ParCor_t * pPars )
{
    if ( pPars == NULL || pPars->pFunc == NULL )
        return 0;
    return ((int (*)(void *))pPars->pFunc)( pPars->pData );
}


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Gia_ManCorrSpecReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f, int nPrefix );
static inline int Gia_ManCorrSpecReal( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f, int nPrefix );

////////////////////////////////////////////////////////////////////////
///        INCREMENTAL ACTIVE-LIST SRM (TFO-triggered re-proof)      ///
////////////////////////////////////////////////////////////////////////
//
// Theory: in &scorr's main loop, every iteration rebuilds the SRM and
// re-proves all candidate equivalence pairs. Once BMC has converged the
// classes, only a handful of pairs are disproved per iteration, yet we
// pay the SAT cost of re-proving ~all remaining pairs. The incremental
// strategy exploits this monotonicity:
//
//   A pair P = (iRepr, iObj) that was UNSAT in round r-1 is GUARANTEED
//   to remain UNSAT in round r if no node X in the SRM TFI of P had its
//   equivalence-class state modified between rounds.
//
// Equivalently: P needs re-verification iff some "seed" (a node with a
// changed pReprs entry since last round) lies in TFI(P) inside the k-frame
// unrolling -- equivalently, iRepr or iObj lies in TFO_k(seeds).
// In ring mode, pNexts changes are handled separately: refinement can create
// new ring edges without changing the surviving endpoints' representatives,
// but such an edge only needs the new pair itself to be re-proved. Treating
// every pNexts change as a TFO seed is correct but too conservative.
//
// We build the SRM exactly as before (so speculative reduction still
// keeps the SRM compact -- this is the lesson from v3.0/rIC3-domain:
// don't disturb spec-reduction), but we EMIT miter POs only for pairs
// whose endpoints are inside TFO_k(seeds). All other previously-proved
// pairs are skipped. Correctness rests on the monotonicity argument
// above; the worst case (large seed set / huge TFO) falls back to the
// full SRM build, which matches baseline behaviour.

typedef struct Cec_IncrMgr_t_ Cec_IncrMgr_t;
struct Cec_IncrMgr_t_
{
    Gia_Man_t *  pAig;            // host AIG (immutable across iterations)
    int          nFrames;         // unrolling depth used by the SRM builder
    int          nObjs;           // cached Gia_ManObjNum(pAig)
    Vec_Int_t *  vReprPrev;       // snapshot of pReprs from previous round
    Vec_Int_t *  vNextPrev;       // snapshot of pNexts from previous round
    Vec_Int_t *  vSeeds;          // nodes whose pReprs changed since snapshot
    Vec_Int_t *  vTfoNodes;       // ids currently in TFO (for fast clearing)
    int *        pTfoMark;        // dense mark array, size = nObjs
    Vec_Int_t *  vBfsCur;         // BFS frontier for current frame
    Vec_Int_t *  vBfsNext;        // BFS frontier carried to next frame
    int          fOwnsFanout;     // 1 if we built static fanout (must free)
};

/**Function*************************************************************
  Synopsis    [Allocate the incremental manager.]
  SideEffects [Builds static fanout on pAig if not present.]
***********************************************************************/
static Cec_IncrMgr_t * Cec_IncrMgrAlloc( Gia_Man_t * pAig, int nFrames )
{
    Cec_IncrMgr_t * p = ABC_CALLOC( Cec_IncrMgr_t, 1 );
    p->pAig      = pAig;
    p->nFrames   = nFrames;
    p->nObjs     = Gia_ManObjNum(pAig);
    p->vReprPrev = Vec_IntStartFull( p->nObjs );  // init to GIA_VOID-equivalent (-1)
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

static void Cec_IncrMgrFree( Cec_IncrMgr_t * p )
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

/**Function*************************************************************
  Synopsis    [Snapshot current equivalence-class state.]
  Description [O(N). Called after SRM construction and before SAT/sim
               refinement, so the next iteration can diff against the
               class state whose pairs were just proved.]
***********************************************************************/
static void Cec_IncrMgrSnapshotClasses( Cec_IncrMgr_t * p )
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

/**Function*************************************************************
  Synopsis    [Compute seeds: nodes whose representative changed.]
  Description [O(N). Returns size of seed set. Does NOT update snapshot
               (caller decides when to snapshot). pNexts is intentionally
               excluded here; ring-link changes are handled edge-locally.]
***********************************************************************/
static int Cec_IncrMgrComputeSeeds( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int i, reprNew, reprOld;
    Vec_IntClear( p->vSeeds );
    for ( i = 1; i < p->nObjs; i++ )  // skip const0
    {
        reprNew = Gia_ObjRepr( pAig, i );
        reprOld = Vec_IntEntry( p->vReprPrev, i );
        if ( reprNew != reprOld )
            Vec_IntPush( p->vSeeds, i );
    }
    return Vec_IntSize( p->vSeeds );
}

/**Function*************************************************************
  Synopsis    [Count nodes whose ring-list successor changed.]
  Description [Used only for convergence/fallback decisions. These nodes
               are not TFO seeds because a pNexts-only change creates a
               new ring edge, not a new fanout cone to re-prove.]
***********************************************************************/
static int Cec_IncrMgrCountNextChanges( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int i, nChanges = 0;
    if ( pAig->pNexts == NULL )
        return 0;
    for ( i = 1; i < p->nObjs; i++ )  // skip const0
        nChanges += Gia_ObjNext( pAig, i ) != Vec_IntEntry( p->vNextPrev, i );
    return nChanges;
}

/**Function*************************************************************
  Synopsis    [Detect whether a current ring edge is new since snapshot.]
  Description [Ring classes store list edges explicitly in pNexts, but the
               SRM also proves the implicit closing edge tail -> head.  For
               explicit edges, compare the predecessor's pNexts slot.  For
               the closing edge, reconstruct whether the same tail/head pair
               existed in the previous snapshot.]
***********************************************************************/
static int Cec_IncrMgrRingEdgeChanged( Cec_IncrMgr_t * p, int iPrev, int iObj )
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
        return 1; // should not happen for callers below; prove conservatively

    // Current edge is the implicit closing edge (tail -> head).
    return iNextOld > 0 ||
           Vec_IntEntry( p->vReprPrev, iPrev ) != iObj ||
           Vec_IntEntry( p->vReprPrev, iObj ) != GIA_VOID ||
           Vec_IntEntry( p->vNextPrev, iObj ) <= 0;
}

/**Function*************************************************************
  Synopsis    [Count total and active candidate pairs before SRM building.]
  Description [This mirrors the PO-emission loops below, but stops before
               constructing the unrolled network.  The count is approximate
               because SRM construction can still simplify a pair away; it
               is only used to decide when active filtering is worth it.]
***********************************************************************/
static void Cec_IncrMgrCountActivePairs( Cec_IncrMgr_t * p, int fRings, int * pTfoMark,
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
                // Include the implicit closing edge (tail -> head).
                iObj = i;
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

/**Function*************************************************************
  Synopsis    [BFS forward TFO of seeds across nFrames unrollings.]
  Description [Marks pTfoMark[id]=1 for every AIG node that is reachable
               from any seed within nFrames combinational+sequential
               steps. RI fanouts cross to the next frame via Gia_ObjRiToRo.
               Cost: O(|TFO_k| * avg_fanout). Memory: amortised - we only
               clear marks for nodes recorded in vTfoNodes.]
***********************************************************************/
static void Cec_IncrMgrComputeTfo( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int * pMark = p->pTfoMark;
    int f, i, k, Id, FanId, RoId;

    // O(|previous TFO|) clear -- avoids touching the global N-sized array
    Vec_IntForEachEntry( p->vTfoNodes, Id, i )
        pMark[Id] = 0;
    Vec_IntClear( p->vTfoNodes );
    Vec_IntClear( p->vBfsCur );
    Vec_IntClear( p->vBfsNext );

    // Seed the frontier
    Vec_IntForEachEntry( p->vSeeds, Id, i )
    {
        if ( !pMark[Id] )
        {
            pMark[Id] = 1;
            Vec_IntPush( p->vTfoNodes, Id );
            Vec_IntPush( p->vBfsCur, Id );
        }
    }

    // For each frame f = 0..nFrames: do combinational fanout BFS, then
    // walk RI fanouts to corresponding ROs in the next frame. After
    // nFrames cross-frame jumps we stop -- pairs deeper than this cannot
    // depend on the seeds within an nFrames-deep SRM.
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
                    // Cross-frame: schedule the corresponding RO for the
                    // next frame's BFS, only if we haven't exhausted depth.
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
                    // RI itself is intentionally NOT marked: SRM emission
                    // is keyed on AIG candidate nodes (ANDs/CIs), not COs.
                }
                else if ( Gia_ObjIsCo(pFan) )
                {
                    // Primary output -- not a candidate; skip.
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
        // Promote next-frame frontier to current
        Vec_IntClear( p->vBfsCur );
        Vec_IntAppend( p->vBfsCur, p->vBfsNext );
        Vec_IntClear( p->vBfsNext );
        if ( Vec_IntSize(p->vBfsCur) == 0 )
            break;
    }
}

/**Function*************************************************************
  Synopsis    [Variant of Gia_ManCorrSpecReduce that emits miter POs only
               for active candidate pairs.]
  Description [Identical to Gia_ManCorrSpecReduce w.r.t. SRM topology and
               speculative reduction. The ONLY difference is the emission
               filter: a pair (a, b) is emitted iff pTfoMark[a] || pTfoMark[b].
               In ring mode, a new/changed ring edge is also emitted even if
               neither endpoint is in TFO. Passing pTfoMark==NULL is equivalent
               to the baseline.]
***********************************************************************/
static Gia_Man_t * Gia_ManCorrSpecReduce_Active( Gia_Man_t * p, int nFrames, int fScorr,
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
                // const-class: pair is (0, i). Filter on i.
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
                // Ring class. Emit old edges only when their endpoints are in
                // TFO; emit new/rewired edges directly because they had no
                // previous UNSAT result to reuse. We still walk the full ring
                // so iPrev stays aligned with the current class order.
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
                // closing edge of the ring: (iPrev, head)
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
            // pair = (pRepr, pObj). Filter on either endpoint.
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


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the real value of the literal w/o spec reduction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_ManCorrSpecReal( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f, int nPrefix )
{
    if ( Gia_ObjIsAnd(pObj) )
    {
        Gia_ManCorrSpecReduce_rec( pNew, p, Gia_ObjFanin0(pObj), f, nPrefix );
        Gia_ManCorrSpecReduce_rec( pNew, p, Gia_ObjFanin1(pObj), f, nPrefix );
        return Gia_ManHashAnd( pNew, Gia_ObjFanin0CopyF(p, f, pObj), Gia_ObjFanin1CopyF(p, f, pObj) );
    }
    if ( f == 0 )
    {
        assert( Gia_ObjIsRo(p, pObj) );
        return Gia_ObjCopyF(p, f, pObj);
    }
    assert( f && Gia_ObjIsRo(p, pObj) );
    pObj = Gia_ObjRoToRi( p, pObj );
    Gia_ManCorrSpecReduce_rec( pNew, p, Gia_ObjFanin0(pObj), f-1, nPrefix );
    return Gia_ObjFanin0CopyF( p, f-1, pObj );
}

/**Function*************************************************************

  Synopsis    [Recursively performs speculative reduction for the object.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCorrSpecReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f, int nPrefix )
{
    Gia_Obj_t * pRepr;
    int iLitNew;
    if ( ~Gia_ObjCopyF(p, f, pObj) )
        return;
    if ( f >= nPrefix && (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
    {
        Gia_ManCorrSpecReduce_rec( pNew, p, pRepr, f, nPrefix );
        iLitNew = Abc_LitNotCond( Gia_ObjCopyF(p, f, pRepr), Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
        Gia_ObjSetCopyF( p, f, pObj, iLitNew );
        return;
    }
    assert( Gia_ObjIsCand(pObj) );
    iLitNew = Gia_ManCorrSpecReal( pNew, p, pObj, f, nPrefix );
    Gia_ObjSetCopyF( p, f, pObj, iLitNew );
}

/**Function*************************************************************

  Synopsis    [Derives SRM for signal correspondence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManCorrSpecReduce( Gia_Man_t * p, int nFrames, int fScorr, Vec_Int_t ** pvOutputs, int fRings )
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
                iPrev = i;
                Gia_ClassForEachObj1( p, i, iObj )
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
                    iPrev = iObj;
                }
                iObj = i;
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
    else
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
            if ( pRepr == NULL )
                continue;
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
//Abc_Print( 1, "Before sweeping = %d\n", Gia_ManAndNum(pNew) );
    pNew = Gia_ManCleanup( pTemp = pNew );
//Abc_Print( 1, "After sweeping = %d\n", Gia_ManAndNum(pNew) );
    Gia_ManStop( pTemp );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Derives SRM for signal correspondence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManCorrSpecReduceInit( Gia_Man_t * p, int nFrames, int nPrefix, int fScorr, Vec_Int_t ** pvOutputs, int fRings )
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
//Abc_Print( 1, "Before sweeping = %d\n", Gia_ManAndNum(pNew) );
    pNew = Gia_ManCleanup( pTemp = pNew );
//Abc_Print( 1, "After sweeping = %d\n", Gia_ManAndNum(pNew) );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Active variant of Gia_ManCorrSpecReduceInit for BMC.]

  Description [Identical to Gia_ManCorrSpecReduceInit but emits a
               candidate PO (pRepr, pObj) only when at least one of the
               endpoints lies in pTfoMark.  Note: the upstream BMC SRM
               builder takes an fRings flag but never inspects it -- the
               topology is always (head, member) pairs derived from
               pReprs alone, with no ring edges.  Therefore the active
               variant only needs pReprs-driven seeds; pNexts changes
               cannot affect this SRM and there is no closing edge to
               reprove.  Passing pTfoMark==NULL falls back to the
               baseline behaviour.]

***********************************************************************/
static Gia_Man_t * Gia_ManCorrSpecReduceInit_Active( Gia_Man_t * p, int nFrames, int nPrefix, int fScorr,
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
            // Active filter: skip pairs whose endpoints are both outside TFO.
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

/**Function*************************************************************

  Synopsis    [Initializes simulation info for lcorr/scorr counter-examples.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManStartSimInfo( Vec_Ptr_t * vInfo, int nFlops )
{
    unsigned * pInfo;
    int k, w, nWords;
    nWords = Vec_PtrReadWordsSimInfo( vInfo );
    assert( nFlops <= Vec_PtrSize(vInfo) );
    for ( k = 0; k < nFlops; k++ )
    {
        pInfo = (unsigned *)Vec_PtrEntry( vInfo, k );
        for ( w = 0; w < nWords; w++ )
            pInfo[w] = 0;
    }
    for ( k = nFlops; k < Vec_PtrSize(vInfo); k++ )
    {
        pInfo = (unsigned *)Vec_PtrEntry( vInfo, k );
        for ( w = 0; w < nWords; w++ )
            pInfo[w] = Gia_ManRandom( 0 );
    }
}

/**Function*************************************************************

  Synopsis    [Remaps simulation info from SRM to the original AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCorrRemapSimInfo( Gia_Man_t * p, Vec_Ptr_t * vInfo )
{
    Gia_Obj_t * pObj, * pRepr;
    unsigned * pInfoObj, * pInfoRepr;
    int i, w, nWords;
    nWords = Vec_PtrReadWordsSimInfo( vInfo );
    Gia_ManForEachRo( p, pObj, i )
    {
        // skip ROs without representatives
        pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
        if ( pRepr == NULL || Gia_ObjFailed(p, Gia_ObjId(p,pObj)) )
            continue;
        pInfoObj = (unsigned *)Vec_PtrEntry( vInfo, i );
        for ( w = 0; w < nWords; w++ )
            assert( pInfoObj[w] == 0 );
        // skip ROs with constant representatives
        if ( Gia_ObjIsConst0(pRepr) )
            continue;
        assert( Gia_ObjIsRo(p, pRepr) );
//        Abc_Print( 1, "%d -> %d    ", i, Gia_ObjId(p, pRepr) );
        // transfer info from the representative
        pInfoRepr = (unsigned *)Vec_PtrEntry( vInfo, Gia_ObjCioId(pRepr) - Gia_ManPiNum(p) );
        for ( w = 0; w < nWords; w++ )
            pInfoObj[w] = pInfoRepr[w];
    }
//    Abc_Print( 1, "\n" );
}

/**Function*************************************************************

  Synopsis    [Collects information about remapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManCorrCreateRemapping( Gia_Man_t * p )
{
    Vec_Int_t * vPairs;
    Gia_Obj_t * pObj, * pRepr;
    int i;
    vPairs = Vec_IntAlloc( 100 );
    Gia_ManForEachRo( p, pObj, i )
    {
        // skip ROs without representatives
        pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
        if ( pRepr == NULL || Gia_ObjIsConst0(pRepr) || Gia_ObjFailed(p, Gia_ObjId(p,pObj)) )
//        if ( pRepr == NULL || Gia_ObjIsConst0(pRepr) || Gia_ObjIsFailedPair(p, Gia_ObjId(p, pRepr), Gia_ObjId(p, pObj)) )
            continue;
        assert( Gia_ObjIsRo(p, pRepr) );
//        Abc_Print( 1, "%d -> %d    ", Gia_ObjId(p,pObj), Gia_ObjId(p, pRepr) );
        // remember the pair
        Vec_IntPush( vPairs, Gia_ObjCioId(pRepr) - Gia_ManPiNum(p) );
        Vec_IntPush( vPairs, i );
    }
    return vPairs;
}

/**Function*************************************************************

  Synopsis    [Remaps simulation info from SRM to the original AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCorrPerformRemapping( Vec_Int_t * vPairs, Vec_Ptr_t * vInfo )
{
    unsigned * pInfoObj, * pInfoRepr;
    int w, i, iObj, iRepr, nWords;
    nWords = Vec_PtrReadWordsSimInfo( vInfo );
    Vec_IntForEachEntry( vPairs, iRepr, i )
    {
        iObj = Vec_IntEntry( vPairs, ++i );
        pInfoObj = (unsigned *)Vec_PtrEntry( vInfo, iObj );
        pInfoRepr = (unsigned *)Vec_PtrEntry( vInfo, iRepr );
        for ( w = 0; w < nWords; w++ )
        {
            assert( pInfoObj[w] == 0 );
            pInfoObj[w] = pInfoRepr[w];
        }
    }
}

/**Function*************************************************************

  Synopsis    [Packs one counter-examples into the array of simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

*************************************`**********************************/
int Cec_ManLoadCounterExamplesTry( Vec_Ptr_t * vInfo, Vec_Ptr_t * vPres, int iBit, int * pLits, int nLits )
{
    unsigned * pInfo, * pPres;
    int i;
    for ( i = 0; i < nLits; i++ )
    {
        pInfo = (unsigned *)Vec_PtrEntry(vInfo, Abc_Lit2Var(pLits[i]));
        pPres = (unsigned *)Vec_PtrEntry(vPres, Abc_Lit2Var(pLits[i]));
        if ( Abc_InfoHasBit( pPres, iBit ) && 
             Abc_InfoHasBit( pInfo, iBit ) == Abc_LitIsCompl(pLits[i]) )
             return 0;
    }
    for ( i = 0; i < nLits; i++ )
    {
        pInfo = (unsigned *)Vec_PtrEntry(vInfo, Abc_Lit2Var(pLits[i]));
        pPres = (unsigned *)Vec_PtrEntry(vPres, Abc_Lit2Var(pLits[i]));
        Abc_InfoSetBit( pPres, iBit );
        if ( Abc_InfoHasBit( pInfo, iBit ) == Abc_LitIsCompl(pLits[i]) )
            Abc_InfoXorBit( pInfo, iBit );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs bitpacking of counter-examples.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManLoadCounterExamples( Vec_Ptr_t * vInfo, Vec_Int_t * vCexStore, int iStart )
{ 
    Vec_Int_t * vPat;
    Vec_Ptr_t * vPres;
    int nWords = Vec_PtrReadWordsSimInfo(vInfo);
    int nBits = 32 * nWords; 
    int k, nSize, kMax = 0;//, iBit = 1;
    vPat  = Vec_IntAlloc( 100 );
    vPres = Vec_PtrAllocSimInfo( Vec_PtrSize(vInfo), nWords );
    Vec_PtrCleanSimInfo( vPres, 0, nWords );
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        // skip the output number
        iStart++;
        // get the number of items
        nSize = Vec_IntEntry( vCexStore, iStart++ );
        if ( nSize <= 0 )
            continue;
        // extract pattern
        Vec_IntClear( vPat );
        for ( k = 0; k < nSize; k++ )
            Vec_IntPush( vPat, Vec_IntEntry( vCexStore, iStart++ ) );
        // add pattern to storage
        for ( k = 1; k < nBits; k++ )
            if ( Cec_ManLoadCounterExamplesTry( vInfo, vPres, k, (int *)Vec_IntArray(vPat), Vec_IntSize(vPat) ) )
                break;
        kMax = Abc_MaxInt( kMax, k );
        if ( k == nBits-1 )
            break;
    }
    Vec_PtrFree( vPres );
    Vec_IntFree( vPat );
    return iStart;
}

/**Function*************************************************************

  Synopsis    [Performs bitpacking of counter-examples.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManLoadCounterExamples2( Vec_Ptr_t * vInfo, Vec_Int_t * vCexStore, int iStart )
{ 
    unsigned * pInfo;
    int nBits = 32 * Vec_PtrReadWordsSimInfo(vInfo); 
    int k, iLit, nLits, Out, iBit = 1;
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        // skip the output number
//        iStart++;
        Out = Vec_IntEntry( vCexStore, iStart++ );
//        Abc_Print( 1, "iBit = %d. Out = %d.\n", iBit, Out );
        // get the number of items
        nLits = Vec_IntEntry( vCexStore, iStart++ );
        if ( nLits <= 0 )
            continue;
        // add pattern to storage
        for ( k = 0; k < nLits; k++ )
        {
            iLit = Vec_IntEntry( vCexStore, iStart++ );
            pInfo = (unsigned *)Vec_PtrEntry( vInfo, Abc_Lit2Var(iLit) );
            if ( Abc_InfoHasBit( pInfo, iBit ) == Abc_LitIsCompl(iLit) )
                Abc_InfoXorBit( pInfo, iBit );
        }
        if ( ++iBit == nBits )
            break;
    }
//    Abc_Print( 1, "added %d bits\n", iBit-1 );
    return iStart;
}

/**Function*************************************************************

  Synopsis    [Resimulates counter-examples derived by the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManResimulateCounterExamples( Cec_ManSim_t * pSim, Vec_Int_t * vCexStore, int nFrames )
{ 
    Vec_Int_t * vPairs;
    Vec_Ptr_t * vSimInfo; 
    int RetValue = 0, iStart = 0;
    vPairs = Gia_ManCorrCreateRemapping( pSim->pAig );
    Gia_ManCreateValueRefs( pSim->pAig );
//    pSim->pPars->nWords  = 63;
    pSim->pPars->nFrames = nFrames;
    vSimInfo = Vec_PtrAllocSimInfo( Gia_ManRegNum(pSim->pAig) + Gia_ManPiNum(pSim->pAig) * nFrames, pSim->pPars->nWords );
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        Cec_ManStartSimInfo( vSimInfo, Gia_ManRegNum(pSim->pAig) );
        iStart = Cec_ManLoadCounterExamples( vSimInfo, vCexStore, iStart );
//        iStart = Cec_ManLoadCounterExamples2( vSimInfo, vCexStore, iStart );
//        Gia_ManCorrRemapSimInfo( pSim->pAig, vSimInfo );
        Gia_ManCorrPerformRemapping( vPairs, vSimInfo );
        RetValue |= Cec_ManSeqResimulate( pSim, vSimInfo );
//        Cec_ManSeqResimulateInfo( pSim->pAig, vSimInfo, NULL );
    }
//Gia_ManEquivPrintOne( pSim->pAig, 85, 0 );
    assert( iStart == Vec_IntSize(vCexStore) );
    Vec_PtrFree( vSimInfo );
    Vec_IntFree( vPairs );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Resimulates counter-examples derived by the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManResimulateCounterExamplesComb( Cec_ManSim_t * pSim, Vec_Int_t * vCexStore )
{ 
    Vec_Ptr_t * vSimInfo; 
    int RetValue = 0, iStart = 0;
    Gia_ManCreateValueRefs( pSim->pAig );
    pSim->pPars->nFrames = 1;
    vSimInfo = Vec_PtrAllocSimInfo( Gia_ManCiNum(pSim->pAig), pSim->pPars->nWords );
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        Cec_ManStartSimInfo( vSimInfo, 0 );
        iStart = Cec_ManLoadCounterExamples( vSimInfo, vCexStore, iStart );
        RetValue |= Cec_ManSeqResimulate( pSim, vSimInfo );
    }
    assert( iStart == Vec_IntSize(vCexStore) );
    Vec_PtrFree( vSimInfo );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Checks whether two endpoints are still in the same class.]

  Description [Ring mode needs special handling for the closing edge
               tail -> head because Gia_ObjHasSameRepr() compares raw
               representatives and the head stores GIA_VOID.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_ManObjsStillMerged( Gia_Man_t * p, int iRepr, int iObj, int fRings )
{
    int iReprRoot, iObjRoot;
    if ( !fRings )
        return Gia_ObjHasSameRepr( p, iRepr, iObj );
    if ( iRepr == 0 )
        return Gia_ObjIsConst( p, iObj );
    if ( iObj == 0 )
        return Gia_ObjIsConst( p, iRepr );
    if ( !Gia_ObjIsClass( p, iRepr ) || !Gia_ObjIsClass( p, iObj ) )
        return 0;
    iReprRoot = Gia_ObjIsHead( p, iRepr ) ? iRepr : Gia_ObjRepr( p, iRepr );
    iObjRoot  = Gia_ObjIsHead( p, iObj  ) ? iObj  : Gia_ObjRepr( p, iObj  );
    return iReprRoot == iObjRoot && iReprRoot != GIA_VOID;
}

static int Cec_ManObjToSplit( Gia_Man_t * p, int iRepr, int iObj, int fRings )
{
    // For the ring closing edge (tail, head), split the tail. Splitting the
    // head is also correct, but it changes the representative of the whole
    // remaining class and creates a much larger incremental seed set.
    if ( fRings && iObj > 0 && Gia_ObjIsHead( p, iObj ) && Gia_ObjIsClass( p, iRepr ) )
        return iRepr;
    return iObj;
}

/**Function*************************************************************

  Synopsis    [Updates equivalence classes by marking those that timed out.]

  Description [Returns 1 if all nodes are proved.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCheckRefinements( Gia_Man_t * p, Vec_Str_t * vStatus, Vec_Int_t * vOutputs, Cec_ManSim_t * pSim, int fRings )
{
    int i, status, iRepr, iObj;
    int Counter = 0;
    assert( 2 * Vec_StrSize(vStatus) == Vec_IntSize(vOutputs) );
    Vec_StrForEachEntry( vStatus, status, i )
    {
        iRepr = Vec_IntEntry( vOutputs, 2*i );
        iObj  = Vec_IntEntry( vOutputs, 2*i+1 );
        if ( status == 1 )
            continue;
        if ( status == 0 )
        {
            // Match upstream ABC: do not force-split when SAT returns a CEX.
            // Cec_ManResimulateCounterExamples replays the CEX and refines the
            // class; only a contrived pattern-packing conflict could leave the
            // pair merged (each lit must collide at every one of the 32*nWords
            // packed slots). Forcing a split here is sound but perturbs the
            // BMC/refinement trajectory and was the cause of the
            // Problem05_label47/49 + token_ring incremental regression.
            if ( Cec_ManObjsStillMerged( p, iRepr, iObj, fRings ) )
                Counter++;
            continue;
        }
        if ( status == -1 )
        {
//            if ( !Gia_ObjFailed( p, iObj ) )
//                Abc_Print( 1, "Gia_ManCheckRefinements(): Failed equivalence is not marked as failed!\n" );
//            Gia_ObjSetFailed( p, iRepr );
//            Gia_ObjSetFailed( p, iObj );
//            if ( fRings )
//            Cec_ManSimClassRemoveOne( pSim, iRepr );
            Cec_ManSimClassRemoveOne( pSim, iObj );
            continue;
        }
    }
//    if ( Counter )
//    Abc_Print( 1, "Gia_ManCheckRefinements(): Could not refine %d nodes.\n", Counter );
    return 1;
}


/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCorrReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    Gia_Obj_t * pRepr;
    if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
    {
        Gia_ManCorrReduce_rec( pNew, p, pRepr );
        pObj->Value = Abc_LitNotCond( pRepr->Value, Gia_ObjPhaseReal(pRepr) ^ Gia_ObjPhaseReal(pObj) );
        return;
    }
    if ( ~pObj->Value )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManCorrReduce_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManCorrReduce_rec( pNew, p, Gia_ObjFanin1(pObj) );
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Reduces AIG using equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManCorrReduce( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManSetPhase( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManCorrReduce_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Prints statistics during solving.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManRefinedClassPrintStats( Gia_Man_t * p, Vec_Str_t * vStatus, int iIter, abctime Time )
{ 
    int nLits, CounterX = 0, Counter0 = 0, Counter = 0;
    int i, Entry, nProve = 0, nDispr = 0, nFail = 0;
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
    {
        if ( Gia_ObjIsNone(p, i) )
            CounterX++;
        else if ( Gia_ObjIsConst(p, i) )
            Counter0++;
        else if ( Gia_ObjIsHead(p, i) )
            Counter++;
    }
    CounterX -= Gia_ManCoNum(p);
    nLits = Gia_ManCiNum(p) + Gia_ManAndNum(p) - Counter - CounterX;
    if ( iIter == -1 )
        Abc_Print( 1, "BMC : " );
    else
        Abc_Print( 1, "%3d : ", iIter );
    Abc_Print( 1, "c =%8d  cl =%7d  lit =%8d  ", Counter0, Counter, nLits );
    if ( vStatus )
    Vec_StrForEachEntry( vStatus, Entry, i )
    {
        if ( Entry == 1 )
            nProve++;
        else if ( Entry == 0 )
            nDispr++;
        else if ( Entry == -1 )
            nFail++;
    }
    Abc_Print( 1, "p =%6d  d =%6d  f =%6d  ", nProve, nDispr, nFail );
    Abc_Print( 1, "%c  ", Gia_ObjIsConst( p, Gia_ObjFaninId0p(p, Gia_ManPo(p, 0)) ) ? '+' : '-' );
    Abc_PrintTime( 1, "T", Time );
}
int Cec_ManCountLits( Gia_Man_t * p )
{ 
    int i, CounterX = 0, Counter0 = 0, Counter = 0;
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
    {
        if ( Gia_ObjIsNone(p, i) )
            CounterX++;
        else if ( Gia_ObjIsConst(p, i) )
            Counter0++;
        else if ( Gia_ObjIsHead(p, i) )
            Counter++;
    }
    CounterX -= Gia_ManCoNum(p);
    return Gia_ManCiNum(p) + Gia_ManAndNum(p) - Counter - CounterX;
}

/**Function*************************************************************

  Synopsis    [Runs BMC for the equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManLSCorrespondenceBmc( Gia_Man_t * pAig, Cec_ParCor_t * pPars, int nPrefs )
{
    Cec_ParSim_t ParsSim, * pParsSim = &ParsSim;
    Cec_ParSat_t ParsSat, * pParsSat = &ParsSat;
    Vec_Str_t * vStatus;
    Vec_Int_t * vOutputs;
    Vec_Int_t * vCexStore;
    Cec_ManSim_t * pSim;
    Gia_Man_t * pSrm;
    int fChanges, RetValue, i;
    // BMC SRM is keyed only on pReprs (Gia_ManCorrSpecReduceInit ignores
    // its fRings flag).  So the incremental filter only needs pReprs-based
    // seeds; pNexts changes cannot affect this SRM and there are no ring
    // closing edges to reprove -- BMC is structurally simpler than the
    // main inductive loop.
    Cec_IncrMgr_t * pBmcMgr = NULL;
    // prepare simulation manager
    Cec_ManSimSetDefaultParams( pParsSim );
    pParsSim->nWords     = pPars->nWords;
    pParsSim->nFrames    = pPars->nRounds;
    pParsSim->fVerbose   = pPars->fVerbose;
    pParsSim->fLatchCorr = pPars->fLatchCorr;
    pParsSim->fSeqSimulate = 1;
    pSim = Cec_ManSimStart( pAig, pParsSim );
    // prepare SAT solving
    Cec_ManSatSetDefaultParams( pParsSat );
    pParsSat->nBTLimit = pPars->nBTLimit;
    pParsSat->fVerbose = pPars->fVerbose;
    if ( pPars->fIncremental )
    {
        // Use the deepest BMC unrolling depth so the TFO BFS covers every
        // frame the SRM emits.  In practice nPrefs is 0 and this matches
        // the main loop's depth, but be defensive in case of non-default
        // nPrefs callers.
        pBmcMgr = Cec_IncrMgrAlloc( pAig, pPars->nFrames + nPrefs );
        Cec_IncrMgrSnapshotClasses( pBmcMgr );
    }
    fChanges = 1;
    for ( i = 0; fChanges && (!pPars->nLimitMax || i < pPars->nLimitMax); i++ )
    {
        int * pTfoMask = NULL;
        int nReprSeeds = 0, nTotalPairs = 0, nActivePairs = 0;
        if ( Cec_ParCorShouldStop( pPars ) )
            break;
        abctime clkBmc = Abc_Clock();
        fChanges = 0;
        // Decide whether to apply incremental TFO mask this iteration.
        // Skip on i==0 because the first full BMC SRM establishes the cache.
        if ( pBmcMgr && i > 0 )
        {
            nReprSeeds = Cec_IncrMgrComputeSeeds( pBmcMgr );
            if ( nReprSeeds == 0 )
            {
                // No pReprs change since last SRM proved its pairs --
                // BMC SRM topology is unchanged so no useful new SAT
                // work; treat as convergence.
                break;
            }
            Cec_IncrMgrComputeTfo( pBmcMgr );
            // BMC SRM is non-ring; pass fRings=0 so we count (head, member)
            // pairs only and skip any ring-edge bookkeeping.
            Cec_IncrMgrCountActivePairs( pBmcMgr, 0, pBmcMgr->pTfoMark, &nTotalPairs, &nActivePairs );
            if ( nActivePairs == 0 )
                break;
            // Same fallback heuristic as the main loop: above ~70% active,
            // the mask plus emission filter costs more than just rebuilding
            // the full SRM.
            if ( !( nTotalPairs > 0 && (ABC_INT64_T)10 * nActivePairs > (ABC_INT64_T)7 * nTotalPairs ) )
                pTfoMask = pBmcMgr->pTfoMark;
        }
        if ( pTfoMask )
            pSrm = Gia_ManCorrSpecReduceInit_Active( pAig, pPars->nFrames, nPrefs, !pPars->fLatchCorr, &vOutputs, pTfoMask );
        else
            pSrm = Gia_ManCorrSpecReduceInit( pAig, pPars->nFrames, nPrefs, !pPars->fLatchCorr, &vOutputs, pPars->fUseRings );
        if ( pTfoMask && pPars->fVeryVerbose )
            Abc_Print( 1, "  [bmc-incr i=%d repr=%d active=%d/%d POs=%d]\n",
                       i, nReprSeeds, nActivePairs, nTotalPairs, Gia_ManCoNum(pSrm) );
        // Snapshot after SRM construction, before SAT/refine: this is the
        // class state whose pairs were just emitted.  The next iteration's
        // diff vs this snapshot tells us which pairs are stale.
        if ( pBmcMgr )
            Cec_IncrMgrSnapshotClasses( pBmcMgr );
        if ( Gia_ManPoNum(pSrm) == 0 )
        {
            Gia_ManStop( pSrm );
            Vec_IntFree( vOutputs );
            break;
        }
        pParsSat->nBTLimit *= 10;
        if ( pPars->fUseCSat )
            vCexStore = Tas_ManSolveMiterNc( pSrm, pPars->nBTLimit, &vStatus, 0 );
        else
            vCexStore = Cec_ManSatSolveMiter( pSrm, pParsSat, &vStatus );
        // refine classes with these counter-examples
        if ( Vec_IntSize(vCexStore) )
        {
            RetValue = Cec_ManResimulateCounterExamples( pSim, vCexStore, pPars->nFrames + 1 + nPrefs );
            Gia_ManCheckRefinements( pAig, vStatus, vOutputs, pSim, pPars->fUseRings );
            fChanges = 1;
        }
        if ( pPars->fVerbose )
            Cec_ManRefinedClassPrintStats( pAig, vStatus, -1, Abc_Clock() - clkBmc );
        // recycle
        Vec_IntFree( vCexStore );
        Vec_StrFree( vStatus );
        Gia_ManStop( pSrm );
        Vec_IntFree( vOutputs );
        if ( Cec_ParCorShouldStop( pPars ) )
            break;
    }
    Cec_IncrMgrFree( pBmcMgr );
    Cec_ManSimStop( pSim );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManLSCorrAnalyzeDependence( Gia_Man_t * p, Vec_Int_t * vEquivs, Vec_Str_t * vStatus )
{
    Gia_Obj_t * pObj, * pObjRo;
    int i, Iter, iObj, iRepr, fPrev, Total, Count0, Count1;
    assert( Vec_StrSize(vStatus) * 2 == Vec_IntSize(vEquivs) );
    Total = 0;
    Gia_ManForEachObj( p, pObj, i )
    {
        assert( pObj->fMark1 == 0 );
        if ( Gia_ObjHasRepr(p, i) )
            Total++;
    }
    Count0 = 0;
    for ( i = 0; i < Vec_StrSize(vStatus); i++ )
    {
        iRepr = Vec_IntEntry(vEquivs, 2*i);
        iObj = Vec_IntEntry(vEquivs, 2*i+1);
        assert( iRepr == Gia_ObjRepr(p, iObj) );
        if ( Vec_StrEntry(vStatus, i) != 1 ) // disproved or undecided
        {
            Gia_ManObj(p, iObj)->fMark1 = 1;
            Count0++;
        }
    }
    for ( Iter = 0; Iter < 100; Iter++ )
    {
        int fChanges = 0;
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( Gia_ObjIsCi(pObj) )
                continue;
            assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) );
//            fPrev = pObj->fMark1;
            if ( Gia_ObjIsAnd(pObj) )
                pObj->fMark1 |= Gia_ObjFanin0(pObj)->fMark1 | Gia_ObjFanin1(pObj)->fMark1;
            else
                pObj->fMark1 |= Gia_ObjFanin0(pObj)->fMark1;
//            fChanges += fPrev ^ pObj->fMark1;
        }
        Gia_ManForEachRiRo( p, pObj, pObjRo, i )
        {
            fPrev = pObjRo->fMark1;
            pObjRo->fMark1 = pObj->fMark1;
            fChanges += fPrev ^ pObjRo->fMark1;
        }
        if ( fChanges == 0 )
            break;
    }
    Count1 = 0;
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( pObj->fMark1 && Gia_ObjHasRepr(p, i) )
            Count1++;
        pObj->fMark1 = 0;
    }
    printf( "%5d -> %5d (%3d)  ", Count0, Count1, Iter );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Internal procedure for register correspondence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManLSCorrespondenceClasses( Gia_Man_t * pAig, Cec_ParCor_t * pPars )
{  
    int nIterMax     = 100000;
    int nAddFrames   = 1; // additional timeframes to simulate
    int fRunBmcFirst = 1;
    Vec_Str_t * vStatus;
    Vec_Int_t * vOutputs;
    Vec_Int_t * vCexStore;
    Cec_ParSim_t ParsSim, * pParsSim = &ParsSim;
    Cec_ParSat_t ParsSat, * pParsSat = &ParsSat;
    Cec_ManSim_t * pSim;
    Gia_Man_t * pSrm;
    int r, RetValue, nPrev[4] = {0};
    abctime clkTotal = Abc_Clock();
    abctime clkSat = 0, clkSim = 0, clkSrm = 0;
    abctime clk2, clk = Abc_Clock();
    // Incremental active-list manager (NULL if -i not set)
    Cec_IncrMgr_t * pMgr = NULL;
    abctime clkIncr = 0;
    int nIncrSkipped = 0, nIncrFallback = 0;
    if ( Gia_ManRegNum(pAig) == 0 )
    {
        Abc_Print( 1, "Cec_ManLatchCorrespondence(): Not a sequential AIG.\n" );
        return 0;
    }
    Gia_ManRandom( 1 );
    // prepare simulation manager
    Cec_ManSimSetDefaultParams( pParsSim );
    pParsSim->nWords     = pPars->nWords;
    pParsSim->nFrames    = pPars->nFrames;
    pParsSim->fVerbose   = pPars->fVerbose;
    pParsSim->fLatchCorr = pPars->fLatchCorr;
    pParsSim->fConstCorr = pPars->fConstCorr;
    pParsSim->fSeqSimulate = 1;
    // create equivalence classes of registers
    pSim = Cec_ManSimStart( pAig, pParsSim );
    if ( pAig->pReprs == NULL )
    {
        Cec_ManSimClassesPrepare( pSim, pPars->nLevelMax );
        Cec_ManSimClassesRefine( pSim );
    }
    // prepare SAT solving
    Cec_ManSatSetDefaultParams( pParsSat );
    pParsSat->nBTLimit = pPars->nBTLimit;
    pParsSat->fVerbose = pPars->fVerbose;
    // limit the number of conflicts in the circuit-based solver
    if ( pPars->fUseCSat )
        pParsSat->nBTLimit = Abc_MinInt( pParsSat->nBTLimit, 1000 );
    if ( pPars->fVerbose )
    {
        Abc_Print( 1, "Obj = %7d. And = %7d. Conf = %5d. Fr = %d. Lcorr = %d. Ring = %d. CSat = %d.\n",
            Gia_ManObjNum(pAig), Gia_ManAndNum(pAig), 
            pPars->nBTLimit, pPars->nFrames, pPars->fLatchCorr, pPars->fUseRings, pPars->fUseCSat );
        Cec_ManRefinedClassPrintStats( pAig, NULL, 0, Abc_Clock() - clk );
    }
    // check the base case
    if ( fRunBmcFirst && (!pPars->fLatchCorr || pPars->nFrames > 1) )
        Cec_ManLSCorrespondenceBmc( pAig, pPars, 0 );
    if ( Cec_ParCorShouldStop( pPars ) )
    {
        Cec_ManSimStop( pSim );
        return 1;
    }
    if ( pPars->nStepsMax == 0 )
    {
        Abc_Print( 1, "Stopped signal correspondence after BMC.\n" );
        Cec_ManSimStop( pSim );
        return 1;
    }
    // Initialise incremental manager (after BMC, before main refinement loop).
    // Works with both SAT and CBS solver paths: the active-list filter just
    // reduces the number of POs in the SRM, and both solvers iterate POs.
    if ( pPars->fIncremental )
    {
        pMgr = Cec_IncrMgrAlloc( pAig, pPars->nFrames );
        Cec_IncrMgrSnapshotClasses( pMgr );  // initial snapshot (post-BMC classes)
    }
    // perform refinement of equivalence classes
    for ( r = 0; r < nIterMax; r++ )
    {
        if ( Cec_ParCorShouldStop( pPars ) )
        {
            Cec_ManSimStop( pSim );
            Cec_IncrMgrFree( pMgr );
            return 1;
        }
        if ( pPars->nStepsMax == r )
        {
            Cec_ManSimStop( pSim );
            Cec_IncrMgrFree( pMgr );
            Abc_Print( 1, "Stopped signal correspondence after %d refiment iterations.\n", r );
            return 1;
        }
        clk = Abc_Clock();
        // perform speculative reduction (with optional active-list filter)
        clk2 = Abc_Clock();
        {
            int * pTfoMask = NULL;
            int nReprSeeds = 0, nNextChanges = 0;
            int nTotalPairs = 0, nActivePairs = 0;
            // Decide whether to apply incremental TFO mask this iteration.
            // Skip on r==0 because the first full SRM establishes the cache.
            if ( pMgr && r > 0 )
            {
                abctime clkI = Abc_Clock();
                nReprSeeds = Cec_IncrMgrComputeSeeds( pMgr );
                nNextChanges = pPars->fUseRings ? Cec_IncrMgrCountNextChanges( pMgr ) : 0;
                if ( nReprSeeds == 0 && nNextChanges == 0 )
                {
                    // No class-state change since the full/active SRM just
                    // proved these pairs; this is true convergence.
                    clkIncr += Abc_Clock() - clkI;
                    clkSrm  += Abc_Clock() - clk2;
                    break;
                }
                Cec_IncrMgrComputeTfo( pMgr );
                Cec_IncrMgrCountActivePairs( pMgr, pPars->fUseRings, pMgr->pTfoMark, &nTotalPairs, &nActivePairs );
                if ( nActivePairs == 0 )
                {
                    // Classes changed, but no remaining candidate pair depends
                    // on the changed reprs and no new ring edge needs proving.
                    clkIncr += Abc_Clock() - clkI;
                    clkSrm  += Abc_Clock() - clk2;
                    break;
                }
                // Fallback is based on emitted candidate pairs, not seed count.
                // A large pNexts-only ring rewiring may have many changed slots
                // but only a few new edges; conversely a tiny seed can fan out
                // to almost all pairs. Above ~70% active pairs, the full SRM is
                // usually cheaper than filtering plus bookkeeping.
                if ( nTotalPairs > 0 && (ABC_INT64_T)10 * nActivePairs > (ABC_INT64_T)7 * nTotalPairs )
                {
                    nIncrFallback++;
                }
                else
                {
                    pTfoMask = pMgr->pTfoMark;
                    nIncrSkipped += nTotalPairs - nActivePairs;
                }
                clkIncr += Abc_Clock() - clkI;
            }

            if ( pTfoMask )
                pSrm = Gia_ManCorrSpecReduce_Active( pAig, pPars->nFrames, !pPars->fLatchCorr, &vOutputs, pPars->fUseRings, pTfoMask, pMgr );
            else
                pSrm = Gia_ManCorrSpecReduce( pAig, pPars->nFrames, !pPars->fLatchCorr, &vOutputs, pPars->fUseRings );
            if ( pTfoMask && pPars->fVeryVerbose )
                Abc_Print( 1, "  [incr r=%d repr=%d next=%d tfo=%d active=%d/%d POs=%d]\n",
                           r, nReprSeeds, nNextChanges, Vec_IntSize(pMgr->vTfoNodes),
                           nActivePairs, nTotalPairs,
                           Gia_ManCoNum(pSrm) );
            // Snapshot after SRM construction: the active builder still needs
            // the old pNexts snapshot to recognize newly-created ring edges.
            // SAT/sim refinement below is what creates the next iteration's diff.
            if ( pMgr )
                Cec_IncrMgrSnapshotClasses( pMgr );
        }
        assert( Gia_ManRegNum(pSrm) == 0 && Gia_ManPiNum(pSrm) == Gia_ManRegNum(pAig)+(pPars->nFrames+!pPars->fLatchCorr)*Gia_ManPiNum(pAig) );
        clkSrm += Abc_Clock() - clk2;
        if ( Gia_ManCoNum(pSrm) == 0 )
        {
            Vec_IntFree( vOutputs );
            Gia_ManStop( pSrm );            
            break;
        }
//Gia_DumpAiger( pSrm, "corrsrm", r, 2 );
        // found counter-examples to speculation
        clk2 = Abc_Clock();
        if ( pPars->fUseCSat )
            vCexStore = Cbs_ManSolveMiterNc( pSrm, pPars->nBTLimit, &vStatus, 0, 0 );
        else
            vCexStore = Cec_ManSatSolveMiter( pSrm, pParsSat, &vStatus );
        Gia_ManStop( pSrm );
        clkSat += Abc_Clock() - clk2;
        if ( Vec_IntSize(vCexStore) == 0 )
        {
            Vec_IntFree( vCexStore );
            Vec_StrFree( vStatus );
            Vec_IntFree( vOutputs );
            break;
        }
//        Cec_ManLSCorrAnalyzeDependence( pAig, vOutputs, vStatus );        

        // refine classes with these counter-examples
        clk2 = Abc_Clock();
        RetValue = Cec_ManResimulateCounterExamples( pSim, vCexStore, pPars->nFrames + 1 + nAddFrames );
        Vec_IntFree( vCexStore );
        clkSim += Abc_Clock() - clk2;
        Gia_ManCheckRefinements( pAig, vStatus, vOutputs, pSim, pPars->fUseRings );
        if ( pPars->fVerbose )
            Cec_ManRefinedClassPrintStats( pAig, vStatus, r+1, Abc_Clock() - clk );
        Vec_StrFree( vStatus );
        Vec_IntFree( vOutputs );
//Gia_ManEquivPrintClasses( pAig, 1, 0 );
        if ( Cec_ParCorShouldStop( pPars ) )
        {
            Cec_ManSimStop( pSim );
            Cec_IncrMgrFree( pMgr );
            return 1;
        }
        // quit if const is no longer there
        if ( pPars->fStopWhenGone && Gia_ManPoNum(pAig) == 1 && !Gia_ObjIsConst( pAig, Gia_ObjFaninId0p(pAig, Gia_ManPo(pAig, 0)) ) )
        {
            printf( "Iterative refinement is stopped after iteration %d\n", r );
            printf( "because the property output is no longer a candidate constant.\n" );
            Cec_ManSimStop( pSim );
            Cec_IncrMgrFree( pMgr );
            return 0;
        }
        if ( pPars->nLimitMax )
        {
            int nCur = Cec_ManCountLits(pAig);
            if ( r > 4 && nPrev[0] - nCur <= 4*pPars->nLimitMax )
            {
                printf( "Iterative refinement is stopped after iteration %d\n", r );
                printf( "because refinement does not proceed quickly.\n" );
                Cec_ManSimStop( pSim );
                Cec_IncrMgrFree( pMgr );
                ABC_FREE( pAig->pReprs );
                ABC_FREE( pAig->pNexts );
                return 0;
            }
            nPrev[0] = nPrev[1];
            nPrev[1] = nPrev[2];
            nPrev[2] = nPrev[3];
            nPrev[3] = nCur;
        }
    }
    if ( pPars->fVerbose )
        Cec_ManRefinedClassPrintStats( pAig, NULL, r+1, Abc_Clock() - clk );
    // check the overflow
    if ( r == nIterMax )
        Abc_Print( 1, "The refinement was not finished. The result may be incorrect.\n" );
    Cec_ManSimStop( pSim );
    // check the base case
    if ( !fRunBmcFirst && (!pPars->fLatchCorr || pPars->nFrames > 1) )
        Cec_ManLSCorrespondenceBmc( pAig, pPars, 0 );
    clkTotal = Abc_Clock() - clkTotal;
    // report the results
    if ( pPars->fVerbose )
    {
        ABC_PRTP( "Srm  ", clkSrm,                        clkTotal );
        ABC_PRTP( "Sat  ", clkSat,                        clkTotal );
        ABC_PRTP( "Sim  ", clkSim,                        clkTotal );
        ABC_PRTP( "Other", clkTotal-clkSat-clkSrm-clkSim, clkTotal );
        if ( pMgr )
        {
            ABC_PRTP( "Incr ", clkIncr, clkTotal );
            Abc_Print( 1, "Incr: fallback rounds = %d, skipped candidate pairs = %d\n", nIncrFallback, nIncrSkipped );
        }
        Abc_PrintTime( 1, "TOTAL",  clkTotal );
    }
    Cec_IncrMgrFree( pMgr );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes new initial state.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Cec_ManComputeInitState( Gia_Man_t * pAig, int nFrames )
{  
    Gia_Obj_t * pObj, * pObjRo, * pObjRi;
    unsigned * pInitState;
    int i, f; 
    Gia_ManRandom( 1 );
//    Abc_Print( 1, "Simulating %d timeframes.\n", nFrames );
    Gia_ManForEachRo( pAig, pObj, i )
        pObj->fMark1 = 0;
    for ( f = 0; f < nFrames; f++ )
    {
        Gia_ManConst0(pAig)->fMark1 = 0;
        Gia_ManForEachPi( pAig, pObj, i )
            pObj->fMark1 = Gia_ManRandom(0) & 1;
        Gia_ManForEachAnd( pAig, pObj, i )
            pObj->fMark1 = (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) & 
                (Gia_ObjFanin1(pObj)->fMark1 ^ Gia_ObjFaninC1(pObj));
        Gia_ManForEachRi( pAig, pObj, i )
            pObj->fMark1 = (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj));
        Gia_ManForEachRiRo( pAig, pObjRi, pObjRo, i )
            pObjRo->fMark1 = pObjRi->fMark1;
    }
    pInitState = ABC_CALLOC( unsigned, Abc_BitWordNum(Gia_ManRegNum(pAig)) );
    Gia_ManForEachRo( pAig, pObj, i )
    {
        if ( pObj->fMark1 )
            Abc_InfoSetBit( pInitState, i );
//        Abc_Print( 1, "%d", pObj->fMark1 );
    }
//    Abc_Print( 1, "\n" );
    Gia_ManCleanMark1( pAig );
    return pInitState;
}

/**Function*************************************************************

  Synopsis    [Prints flop equivalences.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManPrintFlopEquivs( Gia_Man_t * p )
{
    Gia_Obj_t * pObj, * pRepr;
    int i;
    assert( p->vNamesIn != NULL );
    Gia_ManForEachRo( p, pObj, i )
    {
        if ( Gia_ObjIsConst(p, Gia_ObjId(p, pObj)) )
            Abc_Print( 1, "Original flop %s is proved equivalent to constant.\n", Vec_PtrEntry(p->vNamesIn, Gia_ObjCioId(pObj)) );
        else if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
        {
            if ( Gia_ObjIsCi(pRepr) )
                Abc_Print( 1, "Original flop %s is proved equivalent to flop %s.\n",
                    Vec_PtrEntry( p->vNamesIn, Gia_ObjCioId(pObj)  ),
                    Vec_PtrEntry( p->vNamesIn, Gia_ObjCioId(pRepr) ) );
            else
                Abc_Print( 1, "Original flop %s is proved equivalent to internal node %d.\n",
                    Vec_PtrEntry( p->vNamesIn, Gia_ObjCioId(pObj) ), Gia_ObjId(p, pRepr) );
        }
    }
}


/**Function*************************************************************

  Synopsis    [Top-level procedure for register correspondence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManLSCorrespondence( Gia_Man_t * pAig, Cec_ParCor_t * pPars )
{  
    Gia_Man_t * pNew, * pTemp;
    unsigned * pInitState;
    int RetValue;
    ABC_FREE( pAig->pReprs );
    ABC_FREE( pAig->pNexts );
    if ( pPars->nPrefix == 0 )
    {
        RetValue = Cec_ManLSCorrespondenceClasses( pAig, pPars );
        if ( RetValue == 0 )
            return Gia_ManDup( pAig );
    }
    else
    {
        // compute the cycles AIG
        pInitState = Cec_ManComputeInitState( pAig, pPars->nPrefix );
        pTemp = Gia_ManDupFlip( pAig, (int *)pInitState );
        ABC_FREE( pInitState );
        // compute classes of this AIG
        RetValue = Cec_ManLSCorrespondenceClasses( pTemp, pPars );
        // transfer the class info
        pAig->pReprs = pTemp->pReprs; pTemp->pReprs = NULL;
        pAig->pNexts = pTemp->pNexts; pTemp->pNexts = NULL;
        // perform additional BMC
        pPars->fUseCSat = 0;
        pPars->nBTLimit = Abc_MaxInt( pPars->nBTLimit, 1000 );
        Cec_ManLSCorrespondenceBmc( pAig, pPars, pPars->nPrefix );
/*
        // transfer the class info back
        pTemp->pReprs = pAig->pReprs; pAig->pReprs = NULL;
        pTemp->pNexts = pAig->pNexts; pAig->pNexts = NULL;
        // continue refining
        RetValue = Cec_ManLSCorrespondenceClasses( pTemp, pPars );
        // transfer the class info
        pAig->pReprs = pTemp->pReprs; pTemp->pReprs = NULL;
        pAig->pNexts = pTemp->pNexts; pTemp->pNexts = NULL;
*/
        Gia_ManStop( pTemp );
    }
    // derive reduced AIG
    if ( pPars->fMakeChoices )
    {
        pNew = Gia_ManEquivToChoices( pAig, 1 );
//        Gia_ManHasChoices_very_old( pNew );
    }
    else
    {
//        Gia_ManEquivImprove( pAig );
        pNew = Gia_ManCorrReduce( pAig );
        pNew = Gia_ManSeqCleanup( pTemp = pNew );
        Gia_ManStop( pTemp );
        //Gia_AigerWrite( pNew, "reduced.aig", 0, 0, 0 );
    }
    // report the results
    if ( pPars->fVerbose )
    {
        Abc_Print( 1, "NBeg = %d. NEnd = %d. (Gain = %6.2f %%).  RBeg = %d. REnd = %d. (Gain = %6.2f %%).\n", 
            Gia_ManAndNum(pAig), Gia_ManAndNum(pNew), 
            100.0*(Gia_ManAndNum(pAig)-Gia_ManAndNum(pNew))/(Gia_ManAndNum(pAig)?Gia_ManAndNum(pAig):1), 
            Gia_ManRegNum(pAig), Gia_ManRegNum(pNew), 
            100.0*(Gia_ManRegNum(pAig)-Gia_ManRegNum(pNew))/(Gia_ManRegNum(pAig)?Gia_ManRegNum(pAig):1) );
    }
    if ( pPars->nPrefix && (Gia_ManAndNum(pNew) < Gia_ManAndNum(pAig) || Gia_ManRegNum(pNew) < Gia_ManRegNum(pAig)) )
        Abc_Print( 1, "The reduced AIG was produced using %d-th invariants and will not verify.\n", pPars->nPrefix );
    // print verbose info about equivalences
    if ( pPars->fVerboseFlops )
    {
        if ( pAig->vNamesIn == NULL )
            Abc_Print( 1, "Flop output names are not available. Use command \"&get -n\".\n" );
        else
            Cec_ManPrintFlopEquivs( pAig );
    }
    // copy names if present
    if ( pAig->vNamesIn )
    {
        char * pName; int i;
        pNew->vNamesIn = Vec_PtrDupStr( pAig->vNamesIn );
        Vec_PtrForEachEntryStart( char *, pNew->vNamesIn, pName, i, Gia_ManCiNum(pNew) )
            ABC_FREE( pName );
        Vec_PtrShrink( pNew->vNamesIn, Gia_ManCiNum(pNew) );
    }
    if ( pAig->vNamesOut )
    {
        char * pName; int i;
        pNew->vNamesOut = Vec_PtrDupStr( pAig->vNamesOut );
        Vec_PtrForEachEntryStart( char *, pNew->vNamesOut, pName, i, Gia_ManCoNum(pNew) )
            ABC_FREE( pName );
        Vec_PtrShrink( pNew->vNamesOut, Gia_ManCoNum(pNew) );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wec_t * Gia_ManCreateRegSupps( Gia_Man_t * p, int fVerbose )
{
    abctime clk = Abc_Clock();
    Gia_Obj_t * pObj; int i, Id;
    Vec_Wec_t * vSuppsR = Vec_WecStart( Gia_ManRegNum(p) );
    Vec_Wec_t * vSupps  = Vec_WecStart( Gia_ManObjNum(p) );
    Gia_ManForEachRo( p, pObj, i )
        Vec_IntPush( Vec_WecEntry(vSupps, Gia_ObjId(p, pObj)), i );
    Gia_ManForEachAnd( p, pObj, Id )
        Vec_IntTwoMerge2( Vec_WecEntry(vSupps, Gia_ObjFaninId0(pObj, Id)), 
                          Vec_WecEntry(vSupps, Gia_ObjFaninId1(pObj, Id)), 
                          Vec_WecEntry(vSupps, Id) ); 
    Gia_ManForEachRi( p, pObj, i )
        Vec_IntAppend( Vec_WecEntry(vSuppsR, i), Vec_WecEntry(vSupps, Gia_ObjFaninId0p(p, pObj)) );
    Vec_WecFree( vSupps );
    if ( fVerbose )
        Abc_PrintTime( 1, "Support computation", Abc_Clock() - clk );
    return vSuppsR;
}
Vec_Int_t * Gia_ManFindStopFlops( Gia_Man_t * p, int nFlopIncFreq, int fVerbose )
{
    Vec_Int_t * vRes = NULL, * vTemp;  int i, k, Spot, Temp, nItems = 0;
    Vec_Wec_t * vSupps = Gia_ManCreateRegSupps( p, fVerbose );
    Vec_Int_t * vNexts = Vec_IntStartFull( Gia_ManRegNum(p) );
    Vec_Int_t * vAvail = Vec_IntStart( Gia_ManRegNum(p) );
    Vec_Int_t * vHeads = Vec_IntAlloc( 10 );
    Vec_WecForEachLevel( vSupps, vTemp, i ) {
        if ( Vec_IntSize(vTemp) > 2 )
            continue;
        if ( (Spot = Vec_IntFind(vTemp, i)) >= 0 )
            Vec_IntDrop( vTemp, Spot );
        if ( Vec_IntSize(vTemp) != 1 )
            continue;
        Vec_IntWriteEntry( vNexts, i, Vec_IntEntry(vTemp, 0) );
        Vec_IntWriteEntry( vAvail, Vec_IntEntry(vTemp, 0), 1 );
    }
    Vec_IntForEachEntry( vNexts, Spot, i )
        if ( Spot >= 0 && Vec_IntEntry(vAvail, i) == 0 )
            Vec_IntPush( vHeads, i );
    Vec_IntForEachEntry( vHeads, Spot, i ) {
        Gia_ManIncrementTravId( p );
        for ( k = 0, Temp = Spot; Vec_IntEntry(vNexts, Temp) >= 0; k++, Temp = Vec_IntEntry(vNexts, Temp) ) {
            if ( Gia_ObjUpdateTravIdCurrentId(p, Temp) )
                break;
            Vec_IntWriteEntry( vAvail, Temp, 1 );
        }
        if ( k > 100 )
        {
            nItems++;
            if ( vRes == NULL ) 
                vRes = Vec_IntAlloc( 100 );
            Gia_ManIncrementTravId( p );
            for ( k = 0, Temp = Spot; Vec_IntEntry(vNexts, Temp) >= 0; k++, Temp = Vec_IntEntry(vNexts, Temp) ) {
                if ( Gia_ObjUpdateTravIdCurrentId(p, Temp) )
                    break;            
                if ( k % nFlopIncFreq == 0 )
                    Vec_IntPush( vRes, Temp );
            }
        }
        while ( Vec_IntEntry(vNexts, Spot) >= 0 )
        {
            int Next = Vec_IntEntry(vNexts, Spot);
            Vec_IntWriteEntry( vNexts, Spot, -1 );
            Spot = Next;
        }
    }
    if ( fVerbose && vRes ) 
        printf( "Detected %d sequence%s containing %d flops.\n", nItems, nItems > 1 ? "s":"", Vec_IntSize(vRes) );
    Vec_IntFree( vNexts );
    Vec_IntFree( vAvail );
    Vec_IntFree( vHeads );
    Vec_WecFree( vSupps );
    return vRes;
}
Gia_Man_t * Gia_ManDupStopsAdd( Gia_Man_t * p, Vec_Int_t * vStops )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj; int i, Stop;
    Vec_Int_t * vExtras = Vec_IntAlloc( Vec_IntSize(vStops) );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachPi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Vec_IntForEachEntry( vStops, Stop, i )
        Vec_IntPush( vExtras, Gia_ManAppendCi(pNew) );
    Gia_ManForEachRo( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Vec_IntForEachEntry( vStops, Stop, i ) 
    {
        int Lit = Gia_ManCi(p, Gia_ManPiNum(p)+Stop)->Value;
        Gia_ManCi(p, Gia_ManPiNum(p)+Stop)->Value = Vec_IntEntry(vExtras, i);
        Vec_IntWriteEntry( vExtras, i, Lit );
    }
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachPo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Vec_IntForEachEntry( vExtras, Stop, i )
        Gia_ManAppendCo( pNew, Stop );
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Vec_IntFree( vExtras );
    return pNew;
}
void Gia_ManDupStopsRem_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( ~pObj->Value )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManDupStopsRem_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManDupStopsRem_rec( pNew, p, Gia_ObjFanin1(pObj) );
    pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}
Gia_Man_t * Gia_ManDupStopsRem( Gia_Man_t * p, Vec_Int_t * vStops )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj; int i;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachPi( p, pObj, i )
        if ( i < Gia_ManPiNum(p) - Vec_IntSize(vStops) )
            pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachRo( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachPo( p, pObj, i )
        if ( i >= Gia_ManPoNum(p) - Vec_IntSize(vStops) )
            Gia_ManDupStopsRem_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachPi( p, pObj, i )
        if ( i >= Gia_ManPiNum(p) - Vec_IntSize(vStops) )
            pObj->Value = Gia_ObjFanin0Copy( Gia_ManPo(p, i - Gia_ManPiNum(p) + Gia_ManPoNum(p)) );
    Gia_ManForEachPo( p, pObj, i )
        if ( i < Gia_ManPoNum(p) - Vec_IntSize(vStops) )
            Gia_ManDupStopsRem_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManDupStopsRem_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachPo( p, pObj, i )
        if ( i < Gia_ManPoNum(p) - Vec_IntSize(vStops) )
            Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}
Gia_Man_t * Gia_ManDupStopsTest( Gia_Man_t * p )
{
    Vec_Int_t * vStops = Gia_ManFindStopFlops( p, 1, 1 );
    if ( vStops == NULL )
        return Gia_ManDup(p);
    Gia_Man_t * pNew1 = Gia_ManDupStopsAdd( p, vStops );
    Gia_Man_t * pNew2 = Gia_ManDupStopsRem( pNew1, vStops );
    Gia_ManStop( pNew1 );    
    Vec_IntFree( vStops );
    return pNew2;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
