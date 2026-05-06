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

#define CEC_OR_BATCH_SIZE_DEFAULT      16
#define CEC_OR_BATCH_UNSAT_RATE_MIN    0.95
#define CEC_OR_BATCH_HARD_SCORE_MAX    7
#define CEC_OR_BATCH_HARD_THRESHOLD    2
#define CEC_OR_BATCH_HARD_PENALTY      2
#define CEC_OR_BATCH_WIN_SIZE          8
#define CEC_OR_BATCH_WIN_MIN_ROUNDS    2
#define CEC_OR_BATCH_WIN_RATE_MIN      0.25
#define CEC_OR_BATCH_BACKOFF_ROUNDS    4

static Vec_Int_t * Cec_ManSolveMiterWithSolver( Gia_Man_t * pSrm, Cec_ParSat_t * pParsSat, Vec_Str_t ** pvStatus,
                                                int fUseCSat )
{
    if ( fUseCSat )
        return Cbs_ManSolveMiterNc( pSrm, pParsSat->nBTLimit, pvStatus, 0, 0 );
    return Cec_ManSatSolveMiter( pSrm, pParsSat, pvStatus );
}

static void Cec_ManStatusCount( Vec_Str_t * vStatus, int * pnProved, int * pnDisproved, int * pnFailed )
{
    int i, Entry;
    *pnProved = *pnDisproved = *pnFailed = 0;
    Vec_StrForEachEntry( vStatus, Entry, i )
    {
        if ( Entry == 1 )
            (*pnProved)++;
        else if ( Entry == 0 )
            (*pnDisproved)++;
        else
            (*pnFailed)++;
    }
}

static void Cec_ManCorrUpdateHardScores( Gia_Man_t * p, unsigned char * pScores, Vec_Int_t * vOutputs,
                                         Vec_Str_t * vStatus, int * pnHardActive, int * pnHardPromoted )
{
    int i, k, Status, iObj, nHardActive = 0, nHardPromoted = 0;
    if ( pScores == NULL )
        return;
    assert( 2 * Vec_StrSize(vStatus) == Vec_IntSize(vOutputs) );
    Vec_StrForEachEntry( vStatus, Status, i )
    {
        int Old, New;
        iObj = Vec_IntEntry( vOutputs, 2*i + 1 );
        Old = pScores[iObj];
        if ( Status == -1 )
            New = Abc_MinInt( CEC_OR_BATCH_HARD_SCORE_MAX, Old + CEC_OR_BATCH_HARD_PENALTY );
        else
            New = Abc_MaxInt( 0, Old - 1 );
        pScores[iObj] = (unsigned char)New;
        if ( Old < CEC_OR_BATCH_HARD_THRESHOLD && New >= CEC_OR_BATCH_HARD_THRESHOLD )
            nHardPromoted++;
    }
    for ( k = 0; k < Gia_ManObjNum(p); k++ )
        nHardActive += pScores[k] >= CEC_OR_BATCH_HARD_THRESHOLD;
    if ( pnHardActive )
        *pnHardActive = nHardActive;
    if ( pnHardPromoted )
        *pnHardPromoted = nHardPromoted;
}

static int * Cec_ManCorrBuildHardMark( unsigned char * pScores, int nObjs, int * pnHard )
{
    int * pMark = NULL;
    int i, nHard = 0;
    if ( pScores == NULL )
        return NULL;
    for ( i = 0; i < nObjs; i++ )
        nHard += pScores[i] >= CEC_OR_BATCH_HARD_THRESHOLD;
    if ( pnHard )
        *pnHard = nHard;
    if ( nHard == 0 )
        return NULL;
    pMark = ABC_CALLOC( int, nObjs );
    for ( i = 0; i < nObjs; i++ )
        pMark[i] = pScores[i] >= CEC_OR_BATCH_HARD_THRESHOLD;
    return pMark;
}

static int Cec_ManCorrCountCandidates( Gia_Man_t * p, int fRings, int * pTfoMark, int * pFallbackObjMark )
{
    Gia_Obj_t * pObj, * pRepr;
    int i, iObj, nPairs = 0;
    assert( p->pReprs != NULL );
    if ( fRings )
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( Gia_ObjIsConst( p, i ) )
            {
                if ( pTfoMark && !pTfoMark[i] )
                    continue;
                if ( pFallbackObjMark && !pFallbackObjMark[i] )
                    continue;
                nPairs++;
            }
            else if ( Gia_ObjIsHead( p, i ) )
            {
                int iPrev = i;
                Gia_ClassForEachObj1( p, i, iObj )
                {
                    if ( (!pTfoMark || pTfoMark[iPrev] || pTfoMark[iObj]) &&
                         (!pFallbackObjMark || pFallbackObjMark[iObj]) )
                        nPairs++;
                    iPrev = iObj;
                }
                if ( (!pTfoMark || pTfoMark[iPrev] || pTfoMark[i]) &&
                     (!pFallbackObjMark || pFallbackObjMark[i]) )
                    nPairs++;
            }
        }
        return nPairs;
    }
    Gia_ManForEachObj1( p, pObj, i )
    {
        pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
        if ( pRepr )
        {
            if ( pTfoMark )
            {
                int idR = Gia_ObjId(p, pRepr);
                if ( !pTfoMark[i] && !pTfoMark[idR] )
                    continue;
            }
            if ( pFallbackObjMark && !pFallbackObjMark[i] )
                continue;
            nPairs++;
        }
    }
    return nPairs;
}

static int Gia_ManCorrSpecReduceOrRange( Gia_Man_t * pNew, Vec_Int_t * vXorLits, int nStart, int nEnd )
{
    int nMid, iLit0, iLit1;
    assert( nStart < nEnd );
    if ( nStart + 1 == nEnd )
        return Vec_IntEntry( vXorLits, nStart );
    nMid = (nStart + nEnd) >> 1;
    iLit0 = Gia_ManCorrSpecReduceOrRange( pNew, vXorLits, nStart, nMid );
    iLit1 = Gia_ManCorrSpecReduceOrRange( pNew, vXorLits, nMid, nEnd );
    return Gia_ManHashOr( pNew, iLit0, iLit1 );
}

static void Gia_ManCorrSpecReduceAppendCleanBatchPos( Gia_Man_t * pNew, Vec_Int_t * vXorLits,
                                                      int nStart, int nEnd, int nBatchSize,
                                                      Vec_Int_t * vBatchSizes )
{
    int j, nChunkEnd, nSize;
    for ( j = nStart; j < nEnd; j += nBatchSize )
    {
        nChunkEnd = Abc_MinInt( j + nBatchSize, nEnd );
        nSize = nChunkEnd - j;
        Vec_IntPush( vBatchSizes, nSize );
        if ( nSize == 1 )
            continue;
        Gia_ManAppendCo( pNew, Gia_ManCorrSpecReduceOrRange( pNew, vXorLits, j, nChunkEnd ) );
    }
}

static void Gia_ManCorrSpecReduceAppendBatchPos( Gia_Man_t * pNew, Vec_Int_t * vXorLits,
                                                 Vec_Int_t * vGroupStarts, int nBatchSize,
                                                 Vec_Int_t * vBatchSizes, Vec_Int_t * vNoBatch )
{
    int i, j, nGroups, nLits, nStart, nEnd, orLit;
    nLits = Vec_IntSize( vXorLits );
    if ( vBatchSizes == NULL || nBatchSize <= 1 )
    {
        Vec_IntForEachEntry( vXorLits, orLit, i )
            Gia_ManAppendCo( pNew, orLit );
        return;
    }
    assert( vGroupStarts != NULL );
    assert( Vec_IntSize(vGroupStarts) > 0 );
    assert( Vec_IntEntryLast(vGroupStarts) == nLits );
    assert( vNoBatch == NULL || Vec_IntSize(vNoBatch) == nLits );
    nGroups = Vec_IntSize(vGroupStarts) - 1;
    for ( i = 0; i < nGroups; i++ )
    {
        nStart = Vec_IntEntry( vGroupStarts, i );
        nEnd   = Vec_IntEntry( vGroupStarts, i+1 );
        assert( nStart < nEnd );
        j = nStart;
        while ( j < nEnd )
        {
            int k;
            if ( vNoBatch && Vec_IntEntry(vNoBatch, j) )
            {
                Vec_IntPush( vBatchSizes, 1 );
                j++;
                continue;
            }
            for ( k = j; k < nEnd; k++ )
                if ( vNoBatch && Vec_IntEntry(vNoBatch, k) )
                    break;
            Gia_ManCorrSpecReduceAppendCleanBatchPos( pNew, vXorLits, j, k, nBatchSize, vBatchSizes );
            j = k;
        }
    }
}

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
//   speculative-substitution status (pReprs[X]) modified between rounds.
//
// Equivalently: P needs re-verification iff some "seed" (a node with a
// changed pReprs entry since last round) lies in TFI(P) inside the
// k-frame unrolling -- equivalently, iRepr or iObj lies in TFO_k(seeds).
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
    Vec_IntFree( p->vSeeds );
    Vec_IntFree( p->vTfoNodes );
    Vec_IntFree( p->vBfsCur );
    Vec_IntFree( p->vBfsNext );
    ABC_FREE( p->pTfoMark );
    ABC_FREE( p );
}

/**Function*************************************************************
  Synopsis    [Snapshot current pReprs into vReprPrev.]
  Description [O(N). Called at the end of each iteration so that the
               next iteration can diff against it.]
***********************************************************************/
static void Cec_IncrMgrSnapshotReprs( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int i;
    assert( pAig->pReprs != NULL );
    for ( i = 0; i < p->nObjs; i++ )
        Vec_IntWriteEntry( p->vReprPrev, i, Gia_ObjRepr(pAig, i) );
}

/**Function*************************************************************
  Synopsis    [Compute seeds: nodes whose pReprs differ from snapshot.]
  Description [O(N). Returns size of seed set. Does NOT update snapshot
               (caller decides when to snapshot).]
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
  Synopsis    [Variant of Gia_ManCorrSpecReduce: TFO filter + OR-batch + iObj filter.]
  Description [Like Gia_ManCorrSpecReduce in topology and speculative reduction.
               Three orthogonal filters/transforms operate on PO emission:

               1. pTfoMark (NULL = no filter): emit pair (a,b) iff pTfoMark[a]
                  || pTfoMark[b]. This is the v7 incremental TFO mask.

               2. pFallbackObjMark (NULL = no filter): additionally require
                  pFallbackObjMark[iObj] = 1, where iObj is the "Obj-side"
                  endpoint of each pair. Each candidate node has at most one
                  pair as its iObj side, so this filter selects an exact
                  per-pair subset (used by the OR-batch fallback path).

               3. pNoBatchObjMark (NULL = no hard-pair split): pairs whose
                  iObj is marked are emitted as singleton fallback entries, not
                  OR-batched with neighbors.

               4. nBatchSize (1 = no batching): when > 1, group every
                  nBatchSize consecutive emitted miter lits with OR and emit
                  one PO per group; vBatchSizes (if non-NULL) records the
                  actual size of each batch (last batch may be smaller).
                  vOutputs still records ALL per-pair endpoints in emission
                  order so the caller can recover pair-to-batch mapping.]
***********************************************************************/
static Gia_Man_t * Gia_ManCorrSpecReduce_Active( Gia_Man_t * p, int nFrames, int fScorr,
                                                 Vec_Int_t ** pvOutputs, int fRings,
                                                 int * pTfoMark,
                                                 int nBatchSize,
                                                 int * pFallbackObjMark,
                                                 int * pNoBatchObjMark,
                                                 Vec_Int_t * vBatchSizes )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    Vec_Int_t * vXorLits, * vGroupStarts = NULL, * vNoBatch = NULL;
    int f, i, iPrev, iObj, iPrevNew, iObjNew;
    int nLits;
    int iGroupStart = -1, iGroupRepr = -1;
    assert( nFrames > 0 );
    assert( Gia_ManRegNum(p) > 0 );
    assert( p->pReprs != NULL );
    assert( nBatchSize >= 1 );
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
    if ( vBatchSizes && nBatchSize > 1 )
    {
        vGroupStarts = Vec_IntAlloc( 1000 );
        if ( pNoBatchObjMark )
            vNoBatch = Vec_IntAlloc( 1000 );
    }
    if ( fRings )
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( Gia_ObjIsConst( p, i ) )
            {
                // const-class: pair is (0, i). iObj == i.
                if ( pTfoMark && !pTfoMark[i] )
                    continue;
                if ( pFallbackObjMark && !pFallbackObjMark[i] )
                    continue;
                iObjNew = Gia_ManCorrSpecReal( pNew, p, pObj, nFrames, 0 );
                iObjNew = Abc_LitNotCond( iObjNew, Gia_ObjPhase(pObj) );
                if ( iObjNew != 0 )
                {
                    if ( vGroupStarts )
                        Vec_IntPush( vGroupStarts, Vec_IntSize(vXorLits) );
                    Vec_IntPush( *pvOutputs, 0 );
                    Vec_IntPush( *pvOutputs, i );
                    Vec_IntPush( vXorLits, iObjNew );
                    if ( vNoBatch )
                        Vec_IntPush( vNoBatch, pNoBatchObjMark[i] );
                }
            }
            else if ( Gia_ObjIsHead( p, i ) )
            {
                // ring class. Walk the whole ring (iPrev advances), but
                // emit edges only when both filters pass. Each edge has a
                // unique iObj across the ring (members + head as closing
                // edge's iObj), so the iObj filter is unambiguous.
                iPrev = i;
                iGroupStart = Vec_IntSize( vXorLits );
                Gia_ClassForEachObj1( p, i, iObj )
                {
                    int fEmit = (pTfoMark == NULL) || pTfoMark[iPrev] || pTfoMark[iObj];
                    if ( fEmit && pFallbackObjMark && !pFallbackObjMark[iObj] )
                        fEmit = 0;
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
                            if ( vNoBatch )
                                Vec_IntPush( vNoBatch, pNoBatchObjMark[iObj] );
                        }
                    }
                    iPrev = iObj;
                }
                // closing edge of the ring: (iPrev, head). iObj == head.
                iObj = i;
                {
                    int fEmit = (pTfoMark == NULL) || pTfoMark[iPrev] || pTfoMark[iObj];
                    if ( fEmit && pFallbackObjMark && !pFallbackObjMark[iObj] )
                        fEmit = 0;
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
                            if ( vNoBatch )
                                Vec_IntPush( vNoBatch, pNoBatchObjMark[iObj] );
                        }
                    }
                }
                if ( vGroupStarts && Vec_IntSize(vXorLits) > iGroupStart )
                    Vec_IntPush( vGroupStarts, iGroupStart );
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
            // pair = (pRepr, pObj). iObj == i.
            if ( pTfoMark )
            {
                int idR = Gia_ObjId(p, pRepr);
                if ( !pTfoMark[i] && !pTfoMark[idR] )
                    continue;
            }
            if ( pFallbackObjMark && !pFallbackObjMark[i] )
                continue;
            iPrevNew = Gia_ObjIsConst(p, i)? 0 : Gia_ManCorrSpecReal( pNew, p, pRepr, nFrames, 0 );
            iObjNew  = Gia_ManCorrSpecReal( pNew, p, pObj, nFrames, 0 );
            iObjNew  = Abc_LitNotCond( iObjNew, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                int idR = Gia_ObjId(p, pRepr);
                if ( vGroupStarts )
                {
                    if ( iGroupStart == -1 )
                    {
                        iGroupStart = Vec_IntSize(vXorLits);
                        iGroupRepr  = idR;
                    }
                    else if ( iGroupRepr != idR )
                    {
                        if ( Vec_IntSize(vXorLits) > iGroupStart )
                            Vec_IntPush( vGroupStarts, iGroupStart );
                        iGroupStart = Vec_IntSize(vXorLits);
                        iGroupRepr  = idR;
                    }
                }
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pObj) );
                Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, iPrevNew, iObjNew) );
                if ( vNoBatch )
                    Vec_IntPush( vNoBatch, pNoBatchObjMark[i] );
            }
        }
        if ( vGroupStarts && iGroupStart != -1 && Vec_IntSize(vXorLits) > iGroupStart )
            Vec_IntPush( vGroupStarts, iGroupStart );
    }
    nLits = Vec_IntSize(vXorLits);
    if ( vGroupStarts )
        Vec_IntPush( vGroupStarts, nLits );
    Gia_ManCorrSpecReduceAppendBatchPos( pNew, vXorLits, vGroupStarts, nBatchSize, vBatchSizes, vNoBatch );
    if ( vNoBatch )
        Vec_IntFree( vNoBatch );
    if ( vGroupStarts )
        Vec_IntFree( vGroupStarts );
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

  Synopsis    [Updates equivalence classes by marking those that timed out.]

  Description [Returns 1 if all ndoes are proved.]
               
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
            if ( Gia_ObjHasSameRepr(p, iRepr, iObj) )
                Counter++;
//            if ( Gia_ObjHasSameRepr(p, iRepr, iObj) )
//                Abc_Print( 1, "Gia_ManCheckRefinements(): Disproved equivalence (%d,%d) is not refined!\n", iRepr, iObj );
//            if ( Gia_ObjHasSameRepr(p, iRepr, iObj) )
//                Cec_ManSimClassRemoveOne( pSim, iObj );
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
    fChanges = 1;
    for ( i = 0; fChanges && (!pPars->nLimitMax || i < pPars->nLimitMax); i++ )
    {
        if ( Cec_ParCorShouldStop( pPars ) )
            break;
        abctime clkBmc = Abc_Clock();
        fChanges = 0;
        pSrm = Gia_ManCorrSpecReduceInit( pAig, pPars->nFrames, nPrefs, !pPars->fLatchCorr, &vOutputs, pPars->fUseRings );
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
    Cec_ParSat_t ParsBatchSat, * pParsBatchSat = &ParsBatchSat;
    Cec_ManSim_t * pSim;
    Gia_Man_t * pSrm;
    int r, RetValue, nPrev[4] = {0};
    abctime clkTotal = Abc_Clock();
    abctime clkSat = 0, clkSim = 0, clkSrm = 0;
    abctime clk2, clk = Abc_Clock();
    // Incremental active-list manager (NULL if -i not set)
    Cec_IncrMgr_t * pMgr = NULL;
    abctime clkIncr = 0;
    int nIncrFallback = 0;
    // OR-batching state (active iff pPars->fOrBatch and TFO mask is in use)
    Vec_Int_t * vBatchSizes = NULL;
    int nBatchSize = CEC_OR_BATCH_SIZE_DEFAULT;
    int nBatchGroups = 0, nBatchGroupsProved = 0, nBatchGroupsFailed = 0;
    int nBatchPairs = 0, nBatchPairsProved = 0, nBatchPairsFailed = 0;
    int nBatchSingles = 0, nBatchFallbackCalls = 0, nBatchSavedCalls = 0;
    int nBatchRounds = 0, nBatchSkippedRate = 0, nBatchNoGroups = 0;
    int nBatchMaxSize = 0, nBatchFullGroups = 0;
    int nSolverCallsTotal = 0, nVirtualChecksTotal = 0, nIncrSkippedTotal = 0;
    int nBatchSkippedWindow = 0, nBatchWindowResets = 0, nBatchBackoff = 0;
    int nBatchHardActiveMax = 0, nBatchHardPromoted = 0, nBatchHardBlocked = 0;
    int nBatchWinPos = 0, nBatchWinSize = 0;
    int pBatchWinGroups[CEC_OR_BATCH_WIN_SIZE] = {0};
    int pBatchWinProved[CEC_OR_BATCH_WIN_SIZE] = {0};
    int pBatchWinVirtual[CEC_OR_BATCH_WIN_SIZE] = {0};
    int pBatchWinActual[CEC_OR_BATCH_WIN_SIZE] = {0};
    unsigned char * pBatchHardScores = NULL;
    double dOrBatchPrevUnsatRate = 0.0;
    abctime clkBatchTry = 0, clkBatchFallback = 0;
    // -b implies -i: OR-batching only makes sense within incremental mode,
    // since the savings come from not re-solving stable pairs per round.
    if ( pPars->fOrBatch )
        pPars->fIncremental = 1;
    if ( Gia_ManRegNum(pAig) == 0 )
    {
        Abc_Print( 1, "Cec_ManLatchCorrespondence(): Not a sequential AIG.\n" );
        return 0;
    }
    if ( pPars->fOrBatch )
        pBatchHardScores = ABC_CALLOC( unsigned char, Gia_ManObjNum(pAig) );
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
    Cec_ManSatSetDefaultParams( pParsBatchSat );
    pParsBatchSat->nBTLimit = Abc_MaxInt( 10, pPars->nBTLimit / 2 );
    pParsBatchSat->fVerbose = 0;
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
        ABC_FREE( pBatchHardScores );
        return 1;
    }
    if ( pPars->nStepsMax == 0 )
    {
        Abc_Print( 1, "Stopped signal correspondence after BMC.\n" );
        Cec_ManSimStop( pSim );
        ABC_FREE( pBatchHardScores );
        return 1;
    }
    // Initialise incremental manager (after BMC, before main refinement loop).
    // Works with both SAT and CBS solver paths: the active-list filter just
    // reduces the number of POs in the SRM, and both solvers iterate POs.
    if ( pPars->fIncremental )
    {
        pMgr = Cec_IncrMgrAlloc( pAig, pPars->nFrames );
        Cec_IncrMgrSnapshotReprs( pMgr );  // initial snapshot (post-BMC pReprs)
    }
    // perform refinement of equivalence classes
    for ( r = 0; r < nIterMax; r++ )
    {
        int fRoundUsedBatch = 0;
        int nRoundAllPairs = 0, nRoundTfoPairs = 0, nRoundEmitPairs = 0;
        int nRoundIncrSkipped = 0, nRoundStructSkipped = 0, nRoundVirtualChecks = 0;
        int nRoundSrmCi = 0, nRoundSrmAnd = 0, nRoundSrmCo = 0;
        int nRoundBatchCos = 0, nRoundFallbackCos = 0, nRoundActualCalls = 0;
        int nRoundBatchGroups = 0, nRoundBatchProved = 0, nRoundBatchFailed = 0;
        int nRoundBatchPairs = 0, nRoundBatchSingles = 0, nRoundBatchMax = 0, nRoundBatchFull = 0;
        int nRoundHardActive = 0, nRoundHardPromoted = 0, nRoundHardBlocked = 0;
        int nRoundWinGroups = 0, nRoundWinProved = 0, nRoundWinVirtual = 0, nRoundWinActual = 0;
        if ( Cec_ParCorShouldStop( pPars ) )
        {
            Cec_ManSimStop( pSim );
            Cec_IncrMgrFree( pMgr );
            ABC_FREE( pBatchHardScores );
            return 1;
        }
        if ( pPars->nStepsMax == r )
        {
            Cec_ManSimStop( pSim );
            Cec_IncrMgrFree( pMgr );
            ABC_FREE( pBatchHardScores );
            Abc_Print( 1, "Stopped signal correspondence after %d refiment iterations.\n", r );
            return 1;
        }
        clk = Abc_Clock();
        // perform speculative reduction (with optional active-list filter)
        clk2 = Abc_Clock();
        {
            int * pTfoMask = NULL;
            int * pHardMark = NULL;
            int fBatchWindowOk = 1;
            int fBatchSkippedByWindow = 0;
            int w;
            nRoundAllPairs = Cec_ManCorrCountCandidates( pAig, pPars->fUseRings, NULL, NULL );
            // Decide whether to apply incremental TFO mask this iteration.
            // Skip on r==0 (no prior snapshot diff yet) and after fallback.
            if ( pMgr && r > 0 )
            {
                abctime clkI = Abc_Clock();
                int nSeeds = Cec_IncrMgrComputeSeeds( pMgr );
                if ( nSeeds == 0 )
                {
                    // No pReprs change since last round => truly converged.
                    // (Both SAT splits and sim refinement go through pReprs,
                    // so an empty diff means no candidate moved last round.)
                    clkIncr += Abc_Clock() - clkI;
                    clkSrm  += Abc_Clock() - clk2;
                    break;
                }
                // Fallback heuristic: if the disturbed set is large enough
                // that recomputing TFO + filtering offers no benefit over
                // a plain rebuild, skip the mask. The threshold is generous
                // because TFO computation itself is cheap (BFS on static
                // fanout); the real cost is solver work, which scales with
                // emitted POs, not seeds.
                if ( nSeeds * 8 > pMgr->nObjs )
                {
                    nIncrFallback++;
                }
                else
                {
                    Cec_IncrMgrComputeTfo( pMgr );
                    pTfoMask = pMgr->pTfoMark;
                }
                clkIncr += Abc_Clock() - clkI;
            }
            // Snapshot for the NEXT iteration's diff. Must happen before
            // the round modifies pReprs (via SAT/sim refinement below).
            if ( pMgr )
                Cec_IncrMgrSnapshotReprs( pMgr );

            // Decide build mode:
            //   pTfoMask + fOrBatch -> Phase-1 OR-batched SRM (vBatchSizes filled);
            //   pTfoMask alone      -> v7 per-pair active SRM;
            //   no mask             -> baseline full SRM.
            nRoundTfoPairs = Cec_ManCorrCountCandidates( pAig, pPars->fUseRings, pTfoMask, NULL );
            if ( pPars->fOrBatch )
            {
                for ( w = 0; w < nBatchWinSize; w++ )
                {
                    nRoundWinGroups  += pBatchWinGroups[w];
                    nRoundWinProved  += pBatchWinProved[w];
                    nRoundWinVirtual += pBatchWinVirtual[w];
                    nRoundWinActual  += pBatchWinActual[w];
                }
                if ( nBatchBackoff > 0 )
                {
                    nBatchBackoff--;
                    nBatchSkippedWindow++;
                    fBatchSkippedByWindow = 1;
                    fBatchWindowOk = 0;
                }
                else if ( nBatchWinSize >= CEC_OR_BATCH_WIN_MIN_ROUNDS &&
                         (nRoundWinVirtual <= nRoundWinActual ||
                          (nRoundWinGroups > 0 && 1.0 * nRoundWinProved / nRoundWinGroups < CEC_OR_BATCH_WIN_RATE_MIN)) )
                {
                    nBatchWinSize = 0;
                    nBatchWinPos = 0;
                    memset( pBatchWinGroups,  0, sizeof(pBatchWinGroups)  );
                    memset( pBatchWinProved,  0, sizeof(pBatchWinProved)  );
                    memset( pBatchWinVirtual, 0, sizeof(pBatchWinVirtual) );
                    memset( pBatchWinActual,  0, sizeof(pBatchWinActual)  );
                    nBatchBackoff = CEC_OR_BATCH_BACKOFF_ROUNDS;
                    nBatchSkippedWindow++;
                    nBatchWindowResets++;
                    fBatchSkippedByWindow = 1;
                    fBatchWindowOk = 0;
                }
            }
            vBatchSizes = NULL;
            if ( pTfoMask && pPars->fOrBatch && dOrBatchPrevUnsatRate > CEC_OR_BATCH_UNSAT_RATE_MIN && fBatchWindowOk )
            {
                pHardMark = Cec_ManCorrBuildHardMark( pBatchHardScores, Gia_ManObjNum(pAig), &nRoundHardActive );
                if ( pHardMark )
                    nRoundHardBlocked = Cec_ManCorrCountCandidates( pAig, pPars->fUseRings, pTfoMask, pHardMark );
                nBatchRounds++;
                fRoundUsedBatch = 1;
                vBatchSizes = Vec_IntAlloc( 1024 );
                pSrm = Gia_ManCorrSpecReduce_Active( pAig, pPars->nFrames, !pPars->fLatchCorr,
                                                     &vOutputs, pPars->fUseRings, pTfoMask,
                                                     nBatchSize, NULL, pHardMark, vBatchSizes );
                nBatchHardBlocked += nRoundHardBlocked;
                nBatchHardActiveMax = Abc_MaxInt( nBatchHardActiveMax, nRoundHardActive );
            }
            else if ( pTfoMask && pPars->fOrBatch )
            {
                if ( !fBatchSkippedByWindow )
                    nBatchSkippedRate++;
                pSrm = Gia_ManCorrSpecReduce_Active( pAig, pPars->nFrames, !pPars->fLatchCorr,
                                                     &vOutputs, pPars->fUseRings, pTfoMask,
                                                     1, NULL, NULL, NULL );
            }
            else if ( pTfoMask )
                pSrm = Gia_ManCorrSpecReduce_Active( pAig, pPars->nFrames, !pPars->fLatchCorr,
                                                     &vOutputs, pPars->fUseRings, pTfoMask,
                                                     1, NULL, NULL, NULL );
            else
                pSrm = Gia_ManCorrSpecReduce( pAig, pPars->nFrames, !pPars->fLatchCorr, &vOutputs, pPars->fUseRings );
            ABC_FREE( pHardMark );
            if ( pTfoMask && pPars->fVeryVerbose )
                Abc_Print( 1, "  [incr r=%d seeds=%d tfo=%d POs=%d batch=%d prev-unsat=%.1f%%]\n",
                           r, Vec_IntSize(pMgr->vSeeds), Vec_IntSize(pMgr->vTfoNodes),
                           Gia_ManCoNum(pSrm), vBatchSizes ? Vec_IntSize(vBatchSizes) : 0,
                           100.0 * dOrBatchPrevUnsatRate );
        }
        assert( Gia_ManRegNum(pSrm) == 0 && Gia_ManPiNum(pSrm) == Gia_ManRegNum(pAig)+(pPars->nFrames+!pPars->fLatchCorr)*Gia_ManPiNum(pAig) );
        nRoundEmitPairs = Vec_IntSize(vOutputs) / 2;
        nRoundIncrSkipped = Abc_MaxInt( 0, nRoundAllPairs - nRoundTfoPairs );
        nRoundStructSkipped = Abc_MaxInt( 0, nRoundTfoPairs - nRoundEmitPairs );
        nRoundSrmCi       = Gia_ManCiNum(pSrm);
        nRoundSrmAnd      = Gia_ManAndNum(pSrm);
        nRoundSrmCo       = Gia_ManCoNum(pSrm);
        nIncrSkippedTotal += nRoundIncrSkipped;
        clkSrm += Abc_Clock() - clk2;
        if ( Gia_ManCoNum(pSrm) == 0 )
        {
            if ( vBatchSizes == NULL )
            {
                Vec_IntFree( vOutputs );
                Gia_ManStop( pSrm );
                break;
            }
            nBatchNoGroups++;
            vStatus = Vec_StrAlloc( 0 );
            vCexStore = Vec_IntAlloc( 0 );
            Gia_ManStop( pSrm );
        }
        else
        {
            abctime clkSolve;
//Gia_DumpAiger( pSrm, "corrsrm", r, 2 );
            // found counter-examples to speculation
            clk2 = Abc_Clock();
            if ( vBatchSizes )
                vCexStore = Cec_ManSolveMiterWithSolver( pSrm, pParsBatchSat, &vStatus, pPars->fOrBatchUseCSat );
            else
                vCexStore = Cec_ManSolveMiterWithSolver( pSrm, pParsSat, &vStatus, pPars->fUseCSat );
            Gia_ManStop( pSrm );
            clkSolve = Abc_Clock() - clk2;
            if ( vBatchSizes )
                clkBatchTry += clkSolve;
            clkSat += clkSolve;
        }
        // OR-batching Phase-2: expand per-batch status to per-pair, then run
        // a fallback per-pair solve for any batch that failed (SAT or timeout).
        // Soundness: a batched OR is UNSAT iff every disjunct (pair miter) is
        // unsatisfiable, so vStatus[batch]==1 individually proves all K pairs
        // in the batch. If the batched OR is SAT/unknown, we cannot tell which
        // disjunct is the offender, so we MUST resolve per-pair to keep the
        // v7 invariant ("UNSAT in round r"). Without this fallback, sibling
        // pairs of a SAT pair would silently slip through without ever being
        // proven.
        if ( vBatchSizes )
        {
            int N    = Vec_IntSize(vOutputs) / 2;
            int M    = Vec_IntSize(vBatchSizes);
            int p, fbIdx, pIdx, j, poIdx;
            int nFailed = 0;
            Vec_Str_t * vStatusFinal = Vec_StrAlloc( N );
            int * pFallbackMark = ABC_CALLOC( int, Gia_ManObjNum(pAig) );
            Vec_Int_t * vPairMap = Vec_IntStartFull( Gia_ManObjNum(pAig) );
            Vec_Int_t * vCexStoreBatch = vCexStore;
            vCexStore = Vec_IntAlloc( 10000 );
            nRoundBatchCos = Vec_StrSize( vStatus );
            pIdx = 0;
            poIdx = 0;
            for ( j = 0; j < M; j++ )
            {
                int  sz = Vec_IntEntry( vBatchSizes, j );
                int  kk;
                char st = -1;
                assert( sz >= 1 );
                if ( sz > 1 )
                {
                    assert( poIdx < Vec_StrSize(vStatus) );
                    st = Vec_StrEntry( vStatus, poIdx++ );
                    nBatchGroups++;
                    nBatchPairs += sz;
                    nRoundBatchGroups++;
                    nRoundBatchPairs += sz;
                    nRoundBatchMax = Abc_MaxInt( nRoundBatchMax, sz );
                    nBatchMaxSize  = Abc_MaxInt( nBatchMaxSize, sz );
                    if ( sz == nBatchSize )
                    {
                        nRoundBatchFull++;
                        nBatchFullGroups++;
                    }
                }
                for ( kk = 0; kk < sz; kk++, pIdx++ )
                {
                    int iObjP;
                    if ( sz > 1 && st == 1 )
                    {
                        Vec_StrPush( vStatusFinal, 1 );
                        continue;
                    }
                    iObjP = Vec_IntEntry( vOutputs, 2*pIdx + 1 );
                    pFallbackMark[iObjP] = 1;
                    Vec_IntWriteEntry( vPairMap, iObjP, pIdx );
                    Vec_StrPush( vStatusFinal, -2 );  // placeholder, resolved below
                    nFailed++;
                }
                if ( sz == 1 )
                {
                    nBatchSingles++;
                    nRoundBatchSingles++;
                }
                else if ( st == 1 )
                {
                    nBatchGroupsProved++;
                    nBatchPairsProved += sz;
                    nBatchSavedCalls += sz - 1;
                    nRoundBatchProved++;
                }
                else
                {
                    nBatchGroupsFailed++;
                    nBatchPairsFailed += sz;
                    nRoundBatchFailed++;
                }
            }
            assert( pIdx == N );
            assert( poIdx == Vec_StrSize(vStatus) );
            Vec_IntFree( vCexStoreBatch );
            if ( nFailed > 0 )
            {
                Vec_Int_t * vOutputsFb = NULL;
                Vec_Str_t * vStatusFb  = NULL;
                Vec_Int_t * vCexStoreFb = NULL;
                Gia_Man_t * pSrmFb;
                int Nfb;
                abctime clkSolve;

                clk2 = Abc_Clock();
                // vBatchSizes!=NULL implies Phase-1 used the TFO mask, so pMgr
                // is non-NULL and pMgr->pTfoMark is the active mask this round.
                pSrmFb = Gia_ManCorrSpecReduce_Active( pAig, pPars->nFrames, !pPars->fLatchCorr,
                                                       &vOutputsFb, pPars->fUseRings, pMgr->pTfoMark,
                                                       1, pFallbackMark, NULL, NULL );
                clkSrm += Abc_Clock() - clk2;
                clk2 = Abc_Clock();
                vCexStoreFb = Cec_ManSolveMiterWithSolver( pSrmFb, pParsSat, &vStatusFb, pPars->fUseCSat );
                Gia_ManStop( pSrmFb );
                clkSolve = Abc_Clock() - clk2;
                clkBatchFallback += clkSolve;
                clkSat += clkSolve;

                Nfb   = Vec_IntSize(vOutputsFb) / 2;
                nBatchFallbackCalls += Nfb;
                nRoundFallbackCos += Nfb;
                for ( fbIdx = 0; fbIdx < Nfb; fbIdx++ )
                {
                    int iObjP2  = Vec_IntEntry( vOutputsFb,  2*fbIdx + 1 );
                    int iFinal  = Vec_IntEntry( vPairMap, iObjP2 );
                    if ( iFinal >= 0 )
                    {
                        assert( Vec_StrEntry(vStatusFinal, iFinal) == -2 );
                        Vec_StrWriteEntry( vStatusFinal, iFinal, Vec_StrEntry(vStatusFb, fbIdx) );
                    }
                }
                // Any unresolved placeholders were selected for fallback but
                // did not emit a non-trivial miter in phase 2; structural
                // reduction proved them locally.
                for ( p = 0; p < N; p++ )
                    if ( Vec_StrEntry(vStatusFinal, p) == -2 )
                        Vec_StrWriteEntry( vStatusFinal, p, 1 );
                Vec_IntAppend( vCexStore, vCexStoreFb );
                Vec_IntFree( vCexStoreFb );
                Vec_IntFree( vOutputsFb );
                Vec_StrFree( vStatusFb );
            }
            ABC_FREE( pFallbackMark );
            Vec_IntFree( vPairMap );
            Vec_IntFree( vBatchSizes );
            vBatchSizes = NULL;
            Vec_StrFree( vStatus );
            vStatus = vStatusFinal;
            if ( pPars->fVeryVerbose )
                Abc_Print( 1, "  [batch r=%d groups=%d pos=%d pairs=%d fallback-pairs=%d solver=%s]\n",
                           r, M, poIdx, N, nFailed, pPars->fOrBatchUseCSat ? "CBS" : "SAT" );
        }
        {
            int nRoundProved, nRoundDisproved, nRoundFailed, nRoundTotal;
            Cec_ManStatusCount( vStatus, &nRoundProved, &nRoundDisproved, &nRoundFailed );
            nRoundTotal = nRoundProved + nRoundDisproved + nRoundFailed;
            nRoundVirtualChecks = nRoundTotal;
            nRoundActualCalls = fRoundUsedBatch ? nRoundBatchCos + nRoundFallbackCos : nRoundTotal;
            nSolverCallsTotal += nRoundActualCalls;
            nVirtualChecksTotal += nRoundVirtualChecks;
            if ( pBatchHardScores && fRoundUsedBatch )
            {
                Cec_ManCorrUpdateHardScores( pAig, pBatchHardScores, vOutputs, vStatus,
                                             &nRoundHardActive, &nRoundHardPromoted );
                nBatchHardPromoted += nRoundHardPromoted;
                nBatchHardActiveMax = Abc_MaxInt( nBatchHardActiveMax, nRoundHardActive );
            }
            if ( fRoundUsedBatch )
            {
                pBatchWinGroups[nBatchWinPos]  = nRoundBatchGroups;
                pBatchWinProved[nBatchWinPos]  = nRoundBatchProved;
                pBatchWinVirtual[nBatchWinPos] = nRoundVirtualChecks;
                pBatchWinActual[nBatchWinPos]  = nRoundActualCalls;
                nBatchWinPos = (nBatchWinPos + 1) % CEC_OR_BATCH_WIN_SIZE;
                nBatchWinSize = Abc_MinInt( CEC_OR_BATCH_WIN_SIZE, nBatchWinSize + 1 );
            }
            if ( pPars->fOrBatch )
            {
                int w;
                nRoundWinGroups = nRoundWinProved = nRoundWinVirtual = nRoundWinActual = 0;
                for ( w = 0; w < nBatchWinSize; w++ )
                {
                    nRoundWinGroups  += pBatchWinGroups[w];
                    nRoundWinProved  += pBatchWinProved[w];
                    nRoundWinVirtual += pBatchWinVirtual[w];
                    nRoundWinActual  += pBatchWinActual[w];
                }
            }
            if ( pPars->fOrBatch )
                dOrBatchPrevUnsatRate = nRoundTotal ? 1.0 * nRoundProved / nRoundTotal : 0.0;
            if ( pPars->fVerbose && pPars->fOrBatch )
                Abc_Print( 1, "CEX-STAT: r=%d cand=%d tfo=%d emit=%d incrSkip=%d strSkip=%d srm(ci/and/co)=%d/%d/%d calls=%d virt=%d unsat/sat/to=%d/%d/%d batch(co/grp/ok/fail/pairs/sing/full/max)=%d/%d/%d/%d/%d/%d/%d/%d fbCo=%d hard(block/active/new)=%d/%d/%d win(grp/ok/delta/backoff)=%d/%d/%d/%d\n",
                           r, nRoundAllPairs, nRoundTfoPairs, nRoundEmitPairs,
                           nRoundIncrSkipped, nRoundStructSkipped,
                           nRoundSrmCi, nRoundSrmAnd, nRoundSrmCo,
                           nRoundActualCalls, nRoundVirtualChecks,
                           nRoundProved, nRoundDisproved, nRoundFailed,
                           nRoundBatchCos, nRoundBatchGroups, nRoundBatchProved, nRoundBatchFailed,
                           nRoundBatchPairs, nRoundBatchSingles, nRoundBatchFull, nRoundBatchMax,
                           nRoundFallbackCos,
                           nRoundHardBlocked, nRoundHardActive, nRoundHardPromoted,
                           nRoundWinGroups, nRoundWinProved, nRoundWinVirtual - nRoundWinActual, nBatchBackoff );
        }
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
            ABC_FREE( pBatchHardScores );
            return 1;
        }
        // quit if const is no longer there
        if ( pPars->fStopWhenGone && Gia_ManPoNum(pAig) == 1 && !Gia_ObjIsConst( pAig, Gia_ObjFaninId0p(pAig, Gia_ManPo(pAig, 0)) ) )
        {
            printf( "Iterative refinement is stopped after iteration %d\n", r );
            printf( "because the property output is no longer a candidate constant.\n" );
            Cec_ManSimStop( pSim );
            Cec_IncrMgrFree( pMgr );
            ABC_FREE( pBatchHardScores );
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
                ABC_FREE( pBatchHardScores );
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
            Abc_Print( 1, "Incr: fallback rounds = %d\n", nIncrFallback );
        }
        if ( pPars->fOrBatch )
        {
            double dFallbackAvg = nBatchFallbackCalls ? 1.0 * clkBatchFallback / CLOCKS_PER_SEC / nBatchFallbackCalls : 0.0;
            double dTrySec      = 1.0 * clkBatchTry / CLOCKS_PER_SEC;
            double dEstSaved    = nBatchSavedCalls * dFallbackAvg - dTrySec;
            Abc_Print( 1, "Batch: solver=%s K=%d limit=%d rounds=%d skipped-rate=%d no-groups=%d\n",
                       pPars->fOrBatchUseCSat ? "CBS" : "SAT",
                       nBatchSize, pParsBatchSat->nBTLimit, nBatchRounds, nBatchSkippedRate, nBatchNoGroups );
            Abc_Print( 1, "Batch: groups=%d proved=%d failed=%d pairs=%d proved=%d failed=%d singles=%d fallback-calls=%d saved-calls=%d\n",
                       nBatchGroups, nBatchGroupsProved, nBatchGroupsFailed,
                       nBatchPairs, nBatchPairsProved, nBatchPairsFailed,
                       nBatchSingles, nBatchFallbackCalls, nBatchSavedCalls );
            Abc_Print( 1, "Batch: actual-calls=%d virtual-calls=%d call-delta=%d incr-skipped=%d max-size=%d full-groups=%d\n",
                       nSolverCallsTotal, nVirtualChecksTotal, nVirtualChecksTotal - nSolverCallsTotal,
                       nIncrSkippedTotal, nBatchMaxSize, nBatchFullGroups );
            Abc_Print( 1, "Batch: hard-active-max=%d hard-promoted=%d hard-blocked=%d window-skipped=%d window-resets=%d\n",
                       nBatchHardActiveMax, nBatchHardPromoted, nBatchHardBlocked,
                       nBatchSkippedWindow, nBatchWindowResets );
            Abc_Print( 1, "Batch: group-proved-rate=%.1f%% pair-proved-rate=%.1f%% est-saved-vs-fallback-avg=%.2f sec\n",
                       100.0 * nBatchGroupsProved / (nBatchGroups ? nBatchGroups : 1),
                       100.0 * nBatchPairsProved / (nBatchPairs ? nBatchPairs : 1),
                       dEstSaved );
            ABC_PRTP( "BatchTry", clkBatchTry, clkTotal );
            ABC_PRTP( "BatchFb ", clkBatchFallback, clkTotal );
        }
        Abc_PrintTime( 1, "TOTAL",  clkTotal );
    }
    Cec_IncrMgrFree( pMgr );
    ABC_FREE( pBatchHardScores );
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
