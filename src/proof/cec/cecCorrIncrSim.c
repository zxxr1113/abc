/**CFile****************************************************************

  FileName    [cecCorrIncrSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Incremental local-simulation manager for &scorr.]

  Description [Replaces a whole-graph resimulation pass with a TFO-only one
  when the dirty cone induced by the SAT counter-examples is small.

  For each packed CEX batch the host (Cec_ManResimulateCounterExamples) hands
  us the fully-prepared per-batch CI buffer vSimInfo (CEX bits packed into
  lanes, repr ROs remapped onto their candidate ROs).  We then:

    1. derive sources = the input slots of vSimInfo that are nonzero, i.e.
       deviate from the all-zero baseline (lane 0).  This captures both the
       CEX literals and the values the repr-remap copied onto candidate ROs,
       so the cone can never miss a remapped initial state;
    2. walk the frame-aware TFO over static fanouts to collect the dirty
       (frame, objId) cone;
    3. if the cone is larger than CEC_INCRSIM_FRAC of the unrolled key space,
       give up and let the caller run the full simulation (a bit-parallel
       full sweep is cheaper than a local sweep once the cone is wide);
    4. otherwise evaluate signatures for the cone nodes only and refine just
       the equivalence classes that contain a dirty node, frame by frame.

  Untouched nodes keep their phase signature (all bits = Gia_ObjPhase), which
  is exactly their value under the all-zero baseline, so comparisons via
  Cec_ManSimCompareEqual stay sound.  Splitting a class only happens when two
  members differ under a concrete CEX lane, hence every split is sound; the
  caller force-splits any SAT pair the local pass leaves merged.

  All scratch is allocated once (resident across iterations) and reset in O(1)
  by bumping a version stamp, so the per-iteration overhead is O(|dirty cone|),
  never O(N).

  Author      [Xiran Zhao]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Jun 2026.]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Fall back to the full sweep when the dirty cone exceeds this fraction of
// the unrolled key space (nFrames*nObjs).  A local random-access sweep has a
// much larger per-node constant than the cache-friendly bit-parallel full
// sweep, so the cone must be a small fraction to actually win wall-time.
#define CEC_INCRSIM_FRAC_NUM 1
#define CEC_INCRSIM_FRAC_DEN 5

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline int Cec_IncrSimKey( Cec_IncrSim_t * p, int frame, int objId )
{
    return frame * p->nObjs + objId;
}

// Returns the local word buffer of a dirty key, or NULL if the key is not
// dirty (caller substitutes the phase vector).
static inline unsigned * Cec_IncrSimLocal( Cec_IncrSim_t * p, int frame, int objId )
{
    int key = Cec_IncrSimKey( p, frame, objId );
    if ( p->pMark[key] != p->nMarkVersion )
        return NULL;
    return (unsigned *)Vec_IntArray(p->vSimData) + p->pSimOff[key];
}

// Returns the signature of (frame, objId): the local word if dirty, otherwise
// the constant phase vector for that object.
static inline unsigned * Cec_IncrSimSig( Cec_IncrSim_t * p, int frame, int objId )
{
    unsigned * pLoc = Cec_IncrSimLocal( p, frame, objId );
    if ( pLoc )
        return pLoc;
    return Gia_ObjPhase( Gia_ManObj(p->pAig, objId) ) ? p->pPhase1 : p->pPhase0;
}

// Marks (frame, objId) dirty and allocates a zeroed word slot for it.  No-op
// (returns 0) if already marked this batch.  Allocation happens here, before
// evaluation, so vSimData never grows during eval and word pointers stay
// stable across the eval/refine phase.
static inline int Cec_IncrSimMark( Cec_IncrSim_t * p, int frame, int objId )
{
    int w, key = Cec_IncrSimKey( p, frame, objId );
    if ( p->pMark[key] == p->nMarkVersion )
        return 0;
    p->pMark[key]   = p->nMarkVersion;
    p->pSimOff[key] = Vec_IntSize( p->vSimData );
    for ( w = 0; w < p->nWords; w++ )
        Vec_IntPush( p->vSimData, 0 );
    Vec_IntPush( p->vDirtyKeys, key );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Allocates the resident incremental local-sim manager.]

  Description [nWords is the number of simulation words per key (must match
  the host Cec_ManSim_t).  Requires static fanout on pAig for the TFO walk;
  builds it if absent and remembers to tear it down on Free.  The host AIG
  must outlive the manager.]

  SideEffects [Builds static fanout on pAig if not already present.]

***********************************************************************/
Cec_IncrSim_t * Cec_IncrSimAlloc( Gia_Man_t * pAig, int nFrames, int nWords )
{
    Cec_IncrSim_t * p = ABC_CALLOC( Cec_IncrSim_t, 1 );
    int w;
    p->pAig    = pAig;
    p->nFrames = nFrames;
    p->nObjs   = Gia_ManObjNum( pAig );
    p->nPis    = Gia_ManPiNum( pAig );
    p->nRegs   = Gia_ManRegNum( pAig );
    p->nWords  = nWords;
    // Dense arrays; zero-initialized so the first nMarkVersion==1 reset
    // distinguishes "never marked" from "marked in version 1".
    p->pMark        = ABC_CALLOC( int, (size_t)nFrames * p->nObjs );
    p->pSimOff      = ABC_ALLOC ( int, (size_t)nFrames * p->nObjs );
    p->nMarkVersion = 0;
    p->pRootMark    = ABC_CALLOC( int, p->nObjs );
    p->nRootVersion = 0;
    p->vSimData     = Vec_IntAlloc( 4096 );
    p->vSources     = Vec_IntAlloc( 1024 );
    p->vDirtyKeys   = Vec_IntAlloc( 1024 );
    p->vQueue       = Vec_IntAlloc( 1024 );
    p->vDirtyRoots  = Vec_IntAlloc( 1024 );
    p->vClassOld    = Vec_IntAlloc( 64 );
    p->vClassNew    = Vec_IntAlloc( 64 );
    p->pPhase0      = ABC_ALLOC( unsigned, nWords );
    p->pPhase1      = ABC_ALLOC( unsigned, nWords );
    for ( w = 0; w < nWords; w++ )
    {
        p->pPhase0[w] = 0;
        p->pPhase1[w] = ~(unsigned)0;
    }
    if ( pAig->vFanout == NULL )
    {
        Gia_ManStaticFanoutStart( pAig );
        p->fOwnsFanout = 1;
    }
    return p;
}

void Cec_IncrSimFree( Cec_IncrSim_t * p )
{
    if ( p == NULL ) return;
    if ( p->fOwnsFanout )
        Gia_ManStaticFanoutStop( p->pAig );
    Vec_IntFreeP( &p->vSimData );
    Vec_IntFreeP( &p->vSources );
    Vec_IntFreeP( &p->vDirtyKeys );
    Vec_IntFreeP( &p->vQueue );
    Vec_IntFreeP( &p->vDirtyRoots );
    Vec_IntFreeP( &p->vClassOld );
    Vec_IntFreeP( &p->vClassNew );
    ABC_FREE( p->pMark );
    ABC_FREE( p->pSimOff );
    ABC_FREE( p->pRootMark );
    ABC_FREE( p->pPhase0 );
    ABC_FREE( p->pPhase1 );
    ABC_FREE( p );
}

// Clears all per-batch state in O(1) via a version bump.
static void Cec_IncrSimReset( Cec_IncrSim_t * p )
{
    Vec_IntClear( p->vSimData );
    Vec_IntClear( p->vSources );
    Vec_IntClear( p->vDirtyKeys );
    Vec_IntClear( p->vQueue );
    p->nMarkVersion++;
    // Guard against integer overflow on the (astronomically unlikely)
    // wrap-around: fall back to an explicit clear of the dense mark array.
    if ( p->nMarkVersion == 0 )
    {
        memset( p->pMark, 0, sizeof(int) * (size_t)p->nFrames * p->nObjs );
        p->nMarkVersion = 1;
    }
}

/**Function*************************************************************

  Synopsis    [Derives dirty sources from the prepared CI buffer vSimInfo.]

  Description [vSimInfo layout matches Cec_ManSeqResimulate: slots [0..nRegs)
  are the initial ROs at frame 0, then nFrames groups of nPis primary inputs.
  A slot whose words are not all zero deviates from the all-zero baseline and
  is therefore a source; mapping it back to (frame, objId) and marking it
  seeds the TFO walk.  Reading nonzero-ness straight off vSimInfo captures
  both the CEX literals and any value the repr-remap copied onto candidate
  ROs.]

  SideEffects [Marks source keys; copies their words into the local pool.]

***********************************************************************/
static void Cec_IncrSimCollectSources( Cec_IncrSim_t * p, Vec_Ptr_t * vSimInfo )
{
    int nWords = p->nWords;
    int slot, w, frame, objId;
    int nSlots = p->nRegs + p->nFrames * p->nPis;
    assert( nWords == Vec_PtrReadWordsSimInfo(vSimInfo) );
    for ( slot = 0; slot < nSlots; slot++ )
    {
        unsigned * pInfo = (unsigned *)Vec_PtrEntry( vSimInfo, slot );
        int fNonZero = 0;
        for ( w = 0; w < nWords; w++ )
            if ( pInfo[w] ) { fNonZero = 1; break; }
        if ( !fNonZero )
            continue;
        if ( slot < p->nRegs )
        {
            frame = 0;
            objId = Gia_ObjId( p->pAig, Gia_ManRo(p->pAig, slot) );
        }
        else
        {
            int t = slot - p->nRegs;
            frame = t / p->nPis;
            objId = Gia_ObjId( p->pAig, Gia_ManPi(p->pAig, t % p->nPis) );
        }
        if ( frame >= p->nFrames )
            continue;
        if ( Cec_IncrSimMark( p, frame, objId ) )
        {
            unsigned * pLoc = Cec_IncrSimLocal( p, frame, objId );
            for ( w = 0; w < nWords; w++ )
                pLoc[w] = pInfo[w];
            Vec_IntPush( p->vSources, Cec_IncrSimKey(p, frame, objId) );
            Vec_IntPush( p->vQueue,   Cec_IncrSimKey(p, frame, objId) );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Frame-aware BFS over static fanouts from all queued sources.]

  Description [AND fanouts stay in the same frame; RI fanouts cross to
  (frame+1, RoOf(RI)); PO fanouts terminate.  Returns the number of distinct
  dirty (frame, objId) keys.]

  SideEffects [Drains vQueue.]

***********************************************************************/
static int Cec_IncrSimComputeTfo( Cec_IncrSim_t * p )
{
    while ( Vec_IntSize(p->vQueue) > 0 )
    {
        int key   = Vec_IntPop( p->vQueue );
        int frame = key / p->nObjs;
        int objId = key % p->nObjs;
        int FanId, i;
        Gia_ObjForEachFanoutStaticId( p->pAig, objId, FanId, i )
        {
            Gia_Obj_t * pFan = Gia_ManObj( p->pAig, FanId );
            if ( Gia_ObjIsAnd(pFan) )
            {
                if ( Cec_IncrSimMark( p, frame, FanId ) )
                    Vec_IntPush( p->vQueue, Cec_IncrSimKey(p, frame, FanId) );
            }
            else if ( Gia_ObjIsRi(p->pAig, pFan) )
            {
                int nextFrame = frame + 1;
                int roId;
                if ( nextFrame >= p->nFrames )
                    continue;
                roId = Gia_ObjRiToRoId( p->pAig, FanId );
                if ( Cec_IncrSimMark( p, nextFrame, roId ) )
                    Vec_IntPush( p->vQueue, Cec_IncrSimKey(p, nextFrame, roId) );
            }
            // PO fanouts: terminal for class-refinement purposes.
        }
    }
    return Vec_IntSize( p->vDirtyKeys );
}

/**Function*************************************************************

  Synopsis    [Evaluates local signatures for every dirty key.]

  Description [vDirtyKeys is sorted ascending, i.e. frame-major / objId-minor,
  which is a topological order: an AND's fanins have smaller ids (same frame),
  and a dirty RO at frame f>0 reads its driving RI's fanin from frame f-1
  (already evaluated).  Sources were filled by Cec_IncrSimCollectSources and
  are skipped here.]

  SideEffects []

***********************************************************************/
static void Cec_IncrSimEvaluate( Cec_IncrSim_t * p )
{
    int nWords = p->nWords, i, w, key;
    Vec_IntSort( p->vDirtyKeys, 0 );
    Vec_IntForEachEntry( p->vDirtyKeys, key, i )
    {
        int frame = key / p->nObjs;
        int objId = key % p->nObjs;
        Gia_Obj_t * pObj = Gia_ManObj( p->pAig, objId );
        unsigned * pRes = Cec_IncrSimLocal( p, frame, objId );
        if ( Gia_ObjIsAnd(pObj) )
        {
            unsigned * pR0 = Cec_IncrSimSig( p, frame, Gia_ObjFaninId0(pObj, objId) );
            unsigned * pR1 = Cec_IncrSimSig( p, frame, Gia_ObjFaninId1(pObj, objId) );
            if ( Gia_ObjFaninC0(pObj) )
            {
                if ( Gia_ObjFaninC1(pObj) )
                    for ( w = 0; w < nWords; w++ ) pRes[w] = ~(pR0[w] | pR1[w]);
                else
                    for ( w = 0; w < nWords; w++ ) pRes[w] = ~pR0[w] & pR1[w];
            }
            else
            {
                if ( Gia_ObjFaninC1(pObj) )
                    for ( w = 0; w < nWords; w++ ) pRes[w] = pR0[w] & ~pR1[w];
                else
                    for ( w = 0; w < nWords; w++ ) pRes[w] = pR0[w] & pR1[w];
            }
        }
        else if ( Gia_ObjIsRo(p->pAig, pObj) && frame > 0 )
        {
            // RO value at frame f = its driving RI's input at frame f-1.
            Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
            int iDrv = Gia_ObjFaninId0( pRi, Gia_ObjId(p->pAig, pRi) );
            unsigned * pDrv = Cec_IncrSimSig( p, frame - 1, iDrv );
            if ( Gia_ObjFaninC0(pRi) )
                for ( w = 0; w < nWords; w++ ) pRes[w] = ~pDrv[w];
            else
                for ( w = 0; w < nWords; w++ ) pRes[w] = pDrv[w];
            // Lane 0 is the per-frame phase reference (the full sweep re-forces
            // every CI's bit 0 to 0 each frame).  RO phase is 0, so clear it.
            pRes[0] &= ~(unsigned)1;
        }
        // else: a source key (frame-0 RO or PI); its words are already filled.
    }
}

/**Function*************************************************************

  Synopsis    [Refines one class at one frame using local signatures.]

  Description [Mirror of Cec_ManSimClassRefineOne_rec but reading per-frame
  local words (phase vector for untouched members).  Members compared not
  equal to the root are peeled into a new class, recursively refined.]

  SideEffects [Mutates pAig->pReprs/pNexts.]

***********************************************************************/
static void Cec_IncrSimRefineClass( Cec_IncrSim_t * p, int frame, int iRoot )
{
    unsigned * pSim0, * pSim1;
    int Ent;
    Vec_IntClear( p->vClassOld );
    Vec_IntClear( p->vClassNew );
    Vec_IntPush( p->vClassOld, iRoot );
    pSim0 = Cec_IncrSimSig( p, frame, iRoot );
    Gia_ClassForEachObj1( p->pAig, iRoot, Ent )
    {
        pSim1 = Cec_IncrSimSig( p, frame, Ent );
        if ( Cec_ManSimCompareEqual( pSim0, pSim1, p->nWords ) )
            Vec_IntPush( p->vClassOld, Ent );
        else
            Vec_IntPush( p->vClassNew, Ent );
    }
    if ( Vec_IntSize(p->vClassNew) == 0 )
        return;
    Cec_ManSimClassCreate( p->pAig, p->vClassOld );
    Cec_ManSimClassCreate( p->pAig, p->vClassNew );
    if ( Vec_IntSize(p->vClassNew) > 1 )
        Cec_IncrSimRefineClass( p, frame, Vec_IntEntry(p->vClassNew, 0) );
}

/**Function*************************************************************

  Synopsis    [Refines the classes touched in one frame.]

  Description [Collects, for the given frame, the distinct class roots (and
  const candidates) that contain a dirty node, then refines each once.  A
  const candidate whose local signature deviates from its phase vector is no
  longer constant and is removed from the const class (conservative coarser
  handling, matching the design doc).]

  SideEffects [Mutates pAig->pReprs/pNexts.]

***********************************************************************/
static void Cec_IncrSimRefineFrame( Cec_IncrSim_t * p, int frame, int iLo, int iHi )
{
    Gia_Man_t * pAig = p->pAig;
    int i, Ent;
    // bump root-mark version for this frame
    p->nRootVersion++;
    if ( p->nRootVersion == 0 )
    {
        memset( p->pRootMark, 0, sizeof(int) * p->nObjs );
        p->nRootVersion = 1;
    }
    Vec_IntClear( p->vDirtyRoots );
    // collect distinct roots / const candidates touched this frame
    for ( i = iLo; i < iHi; i++ )
    {
        int objId = Vec_IntEntry(p->vDirtyKeys, i) % p->nObjs;
        if ( Gia_ObjIsConst(pAig, objId) )
        {
            // const candidate: drop from const class iff it deviates from phase
            unsigned * pLoc = Cec_IncrSimLocal( p, frame, objId );
            unsigned * pPh  = Gia_ObjPhase(Gia_ManObj(pAig, objId)) ? p->pPhase1 : p->pPhase0;
            if ( pLoc && !Cec_ManSimCompareEqual( pLoc, pPh, p->nWords ) )
                Gia_ObjSetRepr( pAig, objId, GIA_VOID );
            continue;
        }
        if ( !Gia_ObjIsClass(pAig, objId) )
            continue;
        {
            int iRoot = Gia_ObjIsHead(pAig, objId) ? objId : Gia_ObjRepr(pAig, objId);
            if ( p->pRootMark[iRoot] == p->nRootVersion )
                continue;
            p->pRootMark[iRoot] = p->nRootVersion;
            Vec_IntPush( p->vDirtyRoots, iRoot );
        }
    }
    // refine each touched class once
    Vec_IntForEachEntry( p->vDirtyRoots, Ent, i )
        if ( Gia_ObjIsHead(pAig, Ent) )   // may have been split away as non-head
            Cec_IncrSimRefineClass( p, frame, Ent );
}

/**Function*************************************************************

  Synopsis    [Tries to handle one prepared CEX batch by local TFO sim.]

  Description [Returns 1 if the batch was refined locally; 0 if the caller
  should run the full Cec_ManSeqResimulate for this batch (cone too wide).
  vSimInfo is the per-batch CI buffer already produced by the host
  (CEX bits packed, repr ROs remapped).]

  SideEffects [On success, mutates pAig->pReprs/pNexts via local refinement.]

***********************************************************************/
int Cec_IncrSimTryBatch( Cec_IncrSim_t * p, Cec_ManSim_t * pSim, Vec_Ptr_t * vSimInfo, int nFrames )
{
    int nDirty, iLo;
    assert( nFrames <= p->nFrames );
    (void)pSim;  // refinement mutates pAig->pReprs directly, not via pSim
    Cec_IncrSimReset( p );
    Cec_IncrSimCollectSources( p, vSimInfo );
    nDirty = Cec_IncrSimComputeTfo( p );
    if ( nDirty > p->nMaxDirty )
        p->nMaxDirty = nDirty;
    // gate: a wide cone is cheaper to resimulate with the full bit-parallel sweep
    if ( (ABC_INT64_T)nDirty * CEC_INCRSIM_FRAC_DEN >
         (ABC_INT64_T)p->nFrames * p->nObjs * CEC_INCRSIM_FRAC_NUM )
    {
        p->nBatchFull++;
        return 0;
    }
    p->nBatchLocal++;
    Cec_IncrSimEvaluate( p );
    // refine frame by frame; vDirtyKeys is sorted, so equal-frame keys are
    // contiguous and frame increases monotonically.
    iLo = 0;
    while ( iLo < Vec_IntSize(p->vDirtyKeys) )
    {
        int frame = Vec_IntEntry(p->vDirtyKeys, iLo) / p->nObjs;
        int iHi = iLo;
        while ( iHi < Vec_IntSize(p->vDirtyKeys) &&
                Vec_IntEntry(p->vDirtyKeys, iHi) / p->nObjs == frame )
            iHi++;
        Cec_IncrSimRefineFrame( p, frame, iLo, iHi );
        iLo = iHi;
    }
    return 1;
}

// Resets the per-resim-call profile counters; the host calls this once before
// the batch loop so the -w numbers are per-iteration, not cumulative.
void Cec_IncrSimBeginCall( Cec_IncrSim_t * p )
{
    p->nBatchLocal = p->nBatchFull = p->nMaxDirty = 0;
}
int Cec_IncrSimNumLocal( Cec_IncrSim_t * p ) { return p->nBatchLocal; }
int Cec_IncrSimNumFull ( Cec_IncrSim_t * p ) { return p->nBatchFull; }
int Cec_IncrSimNumDirty( Cec_IncrSim_t * p ) { return p->nMaxDirty; }
int Cec_IncrSimNumKeys ( Cec_IncrSim_t * p ) { return p->nFrames * p->nObjs; }

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
