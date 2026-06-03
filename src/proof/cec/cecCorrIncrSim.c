/**CFile****************************************************************

  FileName    [cecCorrIncrSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Incremental local-simulation manager for &scorr (step 3).]

  Description [This file is the data-structure foundation of the
  incremental TFO-only resimulation planned in
  md/scorr_incremental_sim_design.md.  Step 3 implements only the cone
  bookkeeping: it ingests a vCexStore from the SAT loop, maps each CEX
  literal back to a (frame, objId) source on the original AIG, then walks
  the frame-aware TFO and records the set of (frame, objId) keys that
  would need re-evaluation if simulation were to run incrementally.

  Step 3 does NOT evaluate signatures or refine equivalence classes; the
  full Cec_ManResimulateCounterExamples still runs alongside this
  manager.  Its sole output is the dirty-cone size, surfaced via the -w
  profile so we can validate whether the cone is small enough for a
  later TFO-only evaluation pass to be worthwhile.]

  Author      [Xiran Zhao]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Jun 2026.]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline int Cec_IncrSimKey( Cec_IncrSim_t * p, int frame, int objId )
{
    return frame * p->nObjs + objId;
}

// Returns 1 if the key was newly marked; 0 if it was already dirty.
static inline int Cec_IncrSimMark( Cec_IncrSim_t * p, int frame, int objId )
{
    int key = Cec_IncrSimKey( p, frame, objId );
    if ( p->pMark[key] == p->nMarkVersion )
        return 0;
    p->pMark[key] = p->nMarkVersion;
    Vec_IntPush( p->vDirtyKeys, key );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Allocates the incremental local-sim manager.]

  Description [Builds the dense per-key mark array sized for nFrames *
  Gia_ManObjNum(pAig).  Requires static fanout on pAig for the TFO walk;
  if pAig does not already have it, builds and remembers to tear down on
  Free.  The host AIG must outlive the manager.]

  SideEffects [Builds static fanout on pAig if not already present.]

  SeeAlso     []

***********************************************************************/
Cec_IncrSim_t * Cec_IncrSimAlloc( Gia_Man_t * pAig, int nFrames )
{
    Cec_IncrSim_t * p = ABC_CALLOC( Cec_IncrSim_t, 1 );
    p->pAig    = pAig;
    p->nFrames = nFrames;
    p->nObjs   = Gia_ManObjNum( pAig );
    p->nPis    = Gia_ManPiNum( pAig );
    p->nRegs   = Gia_ManRegNum( pAig );
    // Dense mark array; zero-initialized so the first nMarkVersion==1 reset
    // distinguishes "never marked" from "marked in version 1".
    p->pMark        = ABC_CALLOC( int, (size_t)nFrames * p->nObjs );
    p->nMarkVersion = 0;
    p->vSources     = Vec_IntAlloc( 1024 );
    p->vDirtyKeys   = Vec_IntAlloc( 1024 );
    p->vQueue       = Vec_IntAlloc( 1024 );
    if ( pAig->vFanout == NULL )
    {
        Gia_ManStaticFanoutStart( pAig );
        p->fOwnsFanout = 1;
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the incremental local-sim manager.]

  SideEffects [If we built the static fanout in Alloc, tears it down.]

  SeeAlso     []

***********************************************************************/
void Cec_IncrSimFree( Cec_IncrSim_t * p )
{
    if ( p == NULL ) return;
    if ( p->fOwnsFanout )
        Gia_ManStaticFanoutStop( p->pAig );
    Vec_IntFreeP( &p->vSources );
    Vec_IntFreeP( &p->vDirtyKeys );
    Vec_IntFreeP( &p->vQueue );
    ABC_FREE( p->pMark );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Clears all per-batch state in O(1) via version bump.]

  Description [Called between CEX-store batches; leaves nMarkVersion
  monotonically increasing so per-key freshness checks are cheap.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_IncrSimReset( Cec_IncrSim_t * p )
{
    Vec_IntClear( p->vSources );
    Vec_IntClear( p->vDirtyKeys );
    Vec_IntClear( p->vQueue );
    p->nMarkVersion++;
    // Guard against integer overflow: on the (astronomically unlikely)
    // wrap-around, fall back to an explicit clear of the dense array.
    if ( p->nMarkVersion == 0 )
    {
        memset( p->pMark, 0, sizeof(int) * (size_t)p->nFrames * p->nObjs );
        p->nMarkVersion = 1;
    }
}

/**Function*************************************************************

  Synopsis    [Maps a CEX literal to (frame, objId) and marks it dirty.]

  Description [vSimInfo layout matches Cec_ManResimulateCounterExamples:
  the first nRegs slots are the initial ROs at frame 0, then nFrames
  groups of nPis primary inputs.  Out-of-range vars are clamped; this
  can happen when nFrames at resim time is smaller than the SAT
  unrolling depth used by Gia_ManCorrSpecReduce.]

  SideEffects [Pushes a key into vSources and vQueue on first mark.]

  SeeAlso     []

***********************************************************************/
static void Cec_IncrSimAddSourceFromVar( Cec_IncrSim_t * p, int var )
{
    int frame, objId;
    if ( var < p->nRegs )
    {
        frame = 0;
        objId = Gia_ObjId( p->pAig, Gia_ManRo( p->pAig, var ) );
    }
    else
    {
        int t = var - p->nRegs;
        int pi = t % p->nPis;
        frame = t / p->nPis;
        objId = Gia_ObjId( p->pAig, Gia_ManPi( p->pAig, pi ) );
    }
    if ( frame >= p->nFrames )
        return;
    if ( Cec_IncrSimMark( p, frame, objId ) )
    {
        int key = Cec_IncrSimKey( p, frame, objId );
        Vec_IntPush( p->vSources, key );
        Vec_IntPush( p->vQueue, key );
    }
}

/**Function*************************************************************

  Synopsis    [Injects all CEX literals from vCexStore as dirty sources.]

  Description [Scans the same encoding consumed by
  Cec_ManLoadCounterExamples: each entry is (Out, nLits, lits...).
  nLits==0 (trivial SAT) and nLits==-1 (timeout) carry no literals so
  they contribute no source; the dirty cone for those iterations stays
  empty unless other entries supply literals.]

  SideEffects [Mutates vSources / vQueue / pMark.]

  SeeAlso     []

***********************************************************************/
void Cec_IncrSimInjectCexStore( Cec_IncrSim_t * p, Vec_Int_t * vCexStore )
{
    int iStart = 0, nSize, k;
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        iStart++; // skip output number
        assert( iStart < Vec_IntSize(vCexStore) );
        nSize = Vec_IntEntry( vCexStore, iStart++ );
        if ( nSize <= 0 )
            continue;
        for ( k = 0; k < nSize; k++ )
        {
            int lit = Vec_IntEntry( vCexStore, iStart++ );
            Cec_IncrSimAddSourceFromVar( p, Abc_Lit2Var(lit) );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Frame-aware BFS over static fanouts from all queued sources.]

  Description [For each dirty (frame, objId):
                 - AND fanouts stay in the same frame;
                 - RI  fanouts cross to (frame+1, RoOf(RI)) when in range;
                 - PO  fanouts terminate -- POs are not class candidates.

               Returns the number of distinct dirty (frame, objId) keys
               recorded after the walk.]

  SideEffects [Drains vQueue.  vSources / vDirtyKeys hold the result.]

  SeeAlso     []

***********************************************************************/
int Cec_IncrSimComputeTfo( Cec_IncrSim_t * p )
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

int Cec_IncrSimNumSources( Cec_IncrSim_t * p ) { return Vec_IntSize( p->vSources ); }
int Cec_IncrSimNumDirty  ( Cec_IncrSim_t * p ) { return Vec_IntSize( p->vDirtyKeys ); }
int Cec_IncrSimNumKeys   ( Cec_IncrSim_t * p ) { return p->nFrames * p->nObjs; }

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
