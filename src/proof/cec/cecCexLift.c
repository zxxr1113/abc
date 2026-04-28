/**CFile****************************************************************

  FileName    [cecCexLift.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [CEX ternary lifting and cube replication for &scorr.]

  Description [
    Two orthogonal optimizations applied after each SAT call in the scorr
    inductive loop:

    1. Ternary Lifting  — 3-valued simulation on the (combinational) SRM
       shrinks each SAT-returned cube to a near-minimal subset that still
       causes the target CO to evaluate to definite-1.  Smaller cubes
       leave more free CI positions whose random backgrounds (set by
       Cec_ManStartSimInfo) cover a wider part of the state space.

    2. Cube Replication — each lifted cube is emitted nReplicate times in
       the output vCexStore.  Replicas k >= 1 each carry one additional
       randomly-pinned free-CI literal so they are forced into distinct
       bit-slots by Cec_ManLoadCounterExamplesTry.  The remaining free
       positions retain the distinct random values pre-filled by
       Cec_ManStartSimInfo, giving nReplicate independent trajectories
       through the original AIG during sequential re-simulation.

    Both steps are transparent to the caller: the output has the same
    vCexStore format as the SAT solver output, and is fed directly into
    Cec_ManResimulateCounterExamples.

    Note on CBS (circuit SAT) solver: CBS already leaves most CI bits
    unset (they receive random fill later).  The ternary sim works only
    on the literals explicitly present in vCexStore, so unset CIs are
    naturally represented as X — no extra work needed.

    Note on multi-cube conflict: Cec_ManLoadCounterExamplesTry uses
    per-slot conflict detection (vPres bitmask).  Multiple cubes that
    constrain the same CI to different values land in different slots
    automatically.  Replication does NOT bypass this check.
  ]

  Author      [Alan Mishchenko / cex_lifting branch]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

/* Scratch arrays reused across cubes (allocated once, passed by pointer) */
typedef struct CexLiftScratch_t_ {
    int * pCare;     /* care[id]=1 iff node id has a determined value   */
    int * pVal;      /* val[id]   — valid only when care[id]=1          */
    int * pActive;   /* active[i]=1 iff literal i is still in the cube  */
    int   nObjAlloc; /* capacity of pCare / pVal                        */
    int   nLitAlloc; /* capacity of pActive                             */
} CexLiftScratch_t;

static void CexLiftScratch_Resize( CexLiftScratch_t * s, int nObj, int nLit )
{
    if ( nObj > s->nObjAlloc )
    {
        ABC_FREE( s->pCare );
        ABC_FREE( s->pVal );
        s->pCare     = ABC_ALLOC( int, nObj );
        s->pVal      = ABC_ALLOC( int, nObj );
        s->nObjAlloc = nObj;
    }
    if ( nLit > s->nLitAlloc )
    {
        ABC_FREE( s->pActive );
        s->pActive   = ABC_ALLOC( int, nLit );
        s->nLitAlloc = nLit;
    }
}

static void CexLiftScratch_Free( CexLiftScratch_t * s )
{
    ABC_FREE( s->pCare );
    ABC_FREE( s->pVal );
    ABC_FREE( s->pActive );
}

////////////////////////////////////////////////////////////////////////
///                   TERNARY SIMULATION HELPERS                     ///
////////////////////////////////////////////////////////////////////////

/* Initialise pCare/pVal from the currently-active subset of cube lits.
   Const0 (obj id=0) is always care=1, val=0.
   CIs in the active set: care=1, val = !compl.
   All other nodes: care=0 (X). */
static void TernarySeed( Gia_Man_t * p, int * pCare, int * pVal,
                          int * pActive, int * pLits, int nLits )
{
    int i, id;
    memset( pCare, 0, Gia_ManObjNum(p) * sizeof(int) );
    memset( pVal,  0, Gia_ManObjNum(p) * sizeof(int) );
    /* const-0 is always determined */
    pCare[0] = 1;  pVal[0] = 0;
    /* set each active cube literal */
    for ( i = 0; i < nLits; i++ )
    {
        if ( !pActive[i] ) continue;
        id = Gia_ObjId( p, Gia_ManCi( p, Abc_Lit2Var(pLits[i]) ) );
        pCare[id] = 1;
        pVal[id]  = !Abc_LitIsCompl( pLits[i] );  /* compl=1 => ci=0 */
    }
}

/* Forward 3-valued propagation through all AND nodes (topological order).
   GIA stores objects in topological order, so a single forward pass suffices. */
static void TernaryPropagate( Gia_Man_t * p, int * pCare, int * pVal )
{
    Gia_Obj_t * pObj;
    int i, id0, id1, c0, c1, care0, care1, val0, val1;
    Gia_ManForEachAnd( p, pObj, i )
    {
        /* Obtain fanin IDs and complement bits */
        id0   = Gia_ObjFaninId0( pObj, i );
        id1   = Gia_ObjFaninId1( pObj, i );
        c0    = Gia_ObjFaninC0( pObj );
        c1    = Gia_ObjFaninC1( pObj );
        care0 = pCare[id0];
        care1 = pCare[id1];
        /* Apply edge complement to get post-edge values */
        val0  = care0 ? ( pVal[id0] ^ c0 ) : 0;
        val1  = care1 ? ( pVal[id1] ^ c1 ) : 0;
        /*
         * 3-valued AND:
         *   0 & X = 0 (care)     <- one definite 0 absorbs
         *   X & 0 = 0 (care)
         *   1 & 1 = 1 (care)     <- both definite 1
         *   otherwise  = X       <- at least one unknown, no definite 0
         */
        if ( care0 && val0 == 0 )
        {
            pCare[i] = 1;  pVal[i] = 0;
        }
        else if ( care1 && val1 == 0 )
        {
            pCare[i] = 1;  pVal[i] = 0;
        }
        else if ( care0 && care1 )
        {
            /* Both are definite 1 (the only remaining case) */
            pCare[i] = 1;  pVal[i] = 1;
        }
        else
        {
            pCare[i] = 0;  pVal[i] = 0;  /* X */
        }
    }
}

/* Return 1 iff CO iOut evaluates to definite 1 under current pCare/pVal. */
static int TernaryCheckCo( Gia_Man_t * p, int * pCare, int * pVal, int iOut )
{
    Gia_Obj_t * pCo = Gia_ManCo( p, iOut );
    int co_id   = Gia_ObjId( p, pCo );
    int fan_id  = Gia_ObjFaninId0( pCo, co_id );
    int compl   = Gia_ObjFaninC0( pCo );
    int care    = pCare[fan_id];
    int val     = care ? ( pVal[fan_id] ^ compl ) : 0;
    return ( care && val );
}

////////////////////////////////////////////////////////////////////////
///                      LIFTING ONE CUBE                            ///
////////////////////////////////////////////////////////////////////////

/* Greedy ternary lift for a single cube record.
   pLits[0..nLits-1]: literals from vCexStore.
   iOut            : SRM CO index that must stay at definite-1.
   s               : scratch (pre-allocated, capacity >= nObj, nLits).
   *pnDropped      : OUT — number of literals removed.

   Returns a newly-allocated Vec_Int_t with the surviving literals.
   The caller must free it.  On assertion failure (original cube
   doesn't satisfy the CO) the original literal set is returned unchanged
   and *pnDropped = 0. */
static Vec_Int_t * LiftOneCube( Gia_Man_t * pSrm, int * pLits, int nLits,
                                 int iOut, CexLiftScratch_t * s, int * pnDropped )
{
    int i;
    Vec_Int_t * vRes;
    *pnDropped = 0;

    /* Initialise all literals as active */
    for ( i = 0; i < nLits; i++ ) s->pActive[i] = 1;

    /* Verify that the original cube already satisfies the CO */
    TernarySeed( pSrm, s->pCare, s->pVal, s->pActive, pLits, nLits );
    TernaryPropagate( pSrm, s->pCare, s->pVal );
    if ( !TernaryCheckCo( pSrm, s->pCare, s->pVal, iOut ) )
    {
        /* Defensive: should never happen if the SAT solver is correct */
        vRes = Vec_IntAlloc( nLits );
        for ( i = 0; i < nLits; i++ ) Vec_IntPush( vRes, pLits[i] );
        return vRes;
    }

    /* Greedy dropping: try each literal; if the CO still holds after
       removing it, drop it permanently.  The permanent drop is carried
       over to subsequent trials (greedy, not exhaustive). */
    for ( i = 0; i < nLits; i++ )
    {
        s->pActive[i] = 0;   /* tentatively drop literal i */
        TernarySeed( pSrm, s->pCare, s->pVal, s->pActive, pLits, nLits );
        TernaryPropagate( pSrm, s->pCare, s->pVal );
        if ( TernaryCheckCo( pSrm, s->pCare, s->pVal, iOut ) )
        {
            (*pnDropped)++;  /* keep dropped permanently */
        }
        else
        {
            s->pActive[i] = 1;  /* must keep: restore for subsequent trials */
        }
    }

    /* Build result from surviving active literals */
    vRes = Vec_IntAlloc( nLits - *pnDropped );
    for ( i = 0; i < nLits; i++ )
        if ( s->pActive[i] )
            Vec_IntPush( vRes, pLits[i] );
    return vRes;
}

////////////////////////////////////////////////////////////////////////
///                   REPLICATION HELPER                             ///
////////////////////////////////////////////////////////////////////////

/* Emit the base lifted cube into vOut, then emit (nReplicate-1) replicas.
   Each replica k >= 1 carries one additional randomly-selected free-CI
   literal (random polarity).  This extra literal makes the replica
   distinct from earlier entries in vCexStore, so Cec_ManLoadCounterExamplesTry
   places it in a different bit-slot from the base cube and earlier replicas.
   The remaining free bits keep the distinct random backgrounds already
   written by Cec_ManStartSimInfo — no explicit random extension needed here.

   pLiftedLits[0..nLifted-1] : the minimised cube literals.
   nCiTotal                  : total CI count of pSrm (= Gia_ManCiNum(pSrm)).
   pCiUsed[ci]               : 1 if CI index ci is already in the lifted cube. */
static void EmitWithReplicas( Vec_Int_t * vOut, int iOut,
                               int * pLiftedLits, int nLifted,
                               int nReplicate, int nCiTotal, int * pCiUsed )
{
    int k, j, freeIdx, freeCi, freeVal, nFree;

    /* Count free CIs for quick check */
    nFree = nCiTotal - nLifted;  /* rough upper bound; exact count not needed */

    /* Replica 0: the bare lifted cube */
    Vec_IntPush( vOut, iOut );
    Vec_IntPush( vOut, nLifted );
    for ( j = 0; j < nLifted; j++ )
        Vec_IntPush( vOut, pLiftedLits[j] );

    if ( nReplicate <= 1 || nFree <= 0 )
        return;

    /* Replicas 1 .. nReplicate-1: lifted cube + 1 random free-CI pin.
       The random pin makes each replica collide (in different slots) with
       earlier entries, so Cec_ManLoadCounterExamplesTry assigns distinct
       bit positions.  Using Gia_ManRandom(0) for both CI selection and
       polarity keeps this thread-local to the current ABC session. */
    for ( k = 1; k < nReplicate; k++ )
    {
        /* Pick a random free CI index.  Scan from a random offset to avoid
           always picking the same one when the free set is sparse. */
        freeCi = -1;
        freeIdx = (int)( Gia_ManRandom(0) % (unsigned)nCiTotal );
        {
            int tried;
            for ( tried = 0; tried < nCiTotal; tried++ )
            {
                int ci = ( freeIdx + tried ) % nCiTotal;
                if ( !pCiUsed[ci] )
                {
                    freeCi = ci;
                    break;
                }
            }
        }
        if ( freeCi < 0 )
            break;  /* all CIs are pinned — no room for extra literal */

        freeVal = (int)( Gia_ManRandom(0) & 1 );

        /* Emit replica: lifted lits + the extra free-CI literal */
        Vec_IntPush( vOut, iOut );
        Vec_IntPush( vOut, nLifted + 1 );
        for ( j = 0; j < nLifted; j++ )
            Vec_IntPush( vOut, pLiftedLits[j] );
        /* Abc_Var2Lit(var, compl): compl=1 means var=0, compl=0 means var=1 */
        Vec_IntPush( vOut, Abc_Var2Lit( freeCi, !freeVal ) );
    }
}

////////////////////////////////////////////////////////////////////////
///                          PUBLIC API                              ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Ternary-lift every CEX cube in vCexStore, optionally replicate.]

  Description [
    Iterates vCexStore records (format: [iOut, nLits, lit_0..lit_{nLits-1}]).
    For each record:
      1. 3-valued simulation on pSrm minimises the cube.
      2. The minimised cube is emitted nReplicate times; replicas k >= 1
         carry one extra randomly-pinned free-CI literal to force placement
         in distinct simulation bit-slots.

    Returns a newly-allocated Vec_Int_t in the same vCexStore format.
    The caller is responsible for Vec_IntFree().

    pSrm must still be alive when this function is called (Gia_ManStop
    must be deferred until after the call returns).

    nReplicate = 1 : lift only (no replication).
    nReplicate = 0 : treated as 1 (caller should use fCexLift=0 to bypass).
  ]

***********************************************************************/
Vec_Int_t * Cec_ManCexLiftAndReplicate( Gia_Man_t * pSrm, Vec_Int_t * vCexStore,
                                         int nReplicate, int fVerbose )
{
    Vec_Int_t * vOut;
    CexLiftScratch_t scratch;
    int * pCiUsed;
    int iStart, nObj, nCi, nReplMax;
    int nRecs, nLitsOrigTotal, nLitsLiftedTotal, nDroppedTotal;

    if ( nReplicate < 1 ) nReplicate = 1;
    nReplMax = nReplicate;

    nObj = Gia_ManObjNum( pSrm );
    nCi  = Gia_ManCiNum( pSrm );

    /* Output buffer: worst case is nReplMax * original size */
    vOut = Vec_IntAlloc( nReplMax * Vec_IntSize(vCexStore) );

    /* Scratch memory for ternary sim (resized lazily per cube) */
    memset( &scratch, 0, sizeof(scratch) );
    CexLiftScratch_Resize( &scratch, nObj, 64 );

    /* Per-CI usage map for replica generation */
    pCiUsed = ABC_CALLOC( int, nCi );

    nRecs = 0;  nLitsOrigTotal = 0;  nLitsLiftedTotal = 0;  nDroppedTotal = 0;

    iStart = 0;
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        int iOut, nLits, nDropped, nLifted, i;
        int * pLits;
        Vec_Int_t * vLifted;

        /* Parse one record: [iOut, nLits, lit_0 .. lit_{nLits-1}] */
        iOut  = Vec_IntEntry( vCexStore, iStart++ );
        nLits = Vec_IntEntry( vCexStore, iStart++ );

        if ( nLits <= 0 )
        {
            /* Empty cube — skip; don't replicate (no information content) */
            continue;
        }

        pLits  = Vec_IntArray(vCexStore) + iStart;
        iStart += nLits;

        nRecs++;
        nLitsOrigTotal += nLits;

        /* Resize scratch if this cube is larger than any seen so far */
        CexLiftScratch_Resize( &scratch, nObj, nLits );

        /* ---- Ternary lifting ---- */
        vLifted = LiftOneCube( pSrm, pLits, nLits, iOut, &scratch, &nDropped );
        nLifted = Vec_IntSize( vLifted );
        nLitsLiftedTotal += nLifted;
        nDroppedTotal    += nDropped;

        if ( nLifted == 0 )
        {
            /* Fully-free cube after lifting — useless for refinement; skip */
            Vec_IntFree( vLifted );
            continue;
        }

        /* ---- Build CI-usage map for this cube (for replica generation) ---- */
        memset( pCiUsed, 0, nCi * sizeof(int) );
        for ( i = 0; i < nLifted; i++ )
            pCiUsed[ Abc_Lit2Var( Vec_IntEntry(vLifted, i) ) ] = 1;

        /* ---- Emit lifted cube + replicas ---- */
        EmitWithReplicas( vOut, iOut,
                          Vec_IntArray(vLifted), nLifted,
                          nReplMax, nCi, pCiUsed );

        Vec_IntFree( vLifted );
    }

    /* Verbose summary */
    if ( fVerbose && nRecs > 0 )
    {
        double dropPct = nLitsOrigTotal > 0
            ? 100.0 * nDroppedTotal / nLitsOrigTotal : 0.0;
        Abc_Print( 1,
            "[CEX-LIFT] recs=%-4d  lits: %d -> %d  (drop=%.1f%%)  "
            "repl=%-2d  outRecs=%d\n",
            nRecs, nLitsOrigTotal, nLitsLiftedTotal, dropPct,
            nReplMax, Vec_IntSize(vOut) );
    }

    CexLiftScratch_Free( &scratch );
    ABC_FREE( pCiUsed );
    return vOut;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
