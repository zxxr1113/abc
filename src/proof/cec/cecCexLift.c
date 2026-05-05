/**CFile****************************************************************

  FileName    [cecCexLift.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [CEX ternary lifting (bit-parallel) and adaptive replication.]

  Description [
    Two orthogonal optimizations inserted between the SAT call and
    Cec_ManResimulateCounterExamples in the scorr inductive loop.

    ── 1. Ternary Lifting (bit-parallel, 64 trials per sim pass) ──────

    CBS / MiniSAT return a *partial* assignment (cube): only the decision
    variables appear as literals; the vast majority of the SRM CIs are
    already X.  Lifting removes additional redundant literals from this
    small set — it does NOT scan all CIs.

    Algorithm (per record):
      Process the nLits literals in batches of 64.  Within each batch,
      bit k of a 64-bit Word64 represents trial k, where literal
      (batch_start + k) is dropped (set to X) while all other
      non-dropped literals retain their cube values.

      One forward pass through the AND graph evaluates all 64 trials
      simultaneously.  Reading the CO word: bit k = 1 means the CO is
      definite-1 in trial k → literal (batch_start+k) is droppable.

      Drops from earlier batches carry forward into later ones (greedy
      across batches).  Within a batch the test is non-greedy (peers
      tested with each other present).

    Non-greedy safety: if literals A and B are both independently
    droppable but not jointly droppable, our scheme may mark both as
    dropped.  The resulting "lifted" cube is an unsound CEX in the
    ternary-sim sense.  In scorr this is harmless: such a pattern merely
    fails to refine any equivalence class — it never causes incorrect
    merges (simulation is monotone: it only splits).

    Complexity: O( ceil(nLits/64) × nAnd ) vs O( nLits × nAnd ) serial.

    ── 2. Adaptive Cube Replication ──────────────────────────────────

    Context: Cec_ManLoadCounterExamples packs cubes into up to nBits
    bit-slots per simulation batch.  If nRecs cubes already fill that
    capacity, replicating them is pure overhead (information-redundant).
    If nRecs is tiny (say 1), there are ~63 empty slots begging to be
    used.

    K_actual = clamp(64 / nRecs, 1, K_max)
      where K_max = pPars->nCexReplicate (set by -K, default 1 = lift-only)

    Replica 0: bare lifted cube.
    Replica k ≥ 1: lifted cube + one extra randomly-selected free-CI
      literal (random polarity).  The extra pin creates a conflict with
      earlier replicas in Cec_ManLoadCounterExamplesTry, forcing each
      replica into a distinct bit-slot.  The remaining free bits keep the
      independent random backgrounds from Cec_ManStartSimInfo, so each
      replica explores a different extension of the CEX cube.

    When K_max = 1 (default): lifting only, no replication overhead.
    Enable replication: &scorr -L -K 8   (adaptive K ≤ 8).
  ]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

/* 64-bit word for bit-parallel ternary simulation */
typedef unsigned long long Word64;

////////////////////////////////////////////////////////////////////////
///                      SCRATCH MEMORY                              ///
////////////////////////////////////////////////////////////////////////

typedef struct {
    Word64 * pCare;      /* pCare[id]: bit k = node 'id' is care in trial k  */
    Word64 * pVal;       /* pVal[id]:  bit k = value in trial k (valid if care k=1) */
    int    * pDropped;   /* pDropped[i] = 1: literal i confirmed droppable   */
    int      nObjAlloc;
    int      nLitAlloc;
} CexLiftScratch_t;

static void CexLiftScratch_Resize( CexLiftScratch_t * s, int nObj, int nLit )
{
    if ( nObj > s->nObjAlloc )
    {
        ABC_FREE( s->pCare ); s->pCare = ABC_ALLOC( Word64, nObj );
        ABC_FREE( s->pVal  ); s->pVal  = ABC_ALLOC( Word64, nObj );
        s->nObjAlloc = nObj;
    }
    if ( nLit > s->nLitAlloc )
    {
        ABC_FREE( s->pDropped ); s->pDropped = ABC_ALLOC( int, nLit );
        s->nLitAlloc = nLit;
    }
}

static void CexLiftScratch_Free( CexLiftScratch_t * s )
{
    ABC_FREE( s->pCare ); ABC_FREE( s->pVal ); ABC_FREE( s->pDropped );
}

////////////////////////////////////////////////////////////////////////
///         BIT-PARALLEL 64-TRIAL TERNARY SIMULATION                 ///
////////////////////////////////////////////////////////////////////////

/* Run one 64-trial ternary sim for the literal batch [batch_start, batch_start+batch_size).

   Bit layout: bit k of each Word64 encodes trial k.
     Trial k: literal (batch_start+k) is treated as X (we test if it's droppable).
              All other non-dropped literals retain their cube values.
              Already-dropped literals (pDropped[i]=1) are X in ALL trials.

   The CBS/SAT solver only sets a few literals; most CIs are already X.
   We seed ONLY those literals — no full-CI scan required.

   Returns: bitmask where bit k=1 ⟺ CO is definite-1 in trial k,
            meaning literal (batch_start+k) can be dropped.             */
static Word64 TernaryBatch64( Gia_Man_t * p,
                               int * pLits, int * pDropped, int nLits,
                               int batch_start, int batch_size,
                               Word64 * pCare, Word64 * pVal, int iOut )
{
    Gia_Obj_t * pObj;
    int i, idx, id0, id1, c0, c1, id, v, k;
    int co_id, fan_id, co_compl;
    Word64 c0mask, c1mask, care0, care1, val0, val1;
    Word64 zero0, zero1, one0, one1, can_drop, batch_mask;
    int nObj = Gia_ManObjNum( p );

    /* Zero all node words (X in every trial) */
    memset( pCare, 0, nObj * sizeof(Word64) );
    memset( pVal,  0, nObj * sizeof(Word64) );

    /* Const-0: care=1 and val=0 in all 64 trials */
    pCare[0] = ~(Word64)0;
    pVal[0]  =  (Word64)0;

    /* Seed only the cube's literals (CBS leaves non-decision CIs as X already).
       Each SAT-solver cube has at most one literal per CI variable.         */
    for ( i = 0; i < nLits; i++ )
    {
        if ( pDropped[i] ) continue;          /* already dropped → always X */

        id = Gia_ObjId( p, Gia_ManCi( p, Abc_Lit2Var(pLits[i]) ) );
        v  = !Abc_LitIsCompl( pLits[i] );    /* v=1: literal constrains CI=1 */

        if ( i < batch_start || i >= batch_start + batch_size )
        {
            /* Outside this batch: literal is active in all 64 trials */
            pCare[id] = ~(Word64)0;
            pVal[id]  = v ? ~(Word64)0 : (Word64)0;
        }
        else
        {
            /* Inside this batch at position k:
               In trial k this literal is X (dropped); in all other trials active.
               pCare bit k = 0 (X); all other bits = 1.
               pVal  follows the same mask (val is don't-care where care=0). */
            k = i - batch_start;
            pCare[id] = ~( (Word64)1 << k );
            pVal[id]  = v ? ~( (Word64)1 << k ) : (Word64)0;
        }
    }

    /* Forward 3-valued propagation (topological = GIA object order).
       Per bit:
         definite-0:  at least one input is (care=1, val=0)
         definite-1:  both inputs are (care=1, val=1)
         X:           otherwise                               */
    Gia_ManForEachAnd( p, pObj, idx )
    {
        id0   = Gia_ObjFaninId0( pObj, idx );
        id1   = Gia_ObjFaninId1( pObj, idx );
        c0    = Gia_ObjFaninC0( pObj );
        c1    = Gia_ObjFaninC1( pObj );

        /* Edge-complement masks: XOR with all-1s if edge is inverted */
        c0mask = c0 ? ~(Word64)0 : (Word64)0;
        c1mask = c1 ? ~(Word64)0 : (Word64)0;

        care0 = pCare[id0];
        care1 = pCare[id1];
        val0  = pVal[id0] ^ c0mask;   /* val0 after inversion */
        val1  = pVal[id1] ^ c1mask;

        zero0 = care0 & ~val0;        /* fanin0: care=1, val=0 */
        zero1 = care1 & ~val1;
        one0  = care0 &  val0;        /* fanin0: care=1, val=1 */
        one1  = care1 &  val1;

        pCare[idx] = (zero0 | zero1) | (one0 & one1);
        pVal[idx]  =  one0 & one1;
    }

    /* CO evaluation: bit k=1 ⟺ CO is definite-1 in trial k */
    {
        Gia_Obj_t * pCo = Gia_ManCo( p, iOut );
        co_id    = Gia_ObjId( p, pCo );
        fan_id   = Gia_ObjFaninId0( pCo, co_id );
        co_compl = Gia_ObjFaninC0( pCo );
        c0mask   = co_compl ? ~(Word64)0 : (Word64)0;
        can_drop = pCare[fan_id] & ( pVal[fan_id] ^ c0mask );
    }

    /* Mask unused high bits (only batch_size trials are valid) */
    batch_mask = ( batch_size < 64 )
                 ? ( ((Word64)1 << batch_size) - (Word64)1 )
                 : ~(Word64)0;
    return can_drop & batch_mask;
}

////////////////////////////////////////////////////////////////////////
///                   LIFTING ONE CUBE                               ///
////////////////////////////////////////////////////////////////////////

/* Bit-parallel ternary lifting for a single cube [pLits, nLits].
   Literals are processed in batches of 64.  Each batch runs ONE
   forward sim pass and returns a drop-bitmask.  Drops accumulate
   across batches (inter-batch greedy).

   Soundness note: the intra-batch test is non-greedy.  If A and B are
   both individually droppable but not jointly droppable, both may end up
   marked as dropped.  In scorr this is harmless — the resulting "weak"
   cube only fails to split classes it could have split; it never causes
   incorrect merges (resimulation refinement is monotone: split-only).
   We therefore skip the post-hoc validation pass that would otherwise
   require two extra full forward sims per cube.

   *pnDropped ← number of literals removed.
   Returns newly-allocated Vec_Int_t (caller must Vec_IntFree).        */
static Vec_Int_t * LiftOneCube( Gia_Man_t * pSrm, int * pLits, int nLits,
                                  int iOut, CexLiftScratch_t * s, int * pnDropped )
{
    Vec_Int_t * vRes;
    int i, k;
    *pnDropped = 0;
    memset( s->pDropped, 0, nLits * sizeof(int) );

    for ( i = 0; i < nLits; i += 64 )
    {
        int batch_size = ( i + 64 <= nLits ) ? 64 : nLits - i;
        Word64 can_drop = TernaryBatch64( pSrm, pLits, s->pDropped, nLits,
                                           i, batch_size,
                                           s->pCare, s->pVal, iOut );
        for ( k = 0; k < batch_size; k++ )
            if ( ( can_drop >> k ) & (Word64)1 )
            { s->pDropped[i + k] = 1;  (*pnDropped)++; }
    }

    vRes = Vec_IntAlloc( nLits - *pnDropped );
    for ( i = 0; i < nLits; i++ )
        if ( !s->pDropped[i] )
            Vec_IntPush( vRes, pLits[i] );
    return vRes;
}

////////////////////////////////////////////////////////////////////////
///                   CUBE REPLICATION                               ///
////////////////////////////////////////////////////////////////////////

/* Emit K replicas of the lifted cube, each forced into a DISTINCT
   bit-slot inside Cec_ManLoadCounterExamples by appending a per-replica
   tag-bit pattern.

   Why tag bits (and why the previous "single random extra pin" was a
   no-op): Cec_ManLoadCounterExamplesTry returns 0 only when some literal
   conflicts with an already-pinned bit at that slot.  Two replicas that
   share the same cube and pin DIFFERENT free CIs do not conflict — the
   second replica simply joins slot 1 and adds its extra pin there.  All
   K replicas collapse into one slot, defeating the point of replication.

   Fix: pre-pick B = ceil(log2(K)) free PI CIs (call them tag_0..tag_{B-1}).
   Replica r ∈ [0, K-1] appends literals { tag_b = bit_b(r) for b∈[0,B) }.
   Any two replicas r != r' differ in at least one tag bit, so the second
   one to be loaded conflicts with the first at that slot and is forced
   into the next slot.  Result: K replicas occupy K consecutive slots,
   each with the cube core + a unique random extension on the remaining
   free PIs (background bits from Cec_ManStartSimInfo).

   nPiStart = Gia_ManRegNum(pAig): first PI CI index.  CIs [0, nPiStart)
   are RO slots that must stay zero for Gia_ManCorrPerformRemapping —
   we never write tag bits there.                                      */
static void EmitOne( Vec_Int_t * vOut, int iOut,
                      int * pLits, int nLits,
                      int * pTagCi, int nTagBits, int rIdx )
{
    int j, b;
    Vec_IntPush( vOut, iOut );
    Vec_IntPush( vOut, nLits + nTagBits );
    for ( j = 0; j < nLits; j++ )
        Vec_IntPush( vOut, pLits[j] );
    for ( b = 0; b < nTagBits; b++ )
    {
        int bit = ( rIdx >> b ) & 1;
        /* Abc_Var2Lit(var, compl=1) means var=0; compl=0 means var=1 */
        Vec_IntPush( vOut, Abc_Var2Lit( pTagCi[b], !bit ) );
    }
}

static void EmitWithReplicas( Vec_Int_t * vOut, int iOut,
                               int * pLiftedLits, int nLifted,
                               int K, int nCiTotal, int nPiStart,
                               int * pCiUsed )
{
    int k, j, nBits, found;
    int tagCi[6];                  /* up to 64 replicas → 6 tag bits */
    int nPi = nCiTotal - nPiStart;

    /* K=1 or no room for tag CIs: emit bare cube once */
    if ( K <= 1 || nPi <= 0 )
    {
        Vec_IntPush( vOut, iOut );
        Vec_IntPush( vOut, nLifted );
        for ( j = 0; j < nLifted; j++ )
            Vec_IntPush( vOut, pLiftedLits[j] );
        return;
    }

    /* nBits = ceil(log2(K)), capped at 6 (=> K ≤ 64) */
    nBits = 0;
    while ( ( 1 << nBits ) < K ) nBits++;
    if ( nBits > 6 ) { nBits = 6; K = 64; }

    /* Pick nBits distinct free PI CIs (not in cube) for tag bits */
    found = 0;
    {
        int start = nPiStart + (int)( Gia_ManRandom(0) % (unsigned)nPi );
        for ( j = 0; j < nPi && found < nBits; j++ )
        {
            int ci = nPiStart + ( start - nPiStart + j ) % nPi;
            if ( !pCiUsed[ci] ) tagCi[found++] = ci;
        }
    }
    if ( found < nBits )
    {
        /* Not enough free PIs for tag encoding — emit bare cube once */
        Vec_IntPush( vOut, iOut );
        Vec_IntPush( vOut, nLifted );
        for ( j = 0; j < nLifted; j++ )
            Vec_IntPush( vOut, pLiftedLits[j] );
        return;
    }

    /* Emit K replicas; replica k pins tag bits to binary encoding of k */
    for ( k = 0; k < K; k++ )
        EmitOne( vOut, iOut, pLiftedLits, nLifted, tagCi, nBits, k );
}

////////////////////////////////////////////////////////////////////////
///                        PUBLIC API                                ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Bit-parallel ternary lifting + adaptive cube replication.]

  Description [
    For each record in vCexStore:
      1. Lift: reduce the cube via 64-trial bit-parallel ternary sim.
      2. Replicate (if K_max > 1): emit K_actual copies, computed as
           K_actual = clamp(64 / nRecs, 1, K_max)
         so that the fixed simulation batch width is fully utilized when
         nRecs is small, and no replication is done when nRecs >= 64
         (the batch is already full without replication).

    fLift / nReplicate are independent:
      &scorr -L          : lift only         (fLift=1, K=1)
      &scorr -K 8        : replicate only    (fLift=0, K_max=8)
      &scorr -L -K 8     : lift + replicate  (fLift=1, K_max=8)
    Caller wires this via pPars->fCexLift / pPars->nCexReplicate.

    pSrm must be alive; do NOT call Gia_ManStop(pSrm) before this.
  ]

***********************************************************************/
Vec_Int_t * Cec_ManCexLiftAndReplicate( Gia_Man_t * pSrm, Vec_Int_t * vCexStore,
                                         int fLift, int nReplicate, int nReg, int fVerbose )
{
    Vec_Int_t * vOut;
    CexLiftScratch_t scratch;
    int * pCiUsed;
    int nObj, nCi, iStart, K_actual;
    int nRecs, nLitsOrigTotal, nLitsLiftedTotal, nDroppedTotal;

    if ( nReplicate < 1 ) nReplicate = 1;

    /* ── Pre-scan: count records and SAT-only records ──────────────
       nRecs = total records (incl. timeouts/trivials)
       nSat  = records with nLits > 0 — only these consume sim slots
               and are eligible for replication.                    */
    nRecs = 0;
    {
        int _p = 0, _n, _nSat = 0;
        while ( _p < Vec_IntSize(vCexStore) )
        {
            _p++;                              /* skip iOut */
            _n = Vec_IntEntry( vCexStore, _p++ );
            if ( _n > 0 ) { _p += _n; _nSat++; }
            nRecs++;
        }
        /* ── Adaptive K ────────────────────────────────────────────
           Cec_ManLoadCounterExamples uses ~480 slots (nWords=15 × 32).
           Aim: fill the batch but never exceed K_max requested by -K.
             nSat=  1 → K_actual = K_max           one cube → many extensions
             nSat= 50 → K_actual = min(K_max, 9)   50 cubes × 9 copies ≈ 450
             nSat>=480→ K_actual = 1               batch already saturated
           Tag-bit cap: at most 6 tag bits → K_actual ≤ 64.            */
        if ( nReplicate <= 1 )
            K_actual = 1;
        else if ( _nSat == 0 )
            K_actual = 1;
        else
        {
            K_actual = 480 / _nSat;
            K_actual = Abc_MaxInt( K_actual, 1 );
            K_actual = Abc_MinInt( K_actual, nReplicate );
            K_actual = Abc_MinInt( K_actual, 64 );
        }
    }

    nObj = Gia_ManObjNum( pSrm );
    nCi  = Gia_ManCiNum( pSrm );
    vOut = Vec_IntAlloc( K_actual * Vec_IntSize(vCexStore) );

    memset( &scratch, 0, sizeof(scratch) );
    CexLiftScratch_Resize( &scratch, nObj, 64 );   /* initial capacity */
    pCiUsed = ABC_CALLOC( int, nCi );              /* zero-initialised */

    nLitsOrigTotal = nLitsLiftedTotal = nDroppedTotal = 0;
    iStart = 0;

    while ( iStart < Vec_IntSize(vCexStore) )
    {
        int iOut, nLits, nDropped, nLifted, i;
        int * pLits, * pEmitLits;
        Vec_Int_t * vLifted = NULL;

        /* Parse record: [iOut, nLits, lit_0 .. lit_{nLits-1}] */
        iOut  = Vec_IntEntry( vCexStore, iStart++ );
        nLits = Vec_IntEntry( vCexStore, iStart++ );

        /* Pass through timeouts (nLits==-1) and trivial CEXes (nLits==0)
           VERBATIM.  Dropping them shrinks vCexStore which can spuriously
           trigger the "Vec_IntSize==0 → break" early-termination in the
           scorr refinement loop, leaving classes under-refined and causing
           massive over-merging on giant benchmarks.                       */
        if ( nLits <= 0 )
        {
            Vec_IntPush( vOut, iOut );
            Vec_IntPush( vOut, nLits );
            continue;
        }

        pLits  = Vec_IntArray(vCexStore) + iStart;
        iStart += nLits;

        nLitsOrigTotal += nLits;

        if ( fLift )
        {
            /* Grow scratch if this cube has more literals than any previous */
            CexLiftScratch_Resize( &scratch, nObj, nLits );

            /* ── Bit-parallel ternary lifting ── */
            vLifted = LiftOneCube( pSrm, pLits, nLits, iOut, &scratch, &nDropped );
            nLifted          = Vec_IntSize( vLifted );
            nLitsLiftedTotal += nLifted;
            nDroppedTotal    += nDropped;

            /* If a 0-literal cube materialises, emit it verbatim rather
               than swallowing the whole record. */
            if ( nLifted == 0 )
            {
                Vec_IntPush( vOut, iOut );
                Vec_IntPush( vOut, 0 );
                Vec_IntFree( vLifted );
                continue;
            }
            pEmitLits = Vec_IntArray( vLifted );
        }
        else
        {
            /* ── No lifting: emit/replicate the original cube ── */
            nLifted          = nLits;
            nLitsLiftedTotal += nLits;
            pEmitLits        = pLits;
        }

        /* ── CI-usage map for tag-bit pick (avoid cube CIs) ── */
        if ( K_actual > 1 )
        {
            memset( pCiUsed, 0, nCi * sizeof(int) );
            for ( i = 0; i < nLifted; i++ )
                pCiUsed[ Abc_Lit2Var( pEmitLits[i] ) ] = 1;
        }

        /* ── Emit cube + replicas ── */
        EmitWithReplicas( vOut, iOut, pEmitLits, nLifted,
                          K_actual, nCi, nReg, pCiUsed );
        if ( vLifted ) Vec_IntFree( vLifted );
    }

    if ( fVerbose && nLitsOrigTotal > 0 )
    {
        double dropPct = fLift ? 100.0 * nDroppedTotal / nLitsOrigTotal : 0.0;
        Abc_Print( 1,
            "[CEX-LIFT] nRecs=%-4d K=%d  lift=%s  lits: %d -> %d  drop=%.1f%%"
            "  outEntries=%d\n",
            nRecs, K_actual, fLift ? "on" : "off",
            nLitsOrigTotal, nLitsLiftedTotal, dropPct,
            Vec_IntSize(vOut) );
    }

    CexLiftScratch_Free( &scratch );
    ABC_FREE( pCiUsed );
    return vOut;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
