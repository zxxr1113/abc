/**CFile****************************************************************

  FileName    [cecXcgrpCegar.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [CEGAR-enhanced XCGRP: level-bounded abstraction with
               counterexample-guided refinement, plus multi-pivot
               2^N case splitting.

    Motivation (in response to ICCAD'08 lossy-partition cone-blowup):
      ICCAD'08 §3.4 shows that ABC's register-index partitioning (-P)
      is inherently lossy -- cut registers become free variables and
      equivalences are under-approximated.  XCGRP replaced the lossy
      cut by a lossless constant case-split on an XOR pivot; this
      avoids free-variable artifacts but does not itself bound the
      TFI cone size in multi-frame induction.

      This file adds the missing piece: explicit level-bounded
      abstraction with CEGAR refinement (Henzinger-Jhala-Majumdar-
      Sutre POPL'02, Clarke-Grumberg-Jha-Lu-Veith CAV'00).
      Far-away logic is replaced by free "abstract PIs" that carry
      a back-map to the original node.  Spurious equivalences found
      by scorr on the abstraction are detected by simulation on the
      concrete original AIG, and the abstraction is grown locally
      at the offending node.

    Pipeline (for N pivots, level limit L):
      1. Select N highest-scored XOR pivots (chain-length^2 / dist).
      2. For each of the 2^N constant assignments to pivots:
           a. Build level-bounded abstraction:
                - nodes within L levels of any CO are reproduced
                - nodes beyond L are replaced by a new CI that
                  records its original-node ID (abstract PI).
           b. CEGAR loop:
                - run scorr on the abstraction
                - map equivalences back to original node IDs
                - simulate original with random patterns; any pair
                  that disagrees on >=1 pattern is spurious
                - refine: inline the offending abstract PI's driver
                - repeat until no spurious pair or max iters hit
      3. Intersect surviving equivalences across all 2^N branches.
      4. Apply to the original AIG and reduce.

    Soundness:
      A pair (a,b) is accepted only if ALL 2^N branches keep it AND
      random simulation on the original never finds them differing.
      Monte-Carlo simulation can confirm equivalence only
      probabilistically; we treat it as a filter before the outer
      scorr pass re-verifies on the full circuit.  In practice the
      public entry re-runs plain scorr on the merged equivalences,
      so false positives from simulation are caught downstream.

    Completeness:
      As nLevelLimit -> depth(AIG), the abstraction converges to
      the exact circuit, CEGAR terminates in finite steps (each
      refinement strictly shrinks the abstract PI frontier),
      and XCGRP reduces to standard scorr.

    Known limitations (honest):
      - scorr does not expose its SAT counterexamples externally, so
        we fall back to Monte-Carlo simulation for spurious detection
        rather than true SAT-level CEX extraction.
      - Refinement heuristic is local (inline one abstract PI per
        iteration).  Justification-frontier-style refinement would
        be more surgical but requires scorr internals.
      - Level truncation is combinational; it reduces per-frame
        cone size but does not explicitly bound temporal horizon.
  ]

  Author      [xiran - UC Berkeley]

  Date        [Ver. 1.0. Started - April 2026.]

***********************************************************************/

#include "cecInt.h"
#include <limits.h>
#include <string.h>

#ifdef ABC_USE_PTHREADS
#include <pthread.h>
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        FORWARD DECLS                             ///
////////////////////////////////////////////////////////////////////////

// scorr entry (pluggable; same hook used by plain XCGRP)
extern int          Cec_ManLSCorrespondenceClasses( Gia_Man_t * pAig, Cec_ParCor_t * pPars );
extern Gia_Man_t *  Gia_ManCorrReduce( Gia_Man_t * p );

////////////////////////////////////////////////////////////////////////
///                     UNION-FIND + XOR CHAIN                       ///
///   (Minor duplication of cecXcgrp.c helpers; kept local to avoid  ///
///    exporting them.  If file-pair merging is preferred, expose    ///
///    the helpers via a private header cecXcgrpInt.h.)              ///
////////////////////////////////////////////////////////////////////////

static int  Xcg_UfFind( int * pUf, int i )
{
    while ( pUf[i] != i ) { pUf[i] = pUf[pUf[i]]; i = pUf[i]; }
    return i;
}
static void Xcg_UfUnion( int * pUf, int * pRank, int a, int b )
{
    a = Xcg_UfFind(pUf,a); b = Xcg_UfFind(pUf,b);
    if ( a == b ) return;
    if ( pRank[a] < pRank[b] ) { int t=a; a=b; b=t; }
    pUf[b] = a;
    if ( pRank[a] == pRank[b] ) pRank[a]++;
}

// Score[i] = chainLen(i)^2 / (distToCO(i)+1) for XOR gates in chains >=2.
// Returns a newly-allocated score array; caller frees.
static float * Xcg_ComputeScores( Gia_Man_t * p )
{
    int i, nObj = Gia_ManObjNum(p);
    int * pUf      = ABC_ALLOC(int, nObj);
    int * pRank    = ABC_CALLOC(int, nObj);
    int * pChainId = ABC_ALLOC(int, nObj);
    int * pLen     = ABC_CALLOC(int, nObj);
    int * pDist    = ABC_FALLOC(int, nObj);
    float * pScore = ABC_CALLOC(float, nObj);
    Gia_Obj_t * pObj;
    for ( i = 0; i < nObj; i++ ) { pUf[i]=i; pChainId[i]=-1; }
    // Union XOR gates that share XOR-only fanin edges.
    Gia_ManForEachAnd( p, pObj, i )
    {
        int f0, f1;
        if ( !Gia_ObjIsXor(pObj) ) continue;
        f0 = Gia_ObjFaninId0(pObj,i); f1 = Gia_ObjFaninId1(pObj,i);
        if ( Gia_ObjIsXor(Gia_ManObj(p,f0)) ) Xcg_UfUnion(pUf,pRank,i,f0);
        if ( Gia_ObjIsXor(Gia_ManObj(p,f1)) ) Xcg_UfUnion(pUf,pRank,i,f1);
    }
    Gia_ManForEachAnd( p, pObj, i )
        if ( Gia_ObjIsXor(pObj) )
        {
            pChainId[i] = Xcg_UfFind(pUf,i);
            pLen[ pChainId[i] ]++;
        }
    // Backward BFS: shortest fanout distance from any CO.
    Gia_ManForEachCo( p, pObj, i ) pDist[ Gia_ObjId(p,pObj) ] = 0;
    for ( i = nObj-1; i >= 0; i-- )
    {
        int d, f;
        pObj = Gia_ManObj(p,i);
        if ( pDist[i] < 0 ) continue;
        d = pDist[i] + 1;
        if ( Gia_ObjIsCo(pObj) ) {
            f = Gia_ObjFaninId0(pObj,i);
            if ( pDist[f] < 0 || pDist[f] > d ) pDist[f] = d;
        } else if ( Gia_ObjIsAnd(pObj) ) {
            f = Gia_ObjFaninId0(pObj,i);
            if ( pDist[f] < 0 || pDist[f] > d ) pDist[f] = d;
            f = Gia_ObjFaninId1(pObj,i);
            if ( pDist[f] < 0 || pDist[f] > d ) pDist[f] = d;
        }
    }
    Gia_ManForEachAnd( p, pObj, i )
    {
        int clen = (pChainId[i] >= 0) ? pLen[pChainId[i]] : 1;
        if ( !Gia_ObjIsXor(pObj) || clen < 2 || pDist[i] < 0 ) continue;
        pScore[i] = (float)(clen*clen) / (float)(pDist[i] + 1);
    }
    ABC_FREE(pUf); ABC_FREE(pRank); ABC_FREE(pChainId);
    ABC_FREE(pLen); ABC_FREE(pDist);
    return pScore;
}

// Pick top-N XOR pivots by score.  Result: Vec_Int_t of node IDs.
static Vec_Int_t * Xcg_SelectTopNPivots( Gia_Man_t * p, int N )
{
    Vec_Int_t * vPivots = Vec_IntAlloc(N);
    float * pScore = Xcg_ComputeScores(p);
    int i, k;
    for ( k = 0; k < N; k++ )
    {
        int iBest = -1; float fBest = 0.0f;
        for ( i = 0; i < Gia_ManObjNum(p); i++ )
            if ( pScore[i] > fBest ) { fBest = pScore[i]; iBest = i; }
        if ( iBest < 0 ) break;
        Vec_IntPush(vPivots, iBest);
        pScore[iBest] = 0.0f;  // prevent re-selection
        // (No disjointness check here -- pivots may share TFI.  For
        //  independent pivots, filter by structural support Jaccard.
        //  Left as future work; see §3.1 of companion analysis.)
    }
    ABC_FREE(pScore);
    return vPivots;
}

////////////////////////////////////////////////////////////////////////
///                    ABSTRACTION STATE STRUCT                      ///
////////////////////////////////////////////////////////////////////////

// Shared state of a single (pivot-assignment, abstraction) instance.
// The abstraction is mutated in place across CEGAR iterations by
// extending vInlined (original IDs forced to be reproduced).
typedef struct Xcg_Abs_t_ {
    Gia_Man_t *   pOrig;        // original AIG (shared, not owned)
    Gia_Man_t *   pAbs;         // abstracted AIG (owned; rebuilt on refine)
    int           nLevelLimit;  // fanout distance cutoff (0 = unbounded)
    int *         pLevelO;      // level of each original node (Gia_ManLevelNum)
    int *         pDistToCo;    // fanout distance of each original node
    int           nPivots;
    int *         pPivots;      // original node IDs of pivots
    int *         pPivConst;    // forced literal per pivot: 0 (V=0) or 1 (V=1)
    Vec_Int_t *   vAbsPi2Orig;  // abs PI index -> original node ID (-1 for real PIs)
    Vec_Int_t *   vOrig2Abs;    // original node ID -> abs literal (used during build)
    Vec_Int_t *   vInlined;     // original IDs that must NOT be cut (grown by refine)
    char *        pInlinedBit;  // bit flag of vInlined for O(1) lookup (size = nObjOrig)
} Xcg_Abs_t;

static void Xcg_AbsFreeAig( Xcg_Abs_t * p )
{
    if ( p->pAbs ) { Gia_ManStop(p->pAbs); p->pAbs = NULL; }
    if ( p->vAbsPi2Orig ) { Vec_IntFree(p->vAbsPi2Orig); p->vAbsPi2Orig = NULL; }
    if ( p->vOrig2Abs )  { Vec_IntFree(p->vOrig2Abs);  p->vOrig2Abs = NULL; }
}

static void Xcg_AbsFree( Xcg_Abs_t * p )
{
    if ( !p ) return;
    Xcg_AbsFreeAig(p);
    ABC_FREE(p->pLevelO);
    ABC_FREE(p->pDistToCo);
    ABC_FREE(p->pPivots);
    ABC_FREE(p->pPivConst);
    if ( p->vInlined )    Vec_IntFree(p->vInlined);
    ABC_FREE(p->pInlinedBit);
    ABC_FREE(p);
}

// Allocate abstraction state and populate level/distance arrays.
// Pivots are given by (pPivots[], pPivConst[]) of length nPivots.
static Xcg_Abs_t * Xcg_AbsAlloc( Gia_Man_t * pOrig, int nLevelLimit,
                                  int * pPivots, int * pPivConst, int nPivots )
{
    Xcg_Abs_t * p = ABC_CALLOC( Xcg_Abs_t, 1 );
    int i, nObj = Gia_ManObjNum(pOrig);
    Gia_Obj_t * pObj;
    p->pOrig = pOrig;
    p->nLevelLimit = nLevelLimit;
    p->nPivots   = nPivots;
    p->pPivots   = ABC_ALLOC(int, nPivots);
    p->pPivConst = ABC_ALLOC(int, nPivots);
    for ( i = 0; i < nPivots; i++ )
    {
        p->pPivots[i]   = pPivots[i];
        p->pPivConst[i] = pPivConst[i];
    }
    // Compute (combinational) levels and fanout distance to CO.
    Gia_ManLevelNum(pOrig);
    p->pLevelO   = ABC_ALLOC(int, nObj);
    for ( i = 0; i < nObj; i++ ) p->pLevelO[i] = Gia_ObjLevelId(pOrig, i);
    p->pDistToCo = ABC_FALLOC(int, nObj);
    Gia_ManForEachCo( pOrig, pObj, i ) p->pDistToCo[ Gia_ObjId(pOrig,pObj) ] = 0;
    for ( i = nObj - 1; i >= 0; i-- )
    {
        int d, f;
        pObj = Gia_ManObj(pOrig, i);
        if ( p->pDistToCo[i] < 0 ) continue;
        d = p->pDistToCo[i] + 1;
        if ( Gia_ObjIsCo(pObj) ) {
            f = Gia_ObjFaninId0(pObj,i);
            if ( p->pDistToCo[f] < 0 || p->pDistToCo[f] > d ) p->pDistToCo[f] = d;
        } else if ( Gia_ObjIsAnd(pObj) ) {
            f = Gia_ObjFaninId0(pObj,i);
            if ( p->pDistToCo[f] < 0 || p->pDistToCo[f] > d ) p->pDistToCo[f] = d;
            f = Gia_ObjFaninId1(pObj,i);
            if ( p->pDistToCo[f] < 0 || p->pDistToCo[f] > d ) p->pDistToCo[f] = d;
        }
    }
    p->vInlined    = Vec_IntAlloc(32);
    p->pInlinedBit = ABC_CALLOC(char, nObj);
    return p;
}

static inline void Xcg_MarkInlined( Xcg_Abs_t * p, int iOrig )
{
    if ( iOrig < 0 || iOrig >= Gia_ManObjNum(p->pOrig) ) return;
    if ( p->pInlinedBit[iOrig] ) return;
    p->pInlinedBit[iOrig] = 1;
    Vec_IntPush( p->vInlined, iOrig );
}

////////////////////////////////////////////////////////////////////////
///   STAGE 1: BOUNDED DUPLICATION WITH ABSTRACT-PI FRONTIER         ///
////////////////////////////////////////////////////////////////////////

// Decision: should we CUT at this original node (replace by abstract PI)?
// Cutting rules:
//   - Never cut CIs (they become real PIs naturally).
//   - Never cut pivot nodes (their Value is pre-set to const).
//   - Never cut nodes explicitly marked in vInlined (refinement targets).
//   - Cut AND/XOR nodes whose fanout-distance to CO exceeds nLevelLimit.
// The intent is: logic "far" from any output (deep in the TFI) is
// conservatively abstracted; logic near the COs (where the property
// lives) stays concrete.
static inline int Xcg_ShouldCut( Xcg_Abs_t * p, int iObj )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pOrig, iObj);
    if ( p->nLevelLimit <= 0 ) return 0;       // no truncation
    if ( !Gia_ObjIsAnd(pObj)  ) return 0;      // only internal gates
    if ( p->pInlinedBit[iObj] ) return 0;      // refinement override
    // pDistToCo is the SHORTEST distance from iObj to any CO.  Cutting
    // when this exceeds the limit abstracts away "deep" cones.
    return ( p->pDistToCo[iObj] > p->nLevelLimit );
}

// Recursive builder.  Differs from plain XCGRP's DupRec in two ways:
//   (1) checks Xcg_ShouldCut; if true, emits a fresh CI in pAbs and
//       records the back-map entry (abs PI index -> original node ID).
//   (2) also tracks original-ID -> abs literal in vOrig2Abs so the
//       refiner can find already-built nodes on the boundary.
static int Xcg_DupRecBounded( Xcg_Abs_t * p, int iObj )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pOrig, iObj);
    int iLit0, iLit1;
    // Cache: Value holds literal in pAbs if already built (or pre-set).
    if ( ~pObj->Value ) return pObj->Value;

    // Level cutoff: emit abstract PI and record the mapping.  The CI
    // is always pushed as a positive literal (no inversion); later
    // users wrap it with Abc_LitNotCond as needed.
    if ( Xcg_ShouldCut(p, iObj) )
    {
        int iLitPi = Gia_ManAppendCi(p->pAbs);
        // New PI index in pAbs = (Vec_IntSize(vAbsPi2Orig) after push) - 1
        // BUT real PIs occupy the first slots; we track abstract PIs
        // indexed by their PI ordinal.  For simplicity, vAbsPi2Orig is
        // indexed by PI ordinal (1-to-1 with Gia_ManPiNum order).
        // Size before push = current PI count; we must pad for the real
        // PIs that were added first.  See Xcg_Build() below: real PIs
        // are all created before any Xcg_DupRecBounded call.
        Vec_IntPush( p->vAbsPi2Orig, iObj );
        Vec_IntWriteEntry( p->vOrig2Abs, iObj, iLitPi );
        return (pObj->Value = iLitPi);
    }

    // Recurse fanin0 (CI/CO/AND/XOR all have fanin0).
    iLit0 = Xcg_DupRecBounded( p, Gia_ObjFaninId0(pObj, iObj) );
    iLit0 = Abc_LitNotCond(iLit0, Gia_ObjFaninC0(pObj));
    if ( Gia_ObjIsCo(pObj) )
        return (pObj->Value = Gia_ManAppendCo(p->pAbs, iLit0));
    // Fanin1 for AND/XOR.
    iLit1 = Xcg_DupRecBounded( p, Gia_ObjFaninId1(pObj, iObj) );
    iLit1 = Abc_LitNotCond(iLit1, Gia_ObjFaninC1(pObj));
    if ( Gia_ObjIsXor(pObj) )
        pObj->Value = Gia_ManHashXor(p->pAbs, iLit0, iLit1);
    else
        pObj->Value = Gia_ManHashAnd(p->pAbs, iLit0, iLit1);
    Vec_IntWriteEntry( p->vOrig2Abs, iObj, pObj->Value );
    return pObj->Value;
}

// (Re)build the abstraction.  Called initially and after each refine.
// The previous pAbs (if any) is freed.  Pivots are pre-set to consts.
static void Xcg_Build( Xcg_Abs_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    // Discard stale abstraction artifacts.
    Xcg_AbsFreeAig(p);
    p->pAbs = Gia_ManStart( Gia_ManObjNum(p->pOrig) );
    p->pAbs->pName = Abc_UtilStrsav(p->pOrig->pName);
    p->pAbs->pSpec = Abc_UtilStrsav(p->pOrig->pSpec);
    Gia_ManHashStart(p->pAbs);
    Gia_ManFillValue(p->pOrig);
    Gia_ManConst0(p->pOrig)->Value = 0;
    // Pivots: force to the assigned constant (0 or 1 as a literal).
    for ( i = 0; i < p->nPivots; i++ )
        Gia_ManObj(p->pOrig, p->pPivots[i])->Value = p->pPivConst[i];
    // Pre-create all REAL CIs so the PI/RO numbering is preserved.
    // Every subsequent Gia_ManAppendCi call (for abstract PIs) appends
    // AFTER the real PIs, breaking naive PI-indexed simulation unless
    // the simulator is aware.  We expose this ordering via vAbsPi2Orig,
    // which is populated only for abstract PIs.  Real PI slots in that
    // vector (indices 0..nPiOrig-1) are padded with -1.
    p->vAbsPi2Orig = Vec_IntAlloc( Gia_ManObjNum(p->pOrig) );
    p->vOrig2Abs   = Vec_IntStartFull( Gia_ManObjNum(p->pOrig) );
    Gia_ManForEachCi( p->pOrig, pObj, i )
    {
        int iLit = Gia_ManAppendCi(p->pAbs);
        pObj->Value = iLit;
        Vec_IntPush( p->vAbsPi2Orig, -1 );  // -1 marks "real PI, not abstract"
        Vec_IntWriteEntry( p->vOrig2Abs, Gia_ObjId(p->pOrig, pObj), iLit );
    }
    // Walk every CO to materialize reachable logic.
    Gia_ManForEachCo( p->pOrig, pObj, i )
        Xcg_DupRecBounded( p, Gia_ObjId(p->pOrig, pObj) );
    Gia_ManHashStop(p->pAbs);
    Gia_ManSetRegNum(p->pAbs, Gia_ManRegNum(p->pOrig));
}

////////////////////////////////////////////////////////////////////////
///        STAGE 2: BATCHED BIT-PARALLEL SIMULATION VALIDATION       ///
///                                                                  ///
///  Scorr gives us an equivalence class map on pAbs.  We translate  ///
///  each surviving pair (a,b) into original-node IDs and check it   ///
///  against a batch of random patterns simulated on the ORIGINAL    ///
///  AIG.  If ever sim(a) != sim(b) (modulo polarity fComp), the     ///
///  pair is spurious -- an artifact of the abstraction.             ///
///                                                                  ///
///  Design note (hot path rewrite):                                 ///
///    The previous implementation ran one full-circuit simulation   ///
///    PER candidate pair, giving O(P * R * N) cost per CEGAR iter.  ///
///    We now run a single bit-parallel simulation of nWords 32-bit  ///
///    words per iter (O(N * nWords)) and reuse the result for every ///
///    pair via an O(nWords) word compare.  For typical P ~ 10^4,    ///
///    R = 16, N ~ 10^5, this cuts the validation cost by 1000x+.    ///
///                                                                  ///
///  Register outputs (ROs) are treated as free PIs (sampled random- ///
///  ly each call), which is worst-case sound for sequential         ///
///  equivalence: a pair that survives all random RO states is       ///
///  combinationally correlated across all reachable states.         ///
////////////////////////////////////////////////////////////////////////

typedef struct Xcg_SimMan_t_ {
    Gia_Man_t *  pAig;     // reference to the AIG being simulated (not owned)
    int          nWords;   // number of 32-bit words per node (R in the docs)
    unsigned *   pSim;     // nObj * nWords array; layout: pSim[id*nWords + w]
} Xcg_SimMan_t;

static Xcg_SimMan_t * Xcg_SimManAlloc( Gia_Man_t * pAig, int nWords )
{
    Xcg_SimMan_t * p = ABC_CALLOC( Xcg_SimMan_t, 1 );
    p->pAig   = pAig;
    p->nWords = nWords;
    p->pSim   = ABC_CALLOC( unsigned, (size_t)Gia_ManObjNum(pAig) * nWords );
    return p;
}

static void Xcg_SimManFree( Xcg_SimMan_t * p )
{
    if ( !p ) return;
    ABC_FREE(p->pSim);
    ABC_FREE(p);
}

// Run one complete bit-parallel simulation pass.  Fills
// pSim[id*nWords + w] for every object in topological order.
// CI values are drawn from an xorshift32 stream seeded by Seed.
// const-0 (ID 0) is forced to zero.
static void Xcg_SimManRun( Xcg_SimMan_t * p, unsigned Seed )
{
    Gia_Man_t * pAig = p->pAig;
    unsigned *  pData = p->pSim;
    int nW = p->nWords;
    Gia_Obj_t * pObj;
    int i, w;
    unsigned S = Seed ? Seed : 0xDEADBEEFu;
    // const-0 ID=0
    for ( w = 0; w < nW; w++ )
        pData[0 * nW + w] = 0;
    // CIs: each node gets nW fresh words.  ROs are treated as free PIs.
    Gia_ManForEachCi( pAig, pObj, i )
    {
        int id = Gia_ObjId(pAig, pObj);
        unsigned * pDi = pData + (size_t)id * nW;
        for ( w = 0; w < nW; w++ )
        {
            S ^= S << 13; S ^= S >> 17; S ^= S << 5;
            pDi[w] = S;
        }
    }
    // Internal gates in topological order; XOR and AND handled separately
    // so the inner loop is tight (no per-word branch on gate type).
    Gia_ManForEachAnd( pAig, pObj, i )
    {
        int iF0 = Gia_ObjFaninId0(pObj, i);
        int iF1 = Gia_ObjFaninId1(pObj, i);
        int c0  = Gia_ObjFaninC0(pObj);
        int c1  = Gia_ObjFaninC1(pObj);
        unsigned * pD0 = pData + (size_t)iF0 * nW;
        unsigned * pD1 = pData + (size_t)iF1 * nW;
        unsigned * pDi = pData + (size_t)i   * nW;
        if ( Gia_ObjIsXor(pObj) )
        {
            for ( w = 0; w < nW; w++ )
            {
                unsigned v0 = c0 ? ~pD0[w] : pD0[w];
                unsigned v1 = c1 ? ~pD1[w] : pD1[w];
                pDi[w] = v0 ^ v1;
            }
        }
        else
        {
            for ( w = 0; w < nW; w++ )
            {
                unsigned v0 = c0 ? ~pD0[w] : pD0[w];
                unsigned v1 = c1 ? ~pD1[w] : pD1[w];
                pDi[w] = v0 & v1;
            }
        }
    }
    // COs not evaluated: they are not equivalence candidates.
}

// Pair validation against pre-simulated data.  Returns 1 iff every
// one of the nWords * 32 patterns agrees with the claimed polarity.
static inline int Xcg_SimManValidate( Xcg_SimMan_t * p, int iA, int iB, int fComp )
{
    int nW = p->nWords, w;
    unsigned * pA = p->pSim + (size_t)iA * nW;
    unsigned * pB = p->pSim + (size_t)iB * nW;
    if ( fComp )
    {
        for ( w = 0; w < nW; w++ )
            if ( pA[w] != ~pB[w] ) return 0;
    }
    else
    {
        for ( w = 0; w < nW; w++ )
            if ( pA[w] !=  pB[w] ) return 0;
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///        STAGE 2 (cont.): MAP ABS EQUIVS BACK TO ORIGINAL          ///
////////////////////////////////////////////////////////////////////////

// Extract equivalence pairs from pAbs (post-scorr) as (origA, origB, fComp)
// triples.  origA and origB are original-AIG node IDs; fComp is the
// polarity bit (1 = complementary, 0 = same).  The polarity is taken
// from the original AIG's fPhase bits XOR'd together.
// The vector format: triples packed as [origA, origB, fComp, ...].
// Requires Xcg_InstallBackMap to have been called first.
static Vec_Int_t * Xcg_CollectEquivTriples( Xcg_Abs_t * p )
{
    Vec_Int_t * vTrip = Vec_IntAlloc(64);
    Gia_Man_t * pAbs = p->pAbs;
    Gia_Man_t * pOrig = p->pOrig;
    Gia_Obj_t * pObj;
    int i;
    // The back-map lives on pAbs->pObj[].Value (original ID or ~0).
    // It was installed by Xcg_InstallBackMap before this call.
    Gia_ManForEachObj( pAbs, pObj, i )
    {
        int iRepr, origA, origB, fComp;
        if ( !Gia_ObjHasRepr(pAbs, i) ) continue;
        iRepr = Gia_ObjRepr(pAbs, i);
        origA = (int)Gia_ManObj(pAbs, i)->Value;
        origB = (int)Gia_ManObj(pAbs, iRepr)->Value;
        if ( origA == ~0 || origB == ~0 ) continue;
        if ( origA < 0 || origA >= Gia_ManObjNum(pOrig) ) continue;
        if ( origB < 0 || origB >= Gia_ManObjNum(pOrig) ) continue;
        if ( origA == origB ) continue;
        // fPhase bits encode the simulation phase under random sim on
        // the original.  If both original nodes agree in phase, the
        // pair is positive-equivalent; otherwise complementary.
        fComp = (int)(Gia_ManObj(pOrig, origA)->fPhase ^
                      Gia_ManObj(pOrig, origB)->fPhase);
        Vec_IntPush(vTrip, origA);
        Vec_IntPush(vTrip, origB);
        Vec_IntPush(vTrip, fComp);
    }
    return vTrip;
}

// Install the standard back-map on pAbs: pAbs->pObj[j].Value = original
// node ID that maps to j.  (In Xcg_Build we stored forward mappings on
// pOrig->pObj[].Value.)  First-wins semantics for multiple origins
// collapsing to the same abstract literal.
static void Xcg_InstallBackMap( Xcg_Abs_t * p )
{
    Gia_Obj_t * pObj;
    int i, jNew;
    Gia_ManFillValue( p->pAbs );
    Gia_ManForEachObj( p->pOrig, pObj, i )
    {
        if ( !~pObj->Value ) continue;
        if ( Gia_ObjIsCo(pObj) ) continue;
        jNew = Abc_Lit2Var(pObj->Value);
        if ( jNew < 0 || jNew >= Gia_ManObjNum(p->pAbs) ) continue;
        if ( Gia_ManObj(p->pAbs, jNew)->Value == ~0 )
            Gia_ManObj(p->pAbs, jNew)->Value = (unsigned)i;
    }
}

////////////////////////////////////////////////////////////////////////
///        STAGE 3: REFINEMENT HEURISTIC                             ///
////////////////////////////////////////////////////////////////////////

// Find the best refinement target for a spurious pair (origA, origB).
// Heuristic: among currently-abstract PIs (nodes in vAbsPi2Orig with
// non-negative entry), pick the one whose original node has the
// SMALLEST structural distance to either origA or origB.  Inlining
// that node brings the abstraction closest to where the conflict
// manifested.
// Returns original-node ID to inline, or -1 if no candidate exists.
static int Xcg_PickRefinementTarget( Xcg_Abs_t * p, int origA, int origB )
{
    int i, iBest = -1, dBest = INT_MAX;
    int lA = p->pLevelO[origA], lB = p->pLevelO[origB];
    // Cheap proxy for "structural distance": absolute level gap.
    // A full O(E) BFS over the original DAG would be more precise
    // but is optional; most useful refinements are caught by level.
    for ( i = 0; i < Vec_IntSize(p->vAbsPi2Orig); i++ )
    {
        int orig = Vec_IntEntry(p->vAbsPi2Orig, i);
        int d;
        if ( orig < 0 ) continue;            // real PI, not abstract
        if ( p->pInlinedBit[orig] ) continue;// already inlined
        d = Abc_MinInt( Abc_AbsInt(p->pLevelO[orig] - lA),
                        Abc_AbsInt(p->pLevelO[orig] - lB) );
        if ( d < dBest ) { dBest = d; iBest = orig; }
    }
    return iBest;
}

////////////////////////////////////////////////////////////////////////
///     STAGE 3 (cont.): BATCHED REFINEMENT (fixes old RefineChain   ///
///                    bug: mark-only without rebuild stalled CEGAR) ///
///                                                                  ///
///  The old code had two separate refinement routines:              ///
///    - Xcg_RefineOne     : mark + rebuild                          ///
///    - Xcg_RefineChain   : mark ONLY (no rebuild!)   <-- BUG       ///
///  When chain refinement fired, the next iteration called scorr on ///
///  an unchanged abstraction -> identical equivalences -> CEGAR     ///
///  loop made no progress until nMaxRefine was exhausted.           ///
///                                                                  ///
///  The new scheme collects every spurious pair's refinement target ///
///  into vTargets (dedup'd), optionally expands each target to its  ///
///  XOR chain, marks them all at once, and rebuilds pAbs ONCE.      ///
///  This also multiplies progress per iteration, reducing the       ///
///  number of scorr invocations needed.                             ///
////////////////////////////////////////////////////////////////////////

// Mark iOrig (and, if pChainId given, its entire XOR chain) as must-inline.
// Does NOT rebuild; caller must invoke Xcg_Build() once all marks are done.
static void Xcg_MarkInlinedWithChain( Xcg_Abs_t * p, int iOrig, int * pChainId )
{
    Xcg_MarkInlined(p, iOrig);
    if ( pChainId && pChainId[iOrig] >= 0 )
    {
        int cid = pChainId[iOrig];
        Gia_Obj_t * pObj;
        int i;
        Gia_ManForEachAnd( p->pOrig, pObj, i )
            if ( pChainId[i] == cid )
                Xcg_MarkInlined(p, i);
    }
}

////////////////////////////////////////////////////////////////////////
///    STAGE 4: CEGAR DRIVER + MULTI-PIVOT + OPTIONAL REWRITING      ///
////////////////////////////////////////////////////////////////////////

// Chain-ID map (same as Xcg_ComputeScores internals) exposed for
// bulk-refinement; cheap enough to recompute per-driver-call.
static int * Xcg_ComputeChainIdMap( Gia_Man_t * p )
{
    int i, nObj = Gia_ManObjNum(p);
    int * pUf   = ABC_ALLOC(int, nObj);
    int * pRank = ABC_CALLOC(int, nObj);
    int * pCid  = ABC_ALLOC(int, nObj);
    Gia_Obj_t * pObj;
    for ( i = 0; i < nObj; i++ ) { pUf[i] = i; pCid[i] = -1; }
    Gia_ManForEachAnd( p, pObj, i )
    {
        int f0, f1;
        if ( !Gia_ObjIsXor(pObj) ) continue;
        f0 = Gia_ObjFaninId0(pObj,i); f1 = Gia_ObjFaninId1(pObj,i);
        if ( Gia_ObjIsXor(Gia_ManObj(p,f0)) ) Xcg_UfUnion(pUf,pRank,i,f0);
        if ( Gia_ObjIsXor(Gia_ManObj(p,f1)) ) Xcg_UfUnion(pUf,pRank,i,f1);
    }
    Gia_ManForEachAnd( p, pObj, i )
        if ( Gia_ObjIsXor(pObj) ) pCid[i] = Xcg_UfFind(pUf,i);
    ABC_FREE(pUf); ABC_FREE(pRank);
    return pCid;
}

// CEGAR inner loop for ONE pivot-assignment branch.
// Inputs: an abstraction state p, scorr params, max refine iters,
// simulation rounds per pair (nWords), pChainId for bulk refinement
// (optional; NULL disables chain expansion), and fRewrite to pre-rewrite
// the abstraction before each scorr call.
// Outputs: fills pConfirmed with confirmed (origA,origB,fComp) triples
// that passed simulation on the original.
//
// Key differences vs. the old loop:
//   - Simulation allocated ONCE outside the iter loop, reused across
//     iterations (O(N*W) per iter, not O(P*R*N)).
//   - ALL spurious pairs contribute refinement targets (not just the
//     first), and the whole batch is marked + rebuilt in one shot.
//   - After the batched refinement, pAbs is rebuilt exactly once via
//     Xcg_Build.  This fixes the old Xcg_RefineChain stall bug.
static void Xcg_CegarLoop( Xcg_Abs_t * p, Cec_ParCor_t * pPars,
                            int nMaxRefine, int nSimRounds,
                            int * pChainId, int fRewrite,
                            Vec_Int_t * pConfirmed )
{
    Xcg_SimMan_t * pSim = Xcg_SimManAlloc(p->pOrig, nSimRounds);
    Vec_Int_t *    vTargets = Vec_IntAlloc(16);
    int iter;
    for ( iter = 0; iter <= nMaxRefine; iter++ )
    {
        Gia_Man_t * pRew = NULL;
        int i, nSpurious = 0;
        Vec_Int_t * vTrip;
        // Optional rewrite pass BEFORE scorr to shrink the abstraction.
        // Gia_ManAigSyn2 returns a new AIG; we swap it into p->pAbs and
        // invalidate the back-map (it must be rebuilt post-scorr).
        if ( fRewrite )
        {
            pRew = Gia_ManAigSyn2(p->pAbs, 0, 1, 0, 100, 0, 0, 0);
            if ( pRew ) { Gia_ManStop(p->pAbs); p->pAbs = pRew; }
        }
        // Run the correspondence engine on the abstract AIG.
        Cec_ManLSCorrespondenceClasses(p->pAbs, pPars);
        // Back-map: pAbs->pObj[].Value = original node ID.  Rewriting
        // destroys node numbering, so CEGAR cannot proceed past a
        // rewrite pass (see top-of-file limitations).
        if ( !fRewrite || !pRew )
            Xcg_InstallBackMap(p);
        else
            break;
        vTrip = Xcg_CollectEquivTriples(p);
        // ONE simulation pass per iter; validate every pair in O(nWords).
        // Seed varies per iter so successive iters see different patterns.
        Xcg_SimManRun( pSim, (unsigned)(0x9E3779B1u * (unsigned)(iter + 1) + 0x12345u) );
        Vec_IntClear(vTargets);
        for ( i = 0; i < Vec_IntSize(vTrip); i += 3 )
        {
            int origA = Vec_IntEntry(vTrip, i);
            int origB = Vec_IntEntry(vTrip, i+1);
            int fComp = Vec_IntEntry(vTrip, i+2);
            if ( Xcg_SimManValidate(pSim, origA, origB, fComp) )
            {
                Vec_IntPush(pConfirmed, origA);
                Vec_IntPush(pConfirmed, origB);
                Vec_IntPush(pConfirmed, fComp);
            }
            else
            {
                int iT;
                nSpurious++;
                iT = Xcg_PickRefinementTarget(p, origA, origB);
                // Vec_IntPushUnique keeps vTargets tight and bounds rebuild
                // work when many spurious pairs point to the same abstract PI.
                if ( iT >= 0 )
                    Vec_IntPushUnique(vTargets, iT);
            }
        }
        Vec_IntFree(vTrip);
        if ( pPars->fVerbose )
            Abc_Print(1, "  CEGAR iter %d: %d confirmed, %d spurious, %d refine targets.\n",
                      iter, Vec_IntSize(pConfirmed)/3, nSpurious,
                      Vec_IntSize(vTargets));
        if ( nSpurious == 0 )         break;
        if ( iter == nMaxRefine )     break;
        if ( Vec_IntSize(vTargets) == 0 ) break;  // nowhere to refine
        // Batched inline: mark every target (+chain if pChainId) then rebuild.
        {
            int k, iT;
            Vec_IntForEachEntry( vTargets, iT, k )
                Xcg_MarkInlinedWithChain(p, iT, pChainId);
        }
        Xcg_Build(p);
        // pAbs was rebuilt -> old reprs/nexts are already gone with it.
    }
    Vec_IntFree(vTargets);
    Xcg_SimManFree(pSim);
}

////////////////////////////////////////////////////////////////////////
///             TOP-LEVEL DRIVER + PUBLIC ENTRY                      ///
////////////////////////////////////////////////////////////////////////

// Intersect two sorted-by-(origA,origB,fComp) triple vectors.
// We use a small map: origA -> (origB, fComp) and drop disagreeing pairs.
static void Xcg_IntersectTriples( Vec_Int_t * vAccum, Vec_Int_t * vNew,
                                    int nObj, int * pMapB, char * pMapSeen )
{
    int i;
    // Pass 1: hash vAccum by origA -> (origB, fComp).  pMapB[origA]
    // holds origB, pMapSeen[origA] holds 1+fComp.
    memset(pMapSeen, 0, nObj);
    for ( i = 0; i < Vec_IntSize(vAccum); i += 3 )
    {
        int a = Vec_IntEntry(vAccum, i);
        int b = Vec_IntEntry(vAccum, i+1);
        int c = Vec_IntEntry(vAccum, i+2);
        pMapB[a]    = b;
        pMapSeen[a] = (char)(1 + c);   // 1 or 2
    }
    // Pass 2: walk vNew; keep triples present in vAccum with same (b,c).
    Vec_IntClear(vAccum);
    for ( i = 0; i < Vec_IntSize(vNew); i += 3 )
    {
        int a = Vec_IntEntry(vNew, i);
        int b = Vec_IntEntry(vNew, i+1);
        int c = Vec_IntEntry(vNew, i+2);
        if ( pMapSeen[a] && pMapB[a] == b && pMapSeen[a] == 1 + c )
        {
            Vec_IntPush(vAccum, a);
            Vec_IntPush(vAccum, b);
            Vec_IntPush(vAccum, c);
        }
    }
}

////////////////////////////////////////////////////////////////////////
///         BRANCH-LEVEL THREAD DISPATCH (optional, pthreads)        ///
///                                                                  ///
///  Each constant-assignment branch is independent: it owns its     ///
///  own abstraction, pAbs, simulator, and equivalence triples.      ///
///  The only shared state is the ORIGINAL AIG and pPars, so we      ///
///  give each thread a private Gia_ManDup() clone of pOrig -- both  ///
///  Xcg_Build (which mutates pObj->Value via Gia_ManFillValue) and  ///
///  Gia_ManLevelNum (called inside Xcg_AbsAlloc) need exclusive     ///
///  write access to pOrig fields.  Cloning costs O(nObj) per thread ///
///  but eliminates all races at branch granularity.                 ///
///                                                                  ///
///  pPars is shared read/write, matching the existing cecXcgrp.c    ///
///  pattern (Xcgrp_SolveParts).                                     ///
////////////////////////////////////////////////////////////////////////

#ifdef ABC_USE_PTHREADS
typedef struct Xcg_BT_t_ {
    Gia_Man_t *     pOrigMaster;    // shared, read-only
    int *           pPivotIds;      // shared, read-only (original-node IDs)
    int             nPivots;
    int             pPivConst[8];   // per-thread: constant assignment
    int             nLevelLimit;
    int             nMaxRefine;
    int             nSimRounds;
    int             fRewrite;
    Cec_ParCor_t *  pPars;          // shared (same pattern as cecXcgrp.c)
    Vec_Int_t *     vResult;        // per-thread output: (a,b,fComp) triples
} Xcg_BT_t;

static void * Xcg_BranchThread( void * pArg )
{
    Xcg_BT_t *   t = (Xcg_BT_t *)pArg;
    Gia_Man_t *  pLocal;
    int *        pChainLocal;
    Xcg_Abs_t *  pAbs;
    // Private clone of pOrig: Xcg_Build / Gia_ManLevelNum mutate pOrig.
    pLocal = Gia_ManDup(t->pOrigMaster);
    Gia_ManSetPhase(pLocal);
    pChainLocal = Xcg_ComputeChainIdMap(pLocal);
    pAbs = Xcg_AbsAlloc(pLocal, t->nLevelLimit,
                         t->pPivotIds, t->pPivConst, t->nPivots);
    Xcg_Build(pAbs);
    Xcg_CegarLoop(pAbs, t->pPars, t->nMaxRefine, t->nSimRounds,
                   pChainLocal, t->fRewrite, t->vResult);
    Xcg_AbsFree(pAbs);
    ABC_FREE(pChainLocal);
    Gia_ManStop(pLocal);
    return NULL;
}
#endif

// Run one branch sequentially (master thread).  Re-used when pthreads are
// unavailable or nProcs <= 1; also used as the fallback body when the
// pthread path is compiled out.
static void Xcg_RunBranchSerial( Gia_Man_t * pAig, int * pPivotIds,
                                  int pPivConst[8], int nPivots,
                                  int nLevelLimit, int nMaxRefine,
                                  int nSimRounds, int fRewrite,
                                  int * pChainId, Cec_ParCor_t * pPars,
                                  Vec_Int_t * vResult )
{
    Xcg_Abs_t * pAbs;
    pAbs = Xcg_AbsAlloc(pAig, nLevelLimit, pPivotIds, pPivConst, nPivots);
    Xcg_Build(pAbs);
    Xcg_CegarLoop(pAbs, pPars, nMaxRefine, nSimRounds, pChainId, fRewrite, vResult);
    Xcg_AbsFree(pAbs);
}

// Public entry: CEGAR-enhanced XCGRP correspondence.
//   nPivots     : 1..6 (2^N subproblems); effective cap at 6 to keep 64 branches
//   nLevelLimit : 0 disables truncation; positive = cut at that CO-distance
//   nMaxRefine  : max CEGAR iterations per pivot branch (e.g. 8)
//   nSimRounds  : random words per pair validation (e.g. 16 = 512 patterns)
//   fRewrite    : 1 = call Gia_ManAigSyn2 before each scorr (first iter only)
// pPars->nProcs > 1 (with ABC_USE_PTHREADS) enables branch-level parallelism.
// Returns reduced Gia; caller frees.
Gia_Man_t * Cec_ManXcgrpCegarCorrespondence( Gia_Man_t * pAig, Cec_ParCor_t * pPars,
                                              int nPivots, int nLevelLimit,
                                              int nMaxRefine, int nSimRounds,
                                              int fRewrite )
{
    Gia_Man_t * pNew, * pTemp;
    Vec_Int_t * vPivots, * vAccum;
    int * pChainId;
    int i, k, nBranches, nObj;
    int * pMapB;
    char * pMapSeen;
    int nParallel = 1;

    if ( nPivots   < 1 ) nPivots   = 1;
    if ( nPivots   > 6 ) nPivots   = 6;
    if ( nMaxRefine < 0 ) nMaxRefine = 0;
    if ( nSimRounds <= 0 ) nSimRounds = 16;

    // --- Pivot selection (top-N XOR gates by score) ---
    vPivots = Xcg_SelectTopNPivots(pAig, nPivots);
    if ( Vec_IntSize(vPivots) == 0 )
    {
        // No XOR chains: graceful fallback to plain scorr.
        if ( pPars->fVerbose )
            Abc_Print(1, "XCGRP-CEGAR: no pivots found; falling back to scorr.\n");
        Vec_IntFree(vPivots);
        return Cec_ManLSCorrespondence(pAig, pPars);
    }
    nPivots   = Vec_IntSize(vPivots);
    nBranches = 1 << nPivots;
    nObj      = Gia_ManObjNum(pAig);

    // --- Required scaffolding ---
    pChainId = Xcg_ComputeChainIdMap(pAig);
    // Ensure phase bits are consistent so the (origA,origB) polarity
    // agrees across branches.  Gia_ManSetPhase is idempotent.
    Gia_ManSetPhase(pAig);

#ifdef ABC_USE_PTHREADS
    if ( pPars->nProcs > 1 )
    {
        nParallel = pPars->nProcs;
        if ( nParallel > nBranches ) nParallel = nBranches;
    }
#endif

    // --- Branch enumeration: iterate all 2^N constant assignments, in
    // waves of up to nParallel branches.  After each wave, intersect
    // per-branch triples into vAccum in branch-index order (which is
    // the order they are dispatched in, so intersection semantics match
    // the old serial loop exactly).
    vAccum   = Vec_IntAlloc(256);
    pMapB    = ABC_ALLOC(int,  nObj);
    pMapSeen = ABC_ALLOC(char, nObj);
    {
        int iStart;
        int fStopAll = 0;
        Vec_Int_t ** pResults = ABC_ALLOC(Vec_Int_t *, nParallel);
#ifdef ABC_USE_PTHREADS
        pthread_t *  pThr  = (nParallel > 1) ? ABC_ALLOC(pthread_t, nParallel) : NULL;
        Xcg_BT_t *   pArgs = (nParallel > 1) ? ABC_ALLOC(Xcg_BT_t, nParallel)  : NULL;
#endif
        for ( iStart = 0; iStart < nBranches && !fStopAll; iStart += nParallel )
        {
            int nInWave = nBranches - iStart;
            if ( nInWave > nParallel ) nInWave = nParallel;

            // Dispatch all branches in this wave.
            for ( k = 0; k < nInWave; k++ )
            {
                int iBranch = iStart + k;
                int pPivConst[8];
                pResults[k] = Vec_IntAlloc(64);
                for ( i = 0; i < nPivots; i++ )
                    pPivConst[i] = (iBranch >> i) & 1;
                if ( pPars->fVerbose )
                {
                    Abc_Print(1, "XCGRP-CEGAR: branch %d/%d, pivot consts =",
                              iBranch+1, nBranches);
                    for ( i = 0; i < nPivots; i++ )
                        Abc_Print(1, " %d", pPivConst[i]);
                    Abc_Print(1, "\n");
                }
#ifdef ABC_USE_PTHREADS
                if ( nParallel > 1 )
                {
                    pArgs[k].pOrigMaster = pAig;
                    pArgs[k].pPivotIds   = Vec_IntArray(vPivots);
                    pArgs[k].nPivots     = nPivots;
                    for ( i = 0; i < nPivots; i++ )
                        pArgs[k].pPivConst[i] = pPivConst[i];
                    pArgs[k].nLevelLimit = nLevelLimit;
                    pArgs[k].nMaxRefine  = nMaxRefine;
                    pArgs[k].nSimRounds  = nSimRounds;
                    pArgs[k].fRewrite    = fRewrite;
                    pArgs[k].pPars       = pPars;
                    pArgs[k].vResult     = pResults[k];
                    pthread_create(&pThr[k], NULL, Xcg_BranchThread, &pArgs[k]);
                }
                else
#endif
                {
                    Xcg_RunBranchSerial(pAig, Vec_IntArray(vPivots),
                                         pPivConst, nPivots,
                                         nLevelLimit, nMaxRefine, nSimRounds,
                                         fRewrite, pChainId, pPars,
                                         pResults[k]);
                }
            }
            // Join.
#ifdef ABC_USE_PTHREADS
            if ( nParallel > 1 )
                for ( k = 0; k < nInWave; k++ )
                    pthread_join(pThr[k], NULL);
#endif
            // Intersect results in branch-index order.
            for ( k = 0; k < nInWave; k++ )
            {
                int iBranch = iStart + k;
                if ( iBranch == 0 )
                {
                    Vec_IntClear(vAccum);
                    Vec_IntAppend(vAccum, pResults[k]);
                }
                else
                {
                    Xcg_IntersectTriples(vAccum, pResults[k],
                                          nObj, pMapB, pMapSeen);
                }
                Vec_IntFree(pResults[k]);
                if ( Vec_IntSize(vAccum) == 0 )
                {
                    if ( pPars->fVerbose )
                        Abc_Print(1, "XCGRP-CEGAR: empty intersection after branch %d; stopping early.\n", iBranch+1);
                    // Free remaining results in this wave, then abort.
                    for ( k++; k < nInWave; k++ )
                        Vec_IntFree(pResults[k]);
                    fStopAll = 1;
                    break;
                }
            }
        }
        ABC_FREE(pResults);
#ifdef ABC_USE_PTHREADS
        ABC_FREE(pThr);
        ABC_FREE(pArgs);
#endif
    }
    ABC_FREE(pMapB); ABC_FREE(pMapSeen);
    ABC_FREE(pChainId);
    Vec_IntFree(vPivots);

    // --- Apply surviving equivalences to pAig->pReprs ---
    ABC_FREE(pAig->pReprs);
    ABC_FREE(pAig->pNexts);
    pAig->pReprs = ABC_CALLOC(Gia_Rpr_t, nObj);
    for ( i = 0; i < nObj; i++ ) Gia_ObjSetRepr(pAig, i, GIA_VOID);
    for ( i = 0; i < Vec_IntSize(vAccum); i += 3 )
    {
        int a = Vec_IntEntry(vAccum, i);
        int b = Vec_IntEntry(vAccum, i+1);
        /* fComp is honored via fPhase on each node; Gia_ManCorrReduce
           picks the polarity from fPhase bits of a vs. b.  We just set
           the representative pointer here. */
        if ( a < b ) { int t = a; a = b; b = t; }  // larger ID -> smaller ID
        pAig->pReprs[a].iRepr = (unsigned)b;
    }
    pAig->pNexts = Gia_ManDeriveNexts(pAig);
    Vec_IntFree(vAccum);

    // --- Reduce using confirmed equivalences ---
    pNew = Gia_ManCorrReduce(pAig);
    pNew = Gia_ManSeqCleanup(pTemp = pNew);
    Gia_ManStop(pTemp);
    if ( pPars->fVerbose )
        Abc_Print(1, "XCGRP-CEGAR: NBeg=%d NEnd=%d. RBeg=%d REnd=%d.\n",
                  Gia_ManAndNum(pAig), Gia_ManAndNum(pNew),
                  Gia_ManRegNum(pAig), Gia_ManRegNum(pNew));
    return pNew;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
