/**CFile****************************************************************

  FileName    [cecXcgrp.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [XCGRP: XOR-Cluster-Guided Register Partitioning for &scorr.

    Algorithm outline:
      1. Build Union-Find over XOR gates to identify XOR/carry chains.
      2. Score each XOR node: score[v] = chainLen^2 / (distToCO + 1).
         Rewards long chains whose pivot end sits close to circuit outputs.
      3. Pick the globally highest-scored XOR gate as the D&C pivot V.
      4. Build two simplified sub-AIGs by constant propagation:
           pPart0 (V forced to 0) and pPart1 (V forced to 1).
         GIA hash-rewriting automatically collapses adjacent XOR gates
         (e.g., V XOR A  ->  A  when V=0, or  ~A  when V=1).
      5. Run the pluggable solve engine independently on each sub-AIG
         (optionally in parallel via pthreads).
      6. Intersect the found equivalences: keep only pairs that both
         sub-problems agree on.  The case split covers all executions
         (V in {0,1}), so the intersection is sound and complete.

    Engine hook:
      Cec_ManXcgrpCorrespondence() accepts a function-pointer argument
      of type Xcgrp_SolveFunc_t.  Pass NULL to use the default SAT-
      based scorr engine.  Future callers may supply BDD or ES solvers
      for sub-problems with very high XOR density.
  ]

  Author      [xiran - UC Berkeley]

  Date        [Ver. 1.0. Started - April 2026.]

***********************************************************************/

#include "cecInt.h"

#ifdef ABC_USE_PTHREADS
#include <pthread.h>
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        TYPE DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

// Engine dispatch hook: plug in BDD / ES solver for dense XOR sub-problems.
// The default engine is Cec_ManLSCorrespondenceClasses (SAT-based scorr).
typedef int (*Xcgrp_SolveFunc_t)( Gia_Man_t * pAig, Cec_ParCor_t * pPars );

#ifdef ABC_USE_PTHREADS
typedef struct Xcgrp_Thread_t_ {
    Gia_Man_t *       pPart;
    Cec_ParCor_t *    pPars;
    Xcgrp_SolveFunc_t pSolveFunc;
} Xcgrp_Thread_t;
#endif

////////////////////////////////////////////////////////////////////////
///                       UNION-FIND HELPERS                         ///
////////////////////////////////////////////////////////////////////////

static int Xcgrp_UfFind( int * pUf, int i )
{
    // Iterative find with two-step path compression (halving).
    while ( pUf[i] != i )
    {
        pUf[i] = pUf[pUf[i]];
        i = pUf[i];
    }
    return i;
}

static void Xcgrp_UfUnion( int * pUf, int * pRank, int a, int b )
{
    a = Xcgrp_UfFind(pUf, a);
    b = Xcgrp_UfFind(pUf, b);
    if ( a == b ) return;
    if ( pRank[a] < pRank[b] ) { int t = a; a = b; b = t; }
    pUf[b] = a;
    if ( pRank[a] == pRank[b] ) pRank[a]++;
}

////////////////////////////////////////////////////////////////////////
///                     CHAIN-ID COMPUTATION                         ///
////////////////////////////////////////////////////////////////////////

// Returns chainId[i] = Union-Find root for XOR-gate nodes, -1 for others.
// Two XOR gates belong to the same chain iff they are directly connected
// through XOR-only fanin edges (i.e., they form a carry/XOR chain).
static int * Gia_ManXcgrpComputeChainIds( Gia_Man_t * p )
{
    int i, nObj = Gia_ManObjNum(p);
    int * pChainId = ABC_ALLOC( int, nObj );
    int * pUf      = ABC_ALLOC( int, nObj );
    int * pRank    = ABC_CALLOC( int, nObj );
    Gia_Obj_t * pObj;

    for ( i = 0; i < nObj; i++ ) { pUf[i] = i; pChainId[i] = -1; }

    // Union every XOR gate with its XOR-gate fanins.
    Gia_ManForEachAnd( p, pObj, i )
    {
        int f0, f1;
        if ( !Gia_ObjIsXor(pObj) ) continue;
        f0 = Gia_ObjFaninId0(pObj, i);
        f1 = Gia_ObjFaninId1(pObj, i);
        if ( Gia_ObjIsXor(Gia_ManObj(p, f0)) )
            Xcgrp_UfUnion(pUf, pRank, i, f0);
        if ( Gia_ObjIsXor(Gia_ManObj(p, f1)) )
            Xcgrp_UfUnion(pUf, pRank, i, f1);
    }

    // Resolve each XOR gate's canonical root.
    Gia_ManForEachAnd( p, pObj, i )
        if ( Gia_ObjIsXor(pObj) )
            pChainId[i] = Xcgrp_UfFind(pUf, i);

    ABC_FREE(pUf);
    ABC_FREE(pRank);
    return pChainId;   // caller must free
}

// Returns pChainLen[root] = number of XOR gates sharing that root.
static int * Gia_ManXcgrpComputeChainLens( Gia_Man_t * p, const int * pChainId )
{
    int i, nObj = Gia_ManObjNum(p);
    int * pLen = ABC_CALLOC( int, nObj );
    Gia_Obj_t * pObj;
    Gia_ManForEachAnd( p, pObj, i )
        if ( pChainId[i] >= 0 )
            pLen[ pChainId[i] ]++;
    return pLen;   // caller must free
}

////////////////////////////////////////////////////////////////////////
///                     DISTANCE TO CIRCUIT OUTPUT                   ///
////////////////////////////////////////////////////////////////////////

// Returns pDist[i] = shortest backward path length from node i to any CO.
// Unreachable nodes (from all COs) get -1.
// Computed by a single backward sweep in topological order (high-ID to low).
static int * Gia_ManXcgrpDistToCo( Gia_Man_t * p )
{
    int i, nObj = Gia_ManObjNum(p);
    int * pDist = ABC_FALLOC(int, nObj);   // -1 = unset
    Gia_Obj_t * pObj;

    Gia_ManForEachCo( p, pObj, i )
        pDist[ Gia_ObjId(p, pObj) ] = 0;

    // GIA stores objects in topological order (ascending ID), so sweeping
    // from high to low is a valid single-pass backward BFS.
    for ( i = nObj - 1; i >= 0; i-- )
    {
        int d, f;
        pObj = Gia_ManObj(p, i);
        if ( pDist[i] < 0 ) continue;   // node unreachable from any CO yet
        d = pDist[i] + 1;
        if ( Gia_ObjIsCo(pObj) )
        {
            f = Gia_ObjFaninId0(pObj, i);
            if ( pDist[f] < 0 || pDist[f] > d ) pDist[f] = d;
        }
        else if ( Gia_ObjIsAnd(pObj) )
        {
            f = Gia_ObjFaninId0(pObj, i);
            if ( pDist[f] < 0 || pDist[f] > d ) pDist[f] = d;
            f = Gia_ObjFaninId1(pObj, i);
            if ( pDist[f] < 0 || pDist[f] > d ) pDist[f] = d;
        }
    }
    return pDist;   // caller must free
}

////////////////////////////////////////////////////////////////////////
///                     PIVOT SCORING AND SELECTION                  ///
////////////////////////////////////////////////////////////////////////

// Score formula (FastLEC Algorithm 1, adapted for sequential):
//   score[v] = chainLen(v)^2 / (distToCO(v) + 1)
// Only XOR gates in chains of length >= 2 receive a positive score.
// Higher score => better pivot: long chain, close to circuit outputs.
static float * Gia_ManXcgrpComputeScores( Gia_Man_t * p,
                                           const int * pChainId,
                                           const int * pChainLen,
                                           const int * pDistToCo )
{
    int i, nObj = Gia_ManObjNum(p);
    float * pScores = ABC_CALLOC(float, nObj);
    Gia_Obj_t * pObj;
    Gia_ManForEachAnd( p, pObj, i )
    {
        int cid, clen, d;
        if ( !Gia_ObjIsXor(pObj) ) continue;
        cid  = pChainId[i];
        clen = (cid >= 0) ? pChainLen[cid] : 1;
        if ( clen < 2 ) continue;   // isolated XOR gate - no chain benefit
        d = pDistToCo[i];
        if ( d < 0 ) continue;      // unreachable from any CO
        pScores[i] = (float)(clen * clen) / (float)(d + 1);
    }
    return pScores;   // caller must free
}

// Returns the object ID of the highest-scored XOR gate, or -1 if none.
static int Gia_ManXcgrpSelectPivot( Gia_Man_t * p, const float * pScores )
{
    int i, iBest = -1;
    float fBest = 0.0f;
    Gia_Obj_t * pObj;
    Gia_ManForEachAnd( p, pObj, i )
        if ( pScores[i] > fBest ) { fBest = pScores[i]; iBest = i; }
    return iBest;
}

////////////////////////////////////////////////////////////////////////
///                   CONSTANT-PROPAGATION GIA DUP                  ///
////////////////////////////////////////////////////////////////////////

// Recursively copy internal node iObj from p into pNew using hash-based
// AND/XOR building.  Constants (including the forced pivot value) short-
// circuit at the first check because their Value fields are pre-set.
// COs are handled inline: they have one fanin and produce no logic output.
static int Gia_ManXcgrpDupRec( Gia_Man_t * pNew, Gia_Man_t * p, int iObj )
{
    Gia_Obj_t * pObj = Gia_ManObj(p, iObj);
    int iLit0, iLit1;
    if ( ~pObj->Value )        // already built or pre-set (CI / const / pivot)
        return pObj->Value;
    // Process fanin0 (present for both CO and AND/XOR).
    iLit0 = Gia_ManXcgrpDupRec(pNew, p, Gia_ObjFaninId0(pObj, iObj));
    iLit0 = Abc_LitNotCond(iLit0, Gia_ObjFaninC0(pObj));
    if ( Gia_ObjIsCo(pObj) )
        return (pObj->Value = Gia_ManAppendCo(pNew, iLit0));
    // Process fanin1 (AND and XOR nodes only).
    iLit1 = Gia_ManXcgrpDupRec(pNew, p, Gia_ObjFaninId1(pObj, iObj));
    iLit1 = Abc_LitNotCond(iLit1, Gia_ObjFaninC1(pObj));
    // Hash-rewrite: Gia_ManHashXor(pNew, 0, x) = x  (V XOR A = A when V=0)
    //               Gia_ManHashXor(pNew, 1, x) = ~x (V XOR A = ~A when V=1)
    if ( Gia_ObjIsXor(pObj) )
        return (pObj->Value = Gia_ManHashXor(pNew, iLit0, iLit1));
    else
        return (pObj->Value = Gia_ManHashAnd(pNew, iLit0, iLit1));
}

// Build a sequential copy of p with node iPivot forced to iConstLit (0 or 1).
// XOR-chain simplifications propagate automatically through the hash table.
// On return, p->pObj[i].Value holds the literal of original node i in pNew
// (or ~0 if that node was not reachable from any CO under the constant).
static Gia_Man_t * Gia_ManXcgrpSplitOnConst( Gia_Man_t * p, int iPivot, int iConstLit )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;

    pNew = Gia_ManStart(Gia_ManObjNum(p));
    pNew->pName = Abc_UtilStrsav(p->pName);
    pNew->pSpec = Abc_UtilStrsav(p->pSpec);
    Gia_ManHashStart(pNew);

    // Reset all Value fields to "unvisited" (-1 / ~0).
    Gia_ManFillValue(p);

    // Pre-set terminals: const-0 node and the forced pivot.
    // The pivot is always an AND/XOR node (never a CI), so it is safe to
    // set its Value here and still build CIs properly below.
    Gia_ManConst0(p)->Value = 0;                      // literal 0 = const-0
    Gia_ManObj(p, iPivot)->Value = iConstLit;         // literal 0 (V=0) or 1 (V=1)

    // Pre-create all CIs in order so the PI / RO numbering is preserved.
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);

    // Walk every CO; the recursive DFS builds all reachable logic nodes.
    // CO nodes themselves are appended inside Gia_ManXcgrpDupRec.
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManXcgrpDupRec(pNew, p, Gia_ObjId(p, pObj));

    Gia_ManHashStop(pNew);
    Gia_ManSetRegNum(pNew, Gia_ManRegNum(p));
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                  BACK-MAPPING: sub-AIG -> original ID            ///
////////////////////////////////////////////////////////////////////////

// After Gia_ManXcgrpSplitOnConst, p->pObj[i].Value = literal in pPart.
// This routine builds the reverse map: pPart->pObj[j].Value = original ID i.
// Must be called BEFORE the next SplitOnConst call (which resets p's Values).
// COs in p are skipped; they are not equivalence candidates.
static void Xcgrp_SetBackMap( Gia_Man_t * p, Gia_Man_t * pPart )
{
    Gia_Obj_t * pObj;
    int i, jNew;
    Gia_ManFillValue(pPart);   // initialize pPart's Values to ~0 ("not mapped")
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( !~pObj->Value ) continue;              // not reachable in this split
        if ( Gia_ObjIsCo(pObj) ) continue;         // COs are not equiv candidates
        jNew = Abc_Lit2Var(pObj->Value);
        if ( jNew >= Gia_ManObjNum(pPart) ) continue;
        // Take the first original node that maps here (smallest ID = representative).
        if ( Gia_ManObj(pPart, jNew)->Value == ~0 )
            Gia_ManObj(pPart, jNew)->Value = (unsigned)i;
    }
}

////////////////////////////////////////////////////////////////////////
///                 EQUIVALENCE INTERSECTION MERGE                   ///
////////////////////////////////////////////////////////////////////////

// Collect equivalences from one sub-AIG into pEquiv[origI] = origR (repr).
// -1 in pEquiv[i] means node i has no equivalence in this sub-problem.
// Polarity is NOT tracked here: Gia_ManCorrReduce reads polarity from the
// original AIG's fPhase bits (set by Gia_ManSetPhase on the original).
// Soundness: if (origI, origR) appears in BOTH sub-problems' intersections,
// it is equivalent in the full circuit; the original's fPhase bits then
// correctly encode the polarity (same or complementary) because both
// sub-problems use fPhase values consistent with the original's simulation.
static void Xcgrp_CollectEquivs( Gia_Man_t * pPart, int * pEquiv, int nOrig )
{
    Gia_Obj_t * pObj;
    int i, iRepr, origI, origR;
    Gia_ManForEachObj( pPart, pObj, i )
    {
        if ( !Gia_ObjHasRepr(pPart, i) ) continue;
        iRepr = Gia_ObjRepr(pPart, i);
        origI = (int)Gia_ManObj(pPart, i)->Value;
        origR = (int)Gia_ManObj(pPart, iRepr)->Value;
        // Skip nodes with no back-mapping (Value == ~0, cast to -1).
        if ( origI < 0 || origI >= nOrig ) continue;
        if ( origR < 0 || origR >= nOrig ) continue;
        // Normalize: representative = smaller original ID (GIA convention).
        if ( origI < origR ) { int t = origI; origI = origR; origR = t; }
        pEquiv[origI] = origR;
    }
}

// Intersect equivalences from both sub-problems and write into p->pReprs.
// Only pairs that appear in BOTH sub-problems (same representative) are kept.
// Polarity is determined implicitly by the original AIG's fPhase bits.
static void Gia_ManXcgrpMergeEquivs( Gia_Man_t * p,
                                      Gia_Man_t * pPart0,
                                      Gia_Man_t * pPart1 )
{
    int i, nObj = Gia_ManObjNum(p);
    int * pEquiv0 = ABC_FALLOC(int, nObj);
    int * pEquiv1 = ABC_FALLOC(int, nObj);

    Xcgrp_CollectEquivs(pPart0, pEquiv0, nObj);
    Xcgrp_CollectEquivs(pPart1, pEquiv1, nObj);

    assert( p->pReprs == NULL && p->pNexts == NULL );
    p->pReprs = ABC_CALLOC(Gia_Rpr_t, nObj);
    for ( i = 0; i < nObj; i++ )
        Gia_ObjSetRepr(p, i, GIA_VOID);

    // Intersection: keep only pairs agreed upon by both sub-problems.
    for ( i = 0; i < nObj; i++ )
        if ( pEquiv0[i] != -1 && pEquiv0[i] == pEquiv1[i] )
            p->pReprs[i].iRepr = (unsigned)pEquiv0[i];

    p->pNexts = Gia_ManDeriveNexts(p);

    ABC_FREE(pEquiv0);
    ABC_FREE(pEquiv1);
}

////////////////////////////////////////////////////////////////////////
///                    PARALLEL SOLVE (pthreads)                    ///
////////////////////////////////////////////////////////////////////////

#ifdef ABC_USE_PTHREADS
static void * Xcgrp_ThreadSolve( void * pArg )
{
    Xcgrp_Thread_t * pT = (Xcgrp_Thread_t *)pArg;
    pT->pSolveFunc(pT->pPart, pT->pPars);
    return NULL;
}
#endif

// Run pSolveFunc on both sub-AIGs.  If pars->nProcs > 1 and pthreads are
// compiled in, run both in parallel; otherwise fall back to sequential.
static void Xcgrp_SolveParts( Gia_Man_t * pPart0, Gia_Man_t * pPart1,
                               Cec_ParCor_t * pPars,
                               Xcgrp_SolveFunc_t pSolveFunc )
{
#ifdef ABC_USE_PTHREADS
    if ( pPars->nProcs > 1 )
    {
        pthread_t thr0, thr1;
        Xcgrp_Thread_t t0 = { pPart0, pPars, pSolveFunc };
        Xcgrp_Thread_t t1 = { pPart1, pPars, pSolveFunc };
        pthread_create(&thr0, NULL, Xcgrp_ThreadSolve, &t0);
        pthread_create(&thr1, NULL, Xcgrp_ThreadSolve, &t1);
        pthread_join(thr0, NULL);
        pthread_join(thr1, NULL);
        return;
    }
#endif
    pSolveFunc(pPart0, pPars);
    pSolveFunc(pPart1, pPars);
}

////////////////////////////////////////////////////////////////////////
///                       TOP-LEVEL XCGRP ENTRY                     ///
////////////////////////////////////////////////////////////////////////

// Full XCGRP pipeline: score -> select pivot -> split -> solve -> merge.
// pSolveFunc is the pluggable correspondence engine (NULL = default SAT).
// Returns the reduced AIG; caller is responsible for freeing it.
Gia_Man_t * Gia_ManXcgrpCorrespondence( Gia_Man_t * pAig, Cec_ParCor_t * pPars,
                                         Xcgrp_SolveFunc_t pSolveFunc )
{
    extern Gia_Man_t * Gia_ManCorrReduce( Gia_Man_t * p );
    Gia_Man_t * pPart0, * pPart1, * pNew, * pTemp;
    int * pChainId, * pChainLen, * pDistToCo;
    float * pScores;
    int iPivot;

    // --- Step 1: XOR chain extraction (Union-Find) ---
    pChainId  = Gia_ManXcgrpComputeChainIds(pAig);
    pChainLen = Gia_ManXcgrpComputeChainLens(pAig, pChainId);

    // --- Step 2: Backward distance and node scoring ---
    pDistToCo = Gia_ManXcgrpDistToCo(pAig);
    pScores   = Gia_ManXcgrpComputeScores(pAig, pChainId, pChainLen, pDistToCo);

    // --- Step 3: Pivot selection ---
    iPivot = Gia_ManXcgrpSelectPivot(pAig, pScores);

    ABC_FREE(pChainId);
    ABC_FREE(pChainLen);
    ABC_FREE(pDistToCo);
    ABC_FREE(pScores);

    if ( iPivot < 0 )
    {
        // No XOR chain with length >= 2 found; fall back to plain scorr.
        if ( pPars->fVerbose )
            Abc_Print(1, "XCGRP: no XOR chains found, falling back to standard scorr.\n");
        return Cec_ManLSCorrespondence(pAig, pPars);
    }

    if ( pPars->fVerbose )
        Abc_Print(1, "XCGRP: pivot = node %d.\n", iPivot);

    // --- Step 4: Build two sub-AIGs via constant propagation ---
    // First split (V=0): pAig->Value fields are set to pPart0 literals.
    pPart0 = Gia_ManXcgrpSplitOnConst(pAig, iPivot, 0);
    // Build reverse map (pPart0 nodes -> original IDs) before Values are reset.
    Xcgrp_SetBackMap(pAig, pPart0);

    // Second split (V=1): Gia_ManFillValue inside SplitOnConst resets pAig's Values.
    pPart1 = Gia_ManXcgrpSplitOnConst(pAig, iPivot, 1);
    Xcgrp_SetBackMap(pAig, pPart1);

    // --- Step 5: Run correspondence engine on each sub-AIG ---
    if ( pSolveFunc == NULL )
        pSolveFunc = Cec_ManLSCorrespondenceClasses;
    Xcgrp_SolveParts(pPart0, pPart1, pPars, pSolveFunc);

    // --- Step 6: Intersect equivalences and apply to the original AIG ---
    ABC_FREE(pAig->pReprs);
    ABC_FREE(pAig->pNexts);
    Gia_ManXcgrpMergeEquivs(pAig, pPart0, pPart1);

    Gia_ManStop(pPart0);
    Gia_ManStop(pPart1);

    // Reduce the AIG using the confirmed equivalences, then clean up.
    pNew = Gia_ManCorrReduce(pAig);
    pNew = Gia_ManSeqCleanup(pTemp = pNew);
    Gia_ManStop(pTemp);
    return pNew;
}

// Public entry point with verbose summary.  Uses the default SAT engine.
Gia_Man_t * Cec_ManXcgrpCorrespondence( Gia_Man_t * pAig, Cec_ParCor_t * pPars )
{
    Gia_Man_t * pNew;
    ABC_FREE(pAig->pReprs);
    ABC_FREE(pAig->pNexts);
    pNew = Gia_ManXcgrpCorrespondence(pAig, pPars, NULL);
    if ( pPars->fVerbose )
        Abc_Print(1, "XCGRP: NBeg=%d NEnd=%d (%.1f%%). RBeg=%d REnd=%d (%.1f%%).\n",
            Gia_ManAndNum(pAig), Gia_ManAndNum(pNew),
            100.0*(Gia_ManAndNum(pAig)-Gia_ManAndNum(pNew))/(Gia_ManAndNum(pAig)?Gia_ManAndNum(pAig):1),
            Gia_ManRegNum(pAig), Gia_ManRegNum(pNew),
            100.0*(Gia_ManRegNum(pAig)-Gia_ManRegNum(pNew))/(Gia_ManRegNum(pAig)?Gia_ManRegNum(pAig):1));
    return pNew;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
