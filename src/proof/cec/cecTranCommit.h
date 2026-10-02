// Conflict selection and immutable-snapshot commit.
// Private implementation fragment included only by cecTrans.c.

// Exercise reuse across different roots/supports and Page boundaries, including
// generic callers whose covered/used sets change between Pages.  The legacy
// per-candidate scratch path is the oracle for gains, kill-sets and ordering.
static int Cec_TranFrontierGainSelfTest()
{
    Gia_Man_t * p = Gia_ManStart( 16 );
    Cec_TranCandVec_t Page = {0}, Seq = {0}, Expected = {0};
    Cec_TranRoot_t Roots[4];
    Cec_TranCand_t Cand;
    Cec_TranProf_t * pProf = ABC_CALLOC( Cec_TranProf_t, 1 );
    Vec_Int_t * vMffc = Vec_IntAlloc( 8 );
    Vec_Int_t * vOracle = Vec_IntAlloc( 8 );
    Vec_Int_t * vSupport = Vec_IntAlloc( 8 );
    char * pMark, * pOracle, * pCovered, * pUsed;
    int * pRefs, * pSaved, * pOriginal;
    int A, B, C, X, U, V, Root, nObjs, Bytes;
    int State, Target, Out, Gates, i, r, Gain, OracleGain;
    A = Gia_ManAppendCi( p );
    B = Gia_ManAppendCi( p );
    C = Gia_ManAppendCi( p );
    X = Gia_ManAppendAnd( p, A, B );
    U = Gia_ManAppendAnd( p, X, C );
    V = Gia_ManAppendAnd( p, X, Abc_LitNot(C) );
    Root = Gia_ManAppendAnd( p, U, V );
    Gia_ManAppendCo( p, Root );
    Gia_ManCreateRefs( p );
    nObjs = Gia_ManObjNum(p);
    Bytes = sizeof(int) * nObjs;
    pMark = ABC_CALLOC( char, nObjs );
    pOracle = ABC_CALLOC( char, nObjs );
    pCovered = ABC_CALLOC( char, nObjs );
    pUsed = ABC_CALLOC( char, nObjs );
    pSaved = ABC_ALLOC( int, nObjs );
    pOriginal = ABC_ALLOC( int, nObjs );
    memcpy( pOriginal, p->pRefs, Bytes );

    for ( State = 0; State < 4; State++ )
    {
        pCovered[Abc_Lit2Var(U)] = (State & 1) != 0;
        pUsed[Abc_Lit2Var(X)] = (State & 2) != 0;
        pRefs = Cec_TranMffcRefsStart( p, pCovered );
        memcpy( pSaved, pRefs, Bytes );
        Cec_TranCandVecClear( &Page );
        for ( Target = Abc_Lit2Var(X); Target <= Abc_Lit2Var(Root); Target++ )
            for ( Out = 0; Out <= Abc_Lit2Var(Root); Out++ )
                for ( Gates = 0; Gates < 2; Gates++ )
                {
                    memset( &Cand, 0, sizeof(Cand) );
                    Cand.iTarget = Target;
                    Cand.nGates = Gates;
                    Cand.nKind = Gates ? CEC_TRAN_CAND_CONSTR :
                        Out ? CEC_TRAN_CAND_EXIST : CEC_TRAN_CAND_CONST;
                    Cand.iOut = Gates ? Cec_TranRecipeGateCode(0, 0) :
                        Abc_Var2Lit(Out, 0);
                    if ( Gates )
                    {
                        Cand.Recipe = Cec_TranRecipeAlloc( 2 );
                        Cand.Recipe[0] = Abc_Var2Lit(Out, 0);
                        Cand.Recipe[1] = C;
                    }
                    Gain = Cec_TranCandDynamicGainWithRefs( p, &Cand,
                        pCovered, pUsed, pRefs, pMark, vMffc, vSupport );
                    OracleGain = Cec_TranCandDynamicGain( p, &Cand,
                        pCovered, pUsed, pOracle, vOracle, vSupport );
                    assert( Gain == OracleGain );
                    assert( Vec_IntSize(vMffc) == Vec_IntSize(vOracle) );
                    assert( !memcmp(pMark, pOracle, nObjs) );
                    assert( !memcmp(pRefs, pSaved, Bytes) );
                    assert( !memcmp(p->pRefs, pOriginal, Bytes) );
                    if ( State == 0 && Target == Abc_Lit2Var(Root) && !Gates )
                    {
                        if ( Out == 0 ) assert( Gain == 4 );
                        if ( Out == Abc_Lit2Var(X) ) assert( Gain == 3 );
                        if ( Out == Target ) assert( Gain == -1 );
                    }
                    // Include already-tried candidates in the Page to check
                    // frontier filtering as well as live candidate ordering.
                    if ( Out == 0 && Gates )
                        Cand.nStatus = CEC_TRAN_STATE_TRIED_SEQ;
                    Cec_TranCandVecPush( &Page, Cand );
                    Cec_TranCandRecipeRelease( &Cand );
                }
        ABC_FREE( pRefs );
        memset( Roots, 0, sizeof(Roots) );
        for ( r = 0; r < 4; r++ )
            Roots[r].iObj = Abc_Lit2Var(X) + r;
        Cec_TranRootRefreshPotential( p, Roots, 4, pCovered, pUsed,
            pOracle, vOracle, NULL );
        Cec_TranCandVecClear( &Expected );
        for ( r = 0; r < 4 && Roots[r].nMffc > 0; r++ )
            for ( i = 0; i < Page.nSize; i++ )
            {
                Cand = Page.pArray[i];
                if ( Cand.iTarget != Roots[r].iObj ||
                     Cand.nStatus != CEC_TRAN_STATE_CANDIDATE )
                    continue;
                // Preserve the historical raw oracle by default; the
                // explicit actual-cost arm must use the frozen-DAG oracle.
                Cand.Gain = Cec_TranQualityActualCost() ?
                    Cec_TranQualityCostGainOne(p, &Cand, pCovered, pUsed, NULL) :
                    Cec_TranCandDynamicGain( p, &Cand,
                        pCovered, pUsed, pOracle, vOracle, vSupport );
                if ( Cand.Gain <= 0 )
                    continue;
                Cand.nMffc = Roots[r].nMffc;
                Cec_TranCandVecPush( &Expected, Cand );
            }
        qsort( Expected.pArray, Expected.nSize, sizeof(Cec_TranCand_t),
            Cec_TranCandRootHeuristicCompare );
        // A second Page must start with fresh scratch, including when generic
        // root refresh is requested after virtual-selection changes.
        for ( i = 0; i < 2; i++ )
        {
            Cec_TranRootPrepareSeqFrontier( p, Roots, 4, &Page, pCovered,
                pUsed, pMark, vMffc, vSupport, i, &Seq, pProf );
            assert( Seq.nSize == Expected.nSize );
            assert( !memcmp(Seq.pArray, Expected.pArray,
                sizeof(Cec_TranCand_t) * Seq.nSize) );
            assert( !memcmp(p->pRefs, pOriginal, Bytes) );
        }
        // Clear both independent mark workspaces before the next oracle run.
        Cec_TranMffcScratchClear( pMark, vMffc );
        Cec_TranMffcScratchClear( pOracle, vOracle );
    }
    Cec_TranCandVecClear( &Page );
    Cec_TranRootPrepareSeqFrontier( p, Roots, 4, &Page, pCovered,
        pUsed, pMark, vMffc, vSupport, 0, &Seq, pProf );
    assert( Seq.nSize == 0 );
    ABC_FREE( pMark );
    ABC_FREE( pOracle );
    ABC_FREE( pCovered );
    ABC_FREE( pUsed );
    ABC_FREE( pSaved );
    ABC_FREE( pOriginal );
    ABC_FREE( pProf );
    Vec_IntFree( vMffc );
    Vec_IntFree( vOracle );
    Vec_IntFree( vSupport );
    Cec_TranCandVecStop( &Page );
    Cec_TranCandVecStop( &Seq );
    Cec_TranCandVecStop( &Expected );
    Gia_ManStop( p );
    return 1;
}

// The conflict graph is stored by object incidence instead of materializing
// every edge.  An even incidence is a removable/MFFC membership and an odd
// incidence is replacement support.  Two vertices conflict on MFFC/MFFC or
// MFFC/support incidence; shared read-only support is intentionally legal.
typedef struct Cec_TranConflictGraph_t_ Cec_TranConflictGraph_t;
struct Cec_TranConflictGraph_t_
{
    Vec_Wec_t * vUsers;
    Vec_Int_t * vMffcBeg;
    Vec_Int_t * vMffcData;
    Vec_Int_t * vSuppBeg;
    Vec_Int_t * vSuppData;
    unsigned *  pSeen;
    unsigned    TravId;
    int         nVertices;
};

static void Cec_TranConflictGraphStart( Cec_TranConflictGraph_t * pGraph,
    int nObjs )
{
    memset( pGraph, 0, sizeof(Cec_TranConflictGraph_t) );
    pGraph->vUsers = Vec_WecStart( nObjs );
    pGraph->vMffcBeg = Vec_IntAlloc( 64 );
    pGraph->vMffcData = Vec_IntAlloc( 256 );
    pGraph->vSuppBeg = Vec_IntAlloc( 64 );
    pGraph->vSuppData = Vec_IntAlloc( 256 );
}

static void Cec_TranConflictGraphAdd( Cec_TranConflictGraph_t * pGraph,
    Vec_Int_t * vMffc, Vec_Int_t * vSupport )
{
    int iVertex = pGraph->nVertices++;
    int i, iObj;
    Vec_IntPush( pGraph->vMffcBeg, Vec_IntSize(pGraph->vMffcData) );
    Vec_IntForEachEntry( vMffc, iObj, i )
    {
        Vec_IntPush( pGraph->vMffcData, iObj );
        Vec_IntPush( Vec_WecEntry(pGraph->vUsers, iObj),
            Abc_Var2Lit(iVertex, 0) );
    }
    Vec_IntPush( pGraph->vSuppBeg, Vec_IntSize(pGraph->vSuppData) );
    Vec_IntForEachEntry( vSupport, iObj, i )
    {
        Vec_IntPush( pGraph->vSuppData, iObj );
        Vec_IntPush( Vec_WecEntry(pGraph->vUsers, iObj),
            Abc_Var2Lit(iVertex, 1) );
    }
}

static void Cec_TranConflictGraphFinalize( Cec_TranConflictGraph_t * pGraph )
{
    Vec_IntPush( pGraph->vMffcBeg, Vec_IntSize(pGraph->vMffcData) );
    Vec_IntPush( pGraph->vSuppBeg, Vec_IntSize(pGraph->vSuppData) );
    pGraph->pSeen = ABC_CALLOC( unsigned, pGraph->nVertices );
}

static void Cec_TranConflictGraphStop( Cec_TranConflictGraph_t * pGraph )
{
    Vec_WecFree( pGraph->vUsers );
    Vec_IntFree( pGraph->vMffcBeg );
    Vec_IntFree( pGraph->vMffcData );
    Vec_IntFree( pGraph->vSuppBeg );
    Vec_IntFree( pGraph->vSuppData );
    ABC_FREE( pGraph->pSeen );
    memset( pGraph, 0, sizeof(Cec_TranConflictGraph_t) );
}

static void Cec_TranConflictGraphCollectList(
    Cec_TranConflictGraph_t * pGraph, Vec_Int_t * vUsers,
    int iVertex, int fRequireMffc, Vec_Int_t * vNeighbors )
{
    int i, User, iOther;
    Vec_IntForEachEntry( vUsers, User, i )
    {
        if ( fRequireMffc && Abc_LitIsCompl(User) )
            continue;
        iOther = Abc_Lit2Var( User );
        if ( iOther == iVertex || pGraph->pSeen[iOther] == pGraph->TravId )
            continue;
        pGraph->pSeen[iOther] = pGraph->TravId;
        Vec_IntPush( vNeighbors, iOther );
    }
}

static void Cec_TranConflictGraphNeighbors(
    Cec_TranConflictGraph_t * pGraph, int iVertex,
    Vec_Int_t * vNeighbors )
{
    int i, iObj;
    Vec_IntClear( vNeighbors );
    if ( ++pGraph->TravId == 0 )
    {
        memset( pGraph->pSeen, 0,
            sizeof(unsigned) * pGraph->nVertices );
        pGraph->TravId = 1;
    }
    pGraph->pSeen[iVertex] = pGraph->TravId;
    for ( i = Vec_IntEntry(pGraph->vMffcBeg, iVertex);
          i < Vec_IntEntry(pGraph->vMffcBeg, iVertex + 1); i++ )
    {
        iObj = Vec_IntEntry( pGraph->vMffcData, i );
        Cec_TranConflictGraphCollectList( pGraph,
            Vec_WecEntry(pGraph->vUsers, iObj), iVertex, 0, vNeighbors );
    }
    for ( i = Vec_IntEntry(pGraph->vSuppBeg, iVertex);
          i < Vec_IntEntry(pGraph->vSuppBeg, iVertex + 1); i++ )
    {
        iObj = Vec_IntEntry( pGraph->vSuppData, i );
        Cec_TranConflictGraphCollectList( pGraph,
            Vec_WecEntry(pGraph->vUsers, iObj), iVertex, 1, vNeighbors );
    }
}

typedef struct Cec_TranWaveHeap_t_ Cec_TranWaveHeap_t;
struct Cec_TranWaveHeap_t_
{
    int * pHeap;
    int * pPos;
    long long * pLoss;
    int   nSize;
    Cec_TranCandVec_t const * pVertices;
};

static int Cec_TranWaveHeapBetter( Cec_TranWaveHeap_t const * pHeap,
    int iV0, int iV1 )
{
    Cec_TranCand_t const * pC0 = pHeap->pVertices->pArray + iV0;
    Cec_TranCand_t const * pC1 = pHeap->pVertices->pArray + iV1;
    // Compare Gain(c)^2 / (Gain(c) + Loss(c)) without division.  long double
    // avoids overflowing a 64-bit cross product on large proved pools while
    // the deterministic tie-breaks below keep equal priorities stable.
    long double Left = (long double)pC0->Gain * pC0->Gain *
        (pC1->Gain + pHeap->pLoss[iV1]);
    long double Right = (long double)pC1->Gain * pC1->Gain *
        (pC0->Gain + pHeap->pLoss[iV0]);
    if ( Left != Right )
        return Left > Right;
    if ( pC0->Gain != pC1->Gain )
        return pC0->Gain > pC1->Gain;
    if ( pC0->nMffc != pC1->nMffc )
        return pC0->nMffc > pC1->nMffc;
    if ( pC0->iTarget != pC1->iTarget )
        return pC0->iTarget > pC1->iTarget;
    return iV0 < iV1;
}

static void Cec_TranWaveHeapSwap( Cec_TranWaveHeap_t * pHeap,
    int i, int k )
{
    int Temp = pHeap->pHeap[i];
    pHeap->pHeap[i] = pHeap->pHeap[k];
    pHeap->pHeap[k] = Temp;
    pHeap->pPos[pHeap->pHeap[i]] = i;
    pHeap->pPos[pHeap->pHeap[k]] = k;
}

static void Cec_TranWaveHeapUp( Cec_TranWaveHeap_t * pHeap, int i )
{
    int Parent;
    while ( i > 0 )
    {
        Parent = (i - 1) >> 1;
        if ( !Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[i],
                pHeap->pHeap[Parent]) )
            break;
        Cec_TranWaveHeapSwap( pHeap, i, Parent );
        i = Parent;
    }
}

static void Cec_TranWaveHeapDown( Cec_TranWaveHeap_t * pHeap, int i )
{
    int Child;
    while ( (Child = 2 * i + 1) < pHeap->nSize )
    {
        if ( Child + 1 < pHeap->nSize &&
             Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[Child + 1],
                pHeap->pHeap[Child]) )
            Child++;
        if ( !Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[Child],
                pHeap->pHeap[i]) )
            break;
        Cec_TranWaveHeapSwap( pHeap, i, Child );
        i = Child;
    }
}

static void Cec_TranWaveHeapStart( Cec_TranWaveHeap_t * pHeap,
    Cec_TranCandVec_t const * pVertices, long long * pLoss )
{
    int i;
    memset( pHeap, 0, sizeof(Cec_TranWaveHeap_t) );
    pHeap->nSize = pVertices->nSize;
    pHeap->pHeap = ABC_ALLOC( int, pHeap->nSize );
    pHeap->pPos = ABC_ALLOC( int, pHeap->nSize );
    pHeap->pLoss = pLoss;
    pHeap->pVertices = pVertices;
    for ( i = 0; i < pHeap->nSize; i++ )
        pHeap->pHeap[i] = pHeap->pPos[i] = i;
    for ( i = pHeap->nSize / 2; i-- > 0; )
        Cec_TranWaveHeapDown( pHeap, i );
}

static void Cec_TranWaveHeapRemove( Cec_TranWaveHeap_t * pHeap,
    int iVertex )
{
    int i = pHeap->pPos[iVertex];
    if ( i < 0 )
        return;
    pHeap->pPos[iVertex] = -1;
    pHeap->nSize--;
    if ( i == pHeap->nSize )
        return;
    pHeap->pHeap[i] = pHeap->pHeap[pHeap->nSize];
    pHeap->pPos[pHeap->pHeap[i]] = i;
    if ( i > 0 && Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[i],
            pHeap->pHeap[(i - 1) >> 1]) )
        Cec_TranWaveHeapUp( pHeap, i );
    else
        Cec_TranWaveHeapDown( pHeap, i );
}

static int Cec_TranWaveHeapPop( Cec_TranWaveHeap_t * pHeap )
{
    int iVertex = pHeap->pHeap[0];
    Cec_TranWaveHeapRemove( pHeap, iVertex );
    return iVertex;
}

static void Cec_TranWaveHeapStop( Cec_TranWaveHeap_t * pHeap )
{
    ABC_FREE( pHeap->pHeap );
    ABC_FREE( pHeap->pPos );
    memset( pHeap, 0, sizeof(Cec_TranWaveHeap_t) );
}

// Compute the opportunity loss of one candidate in the current induced
// conflict graph.  Conflicting candidates are compressed by root: because at
// most one candidate of a root can be committed, that root contributes only
// the largest gain among its active conflicting candidates.
static long long Cec_TranConflictGraphRootLoss(
    Cec_TranConflictGraph_t * pGraph, Cec_TranCandVec_t const * pVertices,
    int iVertex, char const * pActive, Vec_Int_t * vNeighbors,
    int * pRootBest, unsigned * pRootSeen, unsigned * pRootTravId,
    int * pnActiveNeighbors )
{
    long long Loss = 0;
    int i, iOther, iRoot, Gain, nActive = 0;
    if ( ++*pRootTravId == 0 )
    {
        memset( pRootSeen, 0,
            sizeof(unsigned) * Vec_WecSize(pGraph->vUsers) );
        *pRootTravId = 1;
    }
    Cec_TranConflictGraphNeighbors( pGraph, iVertex, vNeighbors );
    Vec_IntForEachEntry( vNeighbors, iOther, i )
    {
        if ( !pActive[iOther] )
            continue;
        nActive++;
        iRoot = pVertices->pArray[iOther].iTarget;
        Gain = pVertices->pArray[iOther].Gain;
        assert( iRoot >= 0 && iRoot < Vec_WecSize(pGraph->vUsers) );
        assert( Gain > 0 );
        if ( pRootSeen[iRoot] != *pRootTravId )
        {
            pRootSeen[iRoot] = *pRootTravId;
            pRootBest[iRoot] = Gain;
            Loss += Gain;
        }
        else if ( pRootBest[iRoot] < Gain )
        {
            Loss += Gain - pRootBest[iRoot];
            pRootBest[iRoot] = Gain;
        }
    }
    if ( pnActiveNeighbors )
        *pnActiveNeighbors = nActive;
    return Loss;
}

// Dynamic root-compressed weighted-loss GWMIN.  The priority is
//
//        Gain(c)^2 / (Gain(c) + Loss(c)),
//
// where Loss(c) sums the best conflicting gain once per distinct root in the
// current induced graph.  Removing a closed neighborhood can only decrease
// the loss of its remaining neighbors, so only those heap entries are
// recomputed and promoted.
static long long Cec_TranConflictGraphGwmin(
    Cec_TranConflictGraph_t * pGraph, Cec_TranCandVec_t const * pVertices,
    char * pChosen, long long * pnEdges, int * pFirstGain )
{
    Cec_TranWaveHeap_t Heap;
    Vec_Int_t * vNeighbors = Vec_IntAlloc( 64 );
    Vec_Int_t * vRemoved = Vec_IntAlloc( 64 );
    Vec_Int_t * vDirty = Vec_IntAlloc( 64 );
    long long * pLoss = ABC_ALLOC( long long, pVertices->nSize );
    char * pActive = ABC_ALLOC( char, pVertices->nSize );
    char * pDirty = ABC_CALLOC( char, pVertices->nSize );
    int * pRootBest = ABC_ALLOC( int, Vec_WecSize(pGraph->vUsers) );
    unsigned * pRootSeen = ABC_CALLOC( unsigned,
        Vec_WecSize(pGraph->vUsers) );
    unsigned RootTravId = 0;
    long long SumDegree = 0, Weight = 0;
    int i, k, iVertex, iOther, nActiveNeighbors;
    memset( pChosen, 0, pVertices->nSize );
    memset( pActive, 1, pVertices->nSize );
    *pFirstGain = 0;
    for ( i = 0; i < pVertices->nSize; i++ )
    {
        pLoss[i] = Cec_TranConflictGraphRootLoss( pGraph, pVertices, i,
            pActive, vNeighbors, pRootBest, pRootSeen, &RootTravId,
            &nActiveNeighbors );
        SumDegree += nActiveNeighbors;
    }
    *pnEdges = SumDegree / 2;
    Cec_TranWaveHeapStart( &Heap, pVertices, pLoss );
    while ( Heap.nSize )
    {
        iVertex = Cec_TranWaveHeapPop( &Heap );
        assert( pActive[iVertex] );
        if ( Weight == 0 )
            *pFirstGain = pVertices->pArray[iVertex].Gain;
        pActive[iVertex] = 0;
        pChosen[iVertex] = 1;
        Weight += pVertices->pArray[iVertex].Gain;
        Vec_IntClear( vRemoved );
        Vec_IntPush( vRemoved, iVertex );
        Cec_TranConflictGraphNeighbors( pGraph, iVertex, vNeighbors );
        Vec_IntForEachEntry( vNeighbors, iOther, i )
            if ( pActive[iOther] )
            {
                pActive[iOther] = 0;
                Cec_TranWaveHeapRemove( &Heap, iOther );
                Vec_IntPush( vRemoved, iOther );
            }
        Vec_IntClear( vDirty );
        Vec_IntForEachEntry( vRemoved, iOther, i )
        {
            Cec_TranConflictGraphNeighbors( pGraph, iOther, vNeighbors );
            Vec_IntForEachEntry( vNeighbors, iVertex, k )
                if ( pActive[iVertex] && !pDirty[iVertex] )
                {
                    pDirty[iVertex] = 1;
                    Vec_IntPush( vDirty, iVertex );
                }
        }
        Vec_IntForEachEntry( vDirty, iVertex, i )
        {
            long long OldLoss = pLoss[iVertex];
            pLoss[iVertex] = Cec_TranConflictGraphRootLoss( pGraph,
                pVertices, iVertex, pActive, vNeighbors, pRootBest,
                pRootSeen, &RootTravId, NULL );
            assert( pLoss[iVertex] <= OldLoss );
            pDirty[iVertex] = 0;
            Cec_TranWaveHeapUp( &Heap, Heap.pPos[iVertex] );
        }
    }
    Cec_TranWaveHeapStop( &Heap );
    Vec_IntFree( vNeighbors );
    Vec_IntFree( vRemoved );
    Vec_IntFree( vDirty );
    ABC_FREE( pLoss );
    ABC_FREE( pActive );
    ABC_FREE( pDirty );
    ABC_FREE( pRootBest );
    ABC_FREE( pRootSeen );
    return Weight;
}

// Audit the frozen-cost independent set with the exact operation used by the
// real commit: one topological bundle duplication followed by cleanup.  The
// structural conflict graph normally makes the individual gains additive,
// but structural hashing can expose an alias which is not represented by an
// object-incidence edge.  Keep the safety property explicit instead of
// weakening the commit assertion.
static int Cec_TranSelectedExactGain( Gia_Man_t * p,
    Cec_TranCandVec_t const * pVertices, char const * pChosen )
{
    Gia_Man_t * pDup, * pClean;
    Vec_Int_t * vSelected = Vec_IntAlloc( 64 );
    int i, Gain;
    for ( i = 0; i < pVertices->nSize; i++ )
        if ( pChosen[i] )
            Vec_IntPush( vSelected, i );
    if ( Vec_IntSize(vSelected) == 0 )
    {
        Vec_IntFree( vSelected );
        return 0;
    }
    pDup = Cec_TranDupRootBundle( p, pVertices->pArray, vSelected );
    pClean = Cec_TranCleanupKeepRegs( pDup, NULL );
    Gain = Cec_TranGain( p, pClean );
    Gia_ManStop( pDup );
    Gia_ManStop( pClean );
    Vec_IntFree( vSelected );
    return Gain;
}

// A rare non-additive bundle is repaired by one global, deterministic rule:
// visit the chosen candidates by decreasing frozen gain (then MFFC, target,
// and stable vertex index), and retain exactly the candidates whose measured
// bundle marginal is positive.  Replacing the estimate by that exact marginal
// makes the accounting telescope to the final cleanup gain.  This is a
// structural safety fallback, not a circuit-specific quality policy.
static long long Cec_TranRepairSelectedExact( Gia_Man_t * p,
    Cec_TranCandVec_t * pVertices, char * pChosen,
    long long Predicted )
{
    char * pOriginal = ABC_ALLOC( char, pVertices->nSize );
    char * pDone = ABC_CALLOC( char, pVertices->nSize );
    int * pFrozenGain = ABC_ALLOC( int, pVertices->nSize );
    int i, k, iBest, nOriginal = 0, nKept = 0;
    int Exact, Audited, Current = 0;
    abctime clk = Abc_Clock();
    memcpy( pOriginal, pChosen, pVertices->nSize );
    for ( i = 0; i < pVertices->nSize; i++ )
        pFrozenGain[i] = pVertices->pArray[i].Gain,
        nOriginal += pOriginal[i] != 0;
    Exact = Cec_TranSelectedExactGain( p, pVertices, pChosen );
    Audited = Exact;
    if ( Exact > 0 && Exact >= Predicted )
    {
        ABC_FREE( pOriginal );
        ABC_FREE( pDone );
        ABC_FREE( pFrozenGain );
        return Predicted;
    }

    memset( pChosen, 0, pVertices->nSize );
    for ( k = 0; k < nOriginal; k++ )
    {
        int Trial;
        iBest = -1;
        for ( i = 0; i < pVertices->nSize; i++ )
            if ( pOriginal[i] && !pDone[i] &&
                 (iBest < 0 || pFrozenGain[i] > pFrozenGain[iBest] ||
                  (pFrozenGain[i] == pFrozenGain[iBest] &&
                   (pVertices->pArray[i].nMffc >
                        pVertices->pArray[iBest].nMffc ||
                    (pVertices->pArray[i].nMffc ==
                         pVertices->pArray[iBest].nMffc &&
                     (pVertices->pArray[i].iTarget >
                          pVertices->pArray[iBest].iTarget ||
                      (pVertices->pArray[i].iTarget ==
                           pVertices->pArray[iBest].iTarget && i < iBest)))))) )
                iBest = i;
        assert( iBest >= 0 );
        pDone[iBest] = 1;
        pChosen[iBest] = 1;
        Trial = Cec_TranSelectedExactGain( p, pVertices, pChosen );
        if ( Trial <= Current )
        {
            pChosen[iBest] = 0;
            continue;
        }
        pVertices->pArray[iBest].Gain = Trial - Current;
        Current = Trial;
        nKept++;
    }
    assert( nKept > 0 && Current > 0 );
    Exact = Cec_TranSelectedExactGain( p, pVertices, pChosen );
    assert( Exact == Current );
    Abc_Print( 1, "stran-root exact bundle repair: predicted=%lld exact=%d original=%d kept=%d repaired-gain=%d audit-sec=%.6f policy=positive-exact-marginal.\n",
        Predicted, Audited, nOriginal, nKept, Current,
        Cec_TranTimeSec(Abc_Clock() - clk) );
    ABC_FREE( pOriginal );
    ABC_FREE( pDone );
    ABC_FREE( pFrozenGain );
    return Current;
}

static int Cec_TranRootConsumeProved( Gia_Man_t * p,
    Cec_TranCandVec_t * pProved, char * pCovered, char * pUsed,
    char * pSolved, char * pMffc, Vec_Int_t * vMffc, Vec_Int_t * vSupport,
    Cec_TranCandVec_t * pSelected, Cec_TranProf_t * pProf )
{
    Cec_TranFrozenHash_t FrozenHash;
    Cec_TranConflictGraph_t Graph;
    Cec_TranCandVec_t Vertices = {0};
    Vec_Int_t * vProvedIds = Vec_IntAlloc( 64 );
    Gia_Obj_t * pObj;
    int * pRefs = ABC_ALLOC( int, Gia_ManObjNum(p) );
    char * pChosen;
    long long nEdges = 0, SelectedWeight;
    int i, k, iObj, iFan, iProved, Gain;
    int nSelected = 0, nGainEvals = 0, nInitialProved = 0;
    int nInitialPositive = 0, InitialMaxGain = 0, FirstGain = 0;

    // This is the one structural refresh for the frozen commit wave.
    memcpy( pRefs, p->pRefs, sizeof(int) * Gia_ManObjNum(p) );
    Gia_ManForEachAnd( p, pObj, i )
        if ( pCovered[i] )
        {
            iFan = Gia_ObjFaninId0p( p, pObj );
            assert( pRefs[iFan] > 0 );
            pRefs[iFan]--;
            iFan = Gia_ObjFaninId1p( p, pObj );
            assert( pRefs[iFan] > 0 );
            pRefs[iFan]--;
        }
    Cec_TranFrozenHashStart( p, &FrozenHash );
    Cec_TranConflictGraphStart( &Graph, Gia_ManObjNum(p) );
    for ( i = 0; i < pProved->nSize; i++ )
    {
        Cec_TranCand_t Cand = pProved->pArray[i];
        if ( Cand.nStatus != CEC_TRAN_STATE_PROVED_COMB &&
             Cand.nStatus != CEC_TRAN_STATE_PROVED_SEQ )
            continue;
        nInitialProved++;
        if ( pCovered[Cand.iTarget] || pUsed[Cand.iTarget] )
        {
            pProf->nDirtyRootFreed++;
            continue;
        }
        Gain = Cec_TranCandFrozenGainWithRefs( p, &FrozenHash, &Cand,
            pCovered, pUsed, pRefs, pMffc, vMffc, vSupport );
        nGainEvals++;
        if ( Gain <= 0 )
        {
            pProf->nDirtySupportFreed++;
            continue;
        }
        nInitialPositive++;
        InitialMaxGain = Abc_MaxInt( InitialMaxGain, Gain );
        if ( Gain != Cand.Gain || Vec_IntSize(vMffc) != Cand.nMffc )
            pProf->nDirtyMffcChanged++;
        Cand.Gain = Gain;
        Cand.nMffc = Vec_IntSize( vMffc );
        Cand.fPrimaryFrontier = 1;
        pProved->pArray[i].Gain = Gain;
        pProved->pArray[i].nMffc = Cand.nMffc;
        Cec_TranCandVecPush( &Vertices, Cand );
        Vec_IntPush( vProvedIds, i );
        Cec_TranConflictGraphAdd( &Graph, vMffc, vSupport );
    }
    Cec_TranConflictGraphFinalize( &Graph );
    pChosen = ABC_CALLOC( char, Vertices.nSize );
    SelectedWeight = Vertices.nSize ?
        Cec_TranConflictGraphGwmin( &Graph, &Vertices,
            pChosen, &nEdges, &FirstGain ) : 0;
    if ( SelectedWeight )
        SelectedWeight = Cec_TranRepairSelectedExact( p, &Vertices,
            pChosen, SelectedWeight );

    // Apply the independent-set decision as metadata only.  No selected
    // candidate is re-evaluated on a partially modified graph in this wave.
    for ( i = 0; i < Vertices.nSize; i++ )
        if ( pChosen[i] )
        {
            Cec_TranCand_t Cand = Vertices.pArray[i];
            int Lane = Cand.nProofLane ? Cand.nProofLane - 1 :
                (Cand.nStatus == CEC_TRAN_STATE_PROVED_COMB ? 0 : 1);
            int Phase = Cand.nProofLane ? Cand.nProofPhase : Lane;
            int Kind = Cand.nProofLane ? Cand.nProofKind : Cand.nKind;
            Cand.nStatus = CEC_TRAN_STATE_SELECTED;
            Cec_TranCandVecPush( pSelected, Cand );
            iProved = Vec_IntEntry( vProvedIds, i );
            pProved->pArray[iProved].Gain = Cand.Gain;
            pProved->pArray[iProved].nStatus = CEC_TRAN_STATE_SELECTED;
            for ( k = Vec_IntEntry(Graph.vMffcBeg, i);
                  k < Vec_IntEntry(Graph.vMffcBeg, i + 1); k++ )
            {
                iObj = Vec_IntEntry( Graph.vMffcData, k );
                assert( !pCovered[iObj] );
                pCovered[iObj] = pSolved[iObj] = 1;
            }
            for ( k = Vec_IntEntry(Graph.vSuppBeg, i);
                  k < Vec_IntEntry(Graph.vSuppBeg, i + 1); k++ )
            {
                iObj = Vec_IntEntry( Graph.vSuppData, k );
                assert( !pCovered[iObj] );
                pUsed[iObj] = 1;
            }
            pProf->nStageKindSelected[Phase][Kind]++;
            pProf->nStageKindMarginalAndGain[Phase][Kind] += Cand.Gain;
            pProf->nLaneKindSelected[Lane][Kind]++;
            Cec_TranProfileBuildCandidate( pProf, &Cand, 2 );
            nSelected++;
        }
    assert( (nSelected == 0) == (SelectedWeight == 0) );
    Abc_Print( 1, "stran-root commit selection: policy=commit-wave-root-loss-gwmin initial-proved=%d initial-positive=%d initial-max-gain=%d first-gain=%d rounds=%d gain-evals=%d graph-vertices=%d graph-edges=%lld selected-weight=%lld refreshes=1.\n",
        nInitialProved, nInitialPositive, InitialMaxGain, FirstGain,
        nSelected, nGainEvals, Vertices.nSize, nEdges, SelectedWeight );
    ABC_FREE( pChosen );
    ABC_FREE( pRefs );
    Cec_TranFrozenHashStop( &FrozenHash );
    Cec_TranConflictGraphStop( &Graph );
    Cec_TranCandVecStop( &Vertices );
    Vec_IntFree( vProvedIds );
    return nSelected;
}

static int Cec_TranCommitWaveSelfTest()
{
    Cec_TranConflictGraph_t Graph;
    Cec_TranCandVec_t Vertices = {0};
    Cec_TranCand_t Cand;
    Vec_Int_t * vMffc = Vec_IntAlloc( 2 );
    Vec_Int_t * vSupport = Vec_IntAlloc( 1 );
    Vec_Int_t * vNeighbors = Vec_IntAlloc( 8 );
    char Chosen[5] = {0}, Active[5] = {1, 1, 1, 1, 1};
    int RootBest[10] = {0};
    unsigned RootSeen[10] = {0}, RootTravId = 0;
    long long nEdges = 0, Weight, Loss;
    int i, FirstGain, nActiveNeighbors;
    Cec_TranConflictGraphStart( &Graph, 10 );
    for ( i = 0; i < 5; i++ )
    {
        memset( &Cand, 0, sizeof(Cand) );
        Cand.iTarget = i == 2 ? 2 : i + 1;
        Cand.Gain = i == 0 ? 20 : i == 1 ? 15 :
            i == 2 ? 14 : i == 3 ? 8 : 7;
        Cand.nMffc = 1;
        Cec_TranCandVecPush( &Vertices, Cand );
        Vec_IntClear( vMffc );
        Vec_IntClear( vSupport );
        if ( i == 0 )
            Vec_IntPush( vMffc, 1 );
        else if ( i == 1 || i == 2 )
            Vec_IntPush( vMffc, 2 ), Vec_IntPush( vSupport, 1 );
        else if ( i == 3 )
            Vec_IntPush( vMffc, 3 ), Vec_IntPush( vSupport, 1 );
        else
            Vec_IntPush( vMffc, 4 ), Vec_IntPush( vSupport, 2 );
        Cec_TranConflictGraphAdd( &Graph, vMffc, vSupport );
    }
    Cec_TranConflictGraphFinalize( &Graph );
    Loss = Cec_TranConflictGraphRootLoss( &Graph, &Vertices, 0,
        Active, vNeighbors, RootBest, RootSeen, &RootTravId,
        &nActiveNeighbors );
    // v0 sees three conflicting candidates, but v1 and v2 belong to the same
    // root.  Its loss is therefore max(15,14)+8, not 15+14+8.
    assert( nActiveNeighbors == 3 && Loss == 23 );
    Weight = Cec_TranConflictGraphGwmin( &Graph, &Vertices,
        Chosen, &nEdges, &FirstGain );
    // Root-loss GWMIN selects v0 first.  Removing its neighborhood also
    // removes both root-2 alternatives; v4 survives, drops from loss 15 to 0,
    // and is promoted into the independent set.
    assert( nEdges == 6 && Weight == 27 && FirstGain == 20 );
    assert( Chosen[0] && !Chosen[1] && !Chosen[2] &&
        !Chosen[3] && Chosen[4] );
    Cec_TranConflictGraphStop( &Graph );
    Cec_TranCandVecStop( &Vertices );
    Vec_IntFree( vMffc );
    Vec_IntFree( vSupport );
    Vec_IntFree( vNeighbors );
    return 1;
}

// Helper experiments deliberately have no selection heuristic or size cap.
// With helper reuse enabled, every unique, still-valid retained certificate is
// materialized into the temporary proof graph.  With it disabled, none is
// seeded.  Retention and future commit eligibility are identical in both
// modes, so the switch isolates only the inductive value of H.
static void Cec_TranPrepareHelpers( Gia_Man_t * p,
    Cec_TranCandVec_t const * pRetained,
    Cec_TranCandVec_t const * pObligations, int fUseHelpers, int fVerbose,
    Cec_TranProf_t * pProf, Cec_TranCandVec_t * pActive )
{
    Cec_TranCandVec_t Unique = {0};
    Vec_Int_t * vSupport = Vec_IntAlloc( 16 );
    int nObjs = Gia_ManObjNum(p);
    char * pEndpoints = ABC_CALLOC( char, nObjs );
    char * pClasses = ABC_CALLOC( char, nObjs );
    int i, k, iObj, nEndpoints = 0, nGates = 0;
    int nClasses = 0, nEstimate;
    Cec_TranCandVecClear( pActive );
    for ( i = 0; i < pRetained->nSize; i++ )
    {
        Cec_TranCand_t Cand = pRetained->pArray[i];
        if ( !Cec_TranCandVecContains(&Unique, &Cand) )
            Cec_TranCandVecPush( &Unique, Cand );
        else
            pProf->nHelperDedup++;
    }
    if ( fUseHelpers )
        for ( i = 0; i < Unique.nSize; i++ )
            Cec_TranCandVecPush( pActive, Unique.pArray[i] );
    for ( i = 0; i < pActive->nSize; i++ )
    {
        Cec_TranCand_t Cand = pActive->pArray[i];
        if ( !pClasses[Cand.iTarget] )
            pClasses[Cand.iTarget] = 1, nClasses++;
        if ( !pEndpoints[Cand.iTarget] )
            pEndpoints[Cand.iTarget] = 1, nEndpoints++;
        Cec_TranCandCollectSupport( &Cand, vSupport );
        Vec_IntForEachEntry( vSupport, iObj, k )
            if ( !pEndpoints[iObj] )
                pEndpoints[iObj] = 1, nEndpoints++;
        nGates += Cand.nGates;
    }
    nEstimate = Gia_ManObjNum(p) + nGates +
        4 * (pActive->nSize + pObligations->nSize);
    pProf->nHelperRetained = Abc_MaxInt(
        pProf->nHelperRetained, Unique.nSize );
    pProf->nHelperInjected += pActive->nSize;
    pProf->nHelperInactive += Unique.nSize - pActive->nSize;
    pProf->nHelperClasses += nClasses;
    pProf->nHelperEndpoints = Abc_MaxInt(pProf->nHelperEndpoints, nEndpoints);
    pProf->nHelperMaterialGates += nGates;
    if ( fVerbose )
        Abc_Print( 1, "stran-root helper batch: enabled=%s retained=%d active=%d inactive=%d classes=%d endpoints=%d materialized-gates=%d obligations=%d relation-total=%d estimated-srm-nodes=%d.\n",
            fUseHelpers ? "yes" : "no", Unique.nSize, pActive->nSize,
            Unique.nSize - pActive->nSize, nClasses, nEndpoints,
            nGates, pObligations->nSize,
            pActive->nSize + pObligations->nSize, nEstimate );
    Cec_TranCandVecStop( &Unique );
    Vec_IntFree( vSupport );
    ABC_FREE( pEndpoints );
    ABC_FREE( pClasses );
}

// Deterministic structural tests for the root pipeline changes which are too
// small to justify external fixtures: rank-before-B selection, TFI-only
// Existing lookup, zero-gain filtering, H/O proof-graph separation, proof
// history remap, and the temporary/permanent AIG boundary.
static int Cec_TranPipelineSelfTest()
{
    Cec_ParTran_t Pars;
    Cec_TranRoot_t Root;
    Cec_TranDiscStat_t Disc = {0};
    Cec_TranProf_t Prof = {0};
    Cec_TranCandVec_t Known = {0}, Direct = {0}, Cands = {0};
    Cec_TranCandVec_t Seq = {0}, Carry = {0}, History = {0}, Active = {0};
    Cec_TranCand_t DirectCand, ZeroGain;
    Cec_TranDivRank_t Ranks[3] = {{30, 0, 2}, {20, 0, 0}, {10, 0, 1}};
    Cec_TranDivRank_t PinnedRanks[3] = {
        {30, 0, 2}, {20, 0, 0}, {10, 0, 1}};
    Gia_Man_t * p = Gia_ManStart( 16 ), * pBatch;
    Cec_TranPatDb_t * pDb;
    Cec_TranSim_t * pSim;
    Vec_Int_t * vPool = Vec_IntAlloc( 3 );
    Vec_Int_t * vPinned = Vec_IntAlloc( 1 );
    Vec_Int_t * vMffc = Vec_IntAlloc( 8 );
    Vec_Int_t * vSupport = Vec_IntAlloc( 8 );
    Vec_Int_t * vPairs, * vCombPairs, * vQueries, * vMap;
    char * pMffc, * pCovered, * pUsed;
    int i, iX, iY, iN1, iN2, nObjBefore, fFound = 0;
    Vec_IntPush( vPool, 11 );
    Vec_IntPush( vPool, 22 );
    Vec_IntPush( vPool, 33 );
    Cec_TranSelectRankedDivPool( vPool, Ranks, 2, NULL );
    assert( Vec_IntSize(vPool) == 2 &&
        Vec_IntEntry(vPool, 0) == 33 && Vec_IntEntry(vPool, 1) == 11 );
    Vec_IntClear( vPool );
    Vec_IntPush( vPool, 11 );
    Vec_IntPush( vPool, 22 );
    Vec_IntPush( vPool, 33 );
    Vec_IntPush( vPinned, 22 );
    assert( Cec_TranSelectRankedDivPool(vPool, PinnedRanks, 2,
        vPinned) == 1 );
    assert( Vec_IntSize(vPool) == 2 &&
        Vec_IntEntry(vPool, 0) == 33 && Vec_IntEntry(vPool, 1) == 22 &&
        PinnedRanks[0].iPos == 0 && PinnedRanks[1].iPos == 1 );
    // A continuation page may recompute a different ordinary top-B prefix,
    // but it must bind the exact page-zero pool and aligned metadata before
    // resuming either the iterator or the root-batch teaching cache.
    {
        Cec_TranRootCursor_t Cursor = {0};
        Cec_TranDivRank_t PageRanks[2] = {{30, 0, 0}, {20, 0, 1}};
        Vec_Int_t * vPage = Vec_IntAlloc( 2 );
        Cec_TranRootCursorBindBuildPool( &Cursor, 0, vPool, PinnedRanks );
        Vec_IntPush( vPage, 33 );
        Vec_IntPush( vPage, 11 );
        Cec_TranRootCursorBindBuildPool( &Cursor, 1, vPage, PageRanks );
        assert( Vec_IntSize(vPage) == 2 &&
            Vec_IntEntry(vPage, 0) == 33 && Vec_IntEntry(vPage, 1) == 22 &&
            PageRanks[0].iPos == 0 && PageRanks[1].iPos == 1 );
        Cec_TranRootCursorStop( &Cursor );
        Vec_IntFree( vPage );
    }
    Vec_IntClear( vPool );

    iX = Gia_ManAppendCi( p );
    iY = Gia_ManAppendCi( p );
    iN1 = Gia_ManAppendAnd( p, iX, iY );
    iN2 = Gia_ManAppendAnd( p, iX, iY );
    Gia_ManAppendCo( p, iN2 );
    Gia_ManAppendCo( p, iN2 );
    Gia_ManSetRegNum( p, 1 );
    Gia_ManCreateRefs( p );
    Cec_ManTranSetDefaultParams( &Pars );
    Pars.nSimWords = 1;
    Pars.nSimFrames = 2;
    pDb = Cec_TranPatDbStart( p, 0 );
    pSim = Cec_TranSimStart( p, &Pars, pDb );
    Root.iObj = Abc_Lit2Var(iN2);
    Root.nMffc = Gia_NodeMffcSize( p, Gia_ManObj(p, Root.iObj) );
    Vec_IntPush( vPool, Abc_Lit2Var(iN1) );
    Cec_TranCollectRootDirectTfi( p, pSim, &Pars, &Root, vPool,
        NULL, 1,
        &Known, &Direct, &Disc, &Prof );
    for ( i = 0; i < Direct.nSize; i++ )
        fFound |= Direct.pArray[i].nKind == CEC_TRAN_CAND_EXIST &&
            Direct.pArray[i].iOut == iN1;
    assert( fFound );
    Cec_TranCandVecClear( &Direct );
    Vec_IntClear( vPool );
    Cec_TranCollectRootDirectTfi( p, pSim, &Pars, &Root, vPool,
        NULL, 1,
        &Known, &Direct, &Disc, &Prof );
    for ( i = 0; i < Direct.nSize; i++ )
        assert( Direct.pArray[i].nKind != CEC_TRAN_CAND_EXIST );

    pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
    pCovered = ABC_CALLOC( char, Gia_ManObjNum(p) );
    pUsed = ABC_CALLOC( char, Gia_ManObjNum(p) );
    memset( &ZeroGain, 0, sizeof(ZeroGain) );
    ZeroGain.iTarget = Root.iObj;
    ZeroGain.iDiv0 = iX;
    ZeroGain.iDiv1 = iY;
    ZeroGain.nMffc = Root.nMffc;
    ZeroGain.Gain = 0;
    ZeroGain.nGates = 1;
    ZeroGain.Recipe = Cec_TranRecipeAlloc( 2 );
    ZeroGain.Recipe[0] = iX;
    ZeroGain.Recipe[1] = iY;
    ZeroGain.iOut = Cec_TranRecipeGateCode( 0, 0 );
    ZeroGain.nKind = CEC_TRAN_CAND_CONSTR;
    ZeroGain.nStatus = CEC_TRAN_STATE_CANDIDATE;
    Cec_TranCandVecPush( &Cands, ZeroGain );
    Cec_TranRootPrepareSeqFrontier( p, &Root, 1, &Cands,
        pCovered, pUsed, pMffc, vMffc, vSupport, 1, &Seq, &Prof );
    // The raw-one-gate candidate hashes to existing N1.  It is an alias,
    // not a genuinely fresh Build, but its frozen physical cost is zero.
    assert( Seq.nSize == (Cec_TranQualityActualCost() ? 1 : 0) );
    if ( Cec_TranQualityActualCost() )
    {
        assert( Seq.pArray[0].Gain == 1 && Seq.pArray[0].nGates == 1 );
        assert( Seq.pArray[0].iTarget == Root.iObj );
        assert( Cec_TranQualityCostGainOne(p, &ZeroGain, pCovered, pUsed, NULL) == 1 );
    }

    // Interleaved targets and a tried candidate exercise target indexing.
    // Reusing initialized potentials must produce the same sorted frontier
    // as a full dynamic refresh, while retaining zero-gain rejection above.
    {
        Cec_TranRoot_t Roots[2] = { Root, { Abc_Lit2Var(iN1), 1 } };
        Cec_TranCandVec_t Indexed = {0}, Refreshed = {0}, Mixed = {0};
        Cec_TranCand_t Cand = Cec_TranCandCreateLiteral(
            Abc_Lit2Var(iN1), 0, 1, CEC_TRAN_CAND_CONST, 1 );
        Cand.nStatus = CEC_TRAN_STATE_CANDIDATE;
        Cec_TranCandVecPush( &Mixed, Cand );
        Cand.iTarget = Root.iObj;
        Cand.nStatus = CEC_TRAN_STATE_TRIED_SEQ;
        Cec_TranCandVecPush( &Mixed, Cand );
        Cand.nStatus = CEC_TRAN_STATE_CANDIDATE;
        Cec_TranCandVecPush( &Mixed, Cand );
        Cec_TranCandVecPush( &Mixed, ZeroGain );
        Cec_TranRootPrepareSeqFrontier( p, Roots, 2, &Mixed,
            pCovered, pUsed, pMffc, vMffc, vSupport, 0, &Indexed, &Prof );
        Cec_TranRootPrepareSeqFrontier( p, Roots, 2, &Mixed,
            pCovered, pUsed, pMffc, vMffc, vSupport, 1, &Refreshed, &Prof );
        assert( Indexed.nSize == (Cec_TranQualityActualCost() ? 3 : 2) );
        assert( Refreshed.nSize == Indexed.nSize );
        assert( Indexed.pArray[0].iTarget == Root.iObj &&
            Indexed.pArray[Indexed.nSize-1].iTarget == Abc_Lit2Var(iN1) );
        assert( !memcmp(Indexed.pArray, Refreshed.pArray,
            Indexed.nSize * sizeof(Cec_TranCand_t)) );
        Cec_TranCandVecStop( &Indexed );
        Cec_TranCandVecStop( &Refreshed );
        Cec_TranCandVecStop( &Mixed );
    }

    DirectCand = Cec_TranCandCreateLiteral( Root.iObj, iN1,
        Root.nMffc, CEC_TRAN_CAND_EXIST, 1 );
    DirectCand.nProofStage = 2;
    DirectCand.nProofLane = 2;
    DirectCand.nProofPhase = 1;
    DirectCand.nProofKind = CEC_TRAN_CAND_EXIST;
    DirectCand.nStatus = CEC_TRAN_STATE_PROVED_SEQ;
    Cec_TranCandVecPush( &Carry, DirectCand );
    vMap = Vec_IntStartFull( Gia_ManObjNum(p) );
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        Vec_IntWriteEntry( vMap, i, Abc_Var2Lit(i, 0) );
    Cec_TranRemapProofHistory( p, vMap, &Carry, &History, &Prof );
    assert( History.nSize == 1 &&
        History.pArray[0].nStatus == CEC_TRAN_STATE_PROVED_SEQ &&
        History.pArray[0].nProofLane == 2 &&
        History.pArray[0].nProofPhase == 1 &&
        History.pArray[0].nProofKind == CEC_TRAN_CAND_EXIST );
    Cec_TranPrepareHelpers( p, &History, &Cands, 1, 0, &Prof, &Active );
    assert( Active.nSize == History.nSize );
    Cec_TranPrepareHelpers( p, &History, &Cands, 0, 0, &Prof, &Active );
    assert( Active.nSize == 0 );

    nObjBefore = Gia_ManObjNum(p);
    pBatch = Cec_TranBuildRootBatch( p, History.pArray, 1,
        Cands.pArray, 1, 1, &vPairs, &vCombPairs, &vQueries,
        NULL, NULL );
    assert( Vec_IntSize(vPairs) == 4 &&
        Vec_IntSize(vCombPairs) == 2 && Vec_IntSize(vQueries) == 1 );
    assert( Gia_ManObjNum(p) == nObjBefore );
    Gia_ManStop( pBatch );
    Vec_IntFree( vPairs );
    Vec_IntFree( vCombPairs );
    Vec_IntFree( vQueries );
    Vec_IntFree( vMap );
    Cec_TranSimStop( pSim );
    Cec_TranPatDbStop( pDb );
    Cec_TranCandRecipeRelease( &ZeroGain );
    Cec_TranCandVecStop( &Known );
    Cec_TranCandVecStop( &Direct );
    Cec_TranCandVecStop( &Cands );
    Cec_TranCandVecStop( &Seq );
    Cec_TranCandVecStop( &Carry );
    Cec_TranCandVecStop( &History );
    Cec_TranCandVecStop( &Active );
    Vec_IntFree( vPool );
    Vec_IntFree( vMffc );
    Vec_IntFree( vSupport );
    Vec_IntFree( vPinned );
    ABC_FREE( pMffc );
    ABC_FREE( pCovered );
    ABC_FREE( pUsed );
    Gia_ManStop( p );
    return 1;
}

// Prove the complete selected frontier on one immutable snapshot.  COMB-only
// closure stops after CBS; the SEQ phase sends every CBS-unproved submitted
// relation to one shared correspondence fixed point.
static int Cec_TranRootProvePortfolio( Gia_Man_t * p,
    Cec_TranCandVec_t const * pHelpers, Cec_TranCandVec_t * pPortfolio,
    Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, Cec_TranCandVec_t * pProved, int fCombOnly,
    int iPhase )
{
    Vec_Int_t * vStatus;
    Vec_Str_t * vStage;
    Cec_TranCand_t Cand;
    int i, iStage, nNew = 0;
    if ( pPortfolio->nSize == 0 )
        return 0;
    qsort( pPortfolio->pArray, pPortfolio->nSize, sizeof(Cec_TranCand_t),
        Cec_TranCandRootHeuristicCompare );
    for ( i = 0; i < pPortfolio->nSize; i++ )
    {
        pProf->nStageKindSubmitted[iPhase][pPortfolio->pArray[i].nKind]++;
        pProf->nLaneKindSubmitted[0][pPortfolio->pArray[i].nKind]++;
        if ( pPortfolio->pArray[i].nKind == CEC_TRAN_CAND_CONSTR )
            Cec_TranSuppProfRecordCand( pProf->pBuildSuppProf,
                pPortfolio->pArray + i, CEC_TRAN_SUPP_SUBMITTED );
        if ( pPortfolio->pArray[i].fKitPortfolio )
            pProf->nRootKitSubmitted++;
        if ( pPortfolio->pArray[i].fBdcPortfolio )
            pProf->nRootBdcSubmitted++;
    }
    vStatus = Cec_TranProveRootBatch( p,
        pHelpers ? pHelpers->pArray : NULL,
        pHelpers ? pHelpers->nSize : 0,
        pPortfolio->pArray, pPortfolio->nSize,
        pPars, pProf, fCombOnly, &vStage );
    for ( i = 0; i < pPortfolio->nSize; i++ )
    {
        iStage = Vec_StrEntry( vStage, i );
        // A COMB-only closure pass stops before correspondence.  Candidates
        // rejected by CBS are therefore not SEQ submissions in this pass.
        if ( !fCombOnly && iStage != 1 )
            pProf->nLaneKindSubmitted[1][pPortfolio->pArray[i].nKind]++;
        if ( !Vec_IntEntry(vStatus, i) )
            continue;
        assert( iStage == 1 || iStage == 2 );
        Cand = pPortfolio->pArray[i];
        Cand.nProofStage = iStage;
        Cand.nProofLane = iStage;
        Cand.nProofPhase = iPhase;
        Cand.nProofKind = Cand.nKind;
        Cand.nStatus = iStage == 1 ?
            CEC_TRAN_STATE_PROVED_COMB : CEC_TRAN_STATE_PROVED_SEQ;
        pProf->nStageKindProved[iPhase][Cand.nKind]++;
        pProf->nLaneKindProved[iStage - 1][Cand.nKind]++;
        Cec_TranProfileBuildCandidate( pProf, &Cand, 1 );
        if ( Cec_TranCandVecContains(pProved, &Cand) )
            continue;
        Cec_TranCandVecPush( pProved, Cand );
        nNew++;
    }
    Vec_IntFree( vStatus );
    Vec_StrFree( vStage );
    return nNew;
}

static Gia_Man_t * Cec_TranCommitSelectedRootOnly( Gia_Man_t * p,
    Cec_TranCandVec_t * pSelected, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, Cec_TranCandVec_t const * pCarry,
    Cec_TranCandVec_t * pHistory )
{
    Gia_Man_t * pDup, * pClean;
    Gia_Obj_t * pObj;
    Vec_Int_t * vSelected, * vDupToClean, * vOldToClean;
    long long Marginal = 0;
    int i, iLit, iMapped, Gain, fProved = 1;
    abctime clk;
    if ( pSelected->nSize == 0 )
    {
        Cec_TranCandVecClear( pHistory );
        for ( i = 0; i < pCarry->nSize; i++ )
            Cec_TranCandVecPush( pHistory, pCarry->pArray[i] );
        return p;
    }
    vSelected = Vec_IntAlloc( pSelected->nSize );
    for ( i = 0; i < pSelected->nSize; i++ )
        Vec_IntPush( vSelected, i ), Marginal += pSelected->pArray[i].Gain;
    clk = Abc_Clock();
    pDup = Cec_TranDupRootBundle( p, pSelected->pArray, vSelected );
    pProf->timeRootBundleDup += Abc_Clock() - clk;
    clk = Abc_Clock();
    pClean = Cec_TranCleanupKeepRegs( pDup, &vDupToClean );
    pProf->timeRootCleanup += Abc_Clock() - clk;
    vOldToClean = Vec_IntStartFull( Gia_ManObjNum(p) );
    Gia_ManForEachObj( p, pObj, i )
    {
        iLit = Cec_TranMapLitByValue( p, Abc_Var2Lit(i, 0) );
        if ( iLit < 0 || Abc_Lit2Var(iLit) >= Vec_IntSize(vDupToClean) )
            continue;
        iMapped = Vec_IntEntry( vDupToClean, Abc_Lit2Var(iLit) );
        if ( iMapped >= 0 )
            Vec_IntWriteEntry( vOldToClean, i,
                Abc_LitNotCond(iMapped, Abc_LitIsCompl(iLit)) );
    }
    Cec_TranRemapProofHistory( pClean, vOldToClean, pCarry,
        pHistory, pProf );
    clk = Abc_Clock();
    Gain = Cec_TranGain( p, pClean );
    pProf->timeRootExactAudit += Abc_Clock() - clk;
    assert( Gain > 0 && Gain >= Marginal );
    assert( Gia_ManRegNum(p) == Gia_ManRegNum(pClean) );
    if ( pPars->fShadow )
    {
        clk = Abc_Clock();
        fProved = Cec_TranProveWhole( p, pDup, pPars, pProf );
        pProf->timeShadow += Abc_Clock() - clk;
    }
    assert( fProved );
    pProf->nRootBundleAndGain = Gain;
    pProf->nRootBundleRegGain = Gia_ManRegNum(p) - Gia_ManRegNum(pClean);
    pProf->nRootBundleCommits = pSelected->nSize;
    Gia_ManStop( p );
    Gia_ManStop( pDup );
    Vec_IntFree( vSelected );
    Vec_IntFree( vDupToClean );
    Vec_IntFree( vOldToClean );
    return pClean;
}
