// Exact gain, MFFC, and support profiling.
// Private implementation fragment included only by cecTrans.c.

// Among candidates that already passed signature/care matching and structural
// legality, root-only order is deterministic: constants first, then existing
// literals, then constructed recipes by increasing gate count.  Kind priority
// never admits an unmatched relation.  Gain/coverage and the canonical recipe
// key break ties without changing that kind order.
static int Cec_TranCandHeuristicCompare( const void * p0, const void * p1 )
{
    Cec_TranCand_t const * pC0 = (Cec_TranCand_t const *)p0;
    Cec_TranCand_t const * pC1 = (Cec_TranCand_t const *)p1;
    if ( pC0->nKind != pC1->nKind )
        return pC0->nKind - pC1->nKind;
    if ( pC0->nGates != pC1->nGates )
        return pC0->nGates - pC1->nGates;
    if ( pC0->fExactTemplate != pC1->fExactTemplate )
        return pC1->fExactTemplate - pC0->fExactTemplate;
    // The resub engine yields exact covers in decreasing sampled coverage /
    // residual-reduction order.  CI overlap is the next safe tie-break; it is
    // never used as a semantic filter.
    if ( pC0->nResubRank != pC1->nResubRank )
        return pC0->nResubRank - pC1->nResubRank;
    if ( pC0->nCiOverlap != pC1->nCiOverlap )
        return pC1->nCiOverlap - pC0->nCiOverlap;
    if ( pC0->fDivRescue != pC1->fDivRescue )
        return pC0->fDivRescue - pC1->fDivRescue;
    if ( pC0->Gain != pC1->Gain )
        return pC1->Gain - pC0->Gain;
    if ( pC0->iOut != pC1->iOut )
        return pC0->iOut - pC1->iOut;
    return pC0->nGates ? memcmp( pC0->Recipe, pC1->Recipe,
        sizeof(int) * 2 * pC0->nGates ) : 0;
}

// Group candidates by MFFC-ranked target and sort each root's alternatives by
// local gain.  Every layer is proved even after another alternative succeeds;
// the exact-cost portfolio at commit time then compares this order's winner
// with the q=1-primary winner and prevents a globally worse replacement.
// qStrictAll is grouped by target and gain-sorted within each group.  Store
// each [begin,end) range and the maximum direct/normal/rescue widths.  Layer
// lookup scans the small per-root range, exposing the cheap direct lane first,
// then legacy constructed candidates, then diverse-rescue candidates.  The
// metadata remains O(number of roots).
static int Cec_TranCandVecEvalSortTail( Gia_Man_t * p,
    Cec_TranCandVec_t * pVec, int iStart, Cec_TranProf_t * pProf )
{
    int i, nEvals = 0;
    for ( i = iStart; i < pVec->nSize; i++ )
        if ( pVec->pArray[i].Gain < 0 )
        {
            pVec->pArray[i].Gain = Cec_TranRootCandidateGainEval(
                p, pVec->pArray + i, pProf );
            nEvals++;
        }
    if ( pVec->nSize - iStart > 1 )
        qsort( pVec->pArray + iStart, pVec->nSize - iStart,
            sizeof(Cec_TranCand_t), Cec_TranCandGainCompare );
    return nEvals;
}

// Apply one proved replacement per target in one topological duplication.
// Replacements only use earlier literals, so if an earlier selected target is
// itself rewritten, every later recipe automatically sees its equivalent new
// representative.  This is the root-scope analogue of reducing all proved
// signal-correspondence classes at once.
static Gia_Man_t * Cec_TranDupRootBundle( Gia_Man_t * p,
    Cec_TranCand_t const * pCands, Vec_Int_t * vSelected )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int * pSelect = ABC_FALLOC( int, Gia_ManObjNum(p) );
    int i, k, iCand, iLit0, iLit1, iRep;
    Vec_IntForEachEntry( vSelected, iCand, k )
        pSelect[pCands[iCand].iTarget] = iCand;
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + 4 * Vec_IntSize(vSelected) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    pNew->nConstrs = p->nConstrs;
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Gia_ObjFanin0Copy( pObj );
        iLit1 = Gia_ObjFanin1Copy( pObj );
        iCand = pSelect[i];
        if ( iCand < 0 )
        {
            pObj->Value = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
            continue;
        }
        iRep = Cec_TranRecipeBuild( p, pNew, pCands + iCand );
        pObj->Value = iRep;
    }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    pNew->nConstrs = p->nConstrs;
    Cec_TranAssertTypedInterface( p, pNew );
    ABC_FREE( pSelect );
    return pNew;
}

// Exact attribution on the selected set, never on a reselected portfolio.
// First apply every Direct edit and every CBS-origin Build; temporal Build
// is last.  Thus its signed marginal includes cleanup/interactions with those
// retained edits. Original CBS origin stays excluded even if remapping has
// downgraded the reusable certificate strength to sequential. ODC supplies
// its actual all-exit proof lane, not its structural selection status.
static void Cec_TranTemporalBuildProfile( Gia_Man_t * p,
    Cec_TranCandVec_t const * pSelected, Gia_Man_t * pFinal,
    char const * Scope )
{
    Vec_Int_t * vDirect = Vec_IntAlloc( pSelected->nSize );
    Gia_Man_t * pDup, * pClean;
    int i, nWithoutBuild, nBuild = 0;
    for ( i = 0; i < pSelected->nSize; i++ )
        if ( pSelected->pArray[i].nProofKind == CEC_TRAN_CAND_CONSTR )
            nBuild++;
        else
            Vec_IntPush( vDirect, i );
    if ( nBuild )
    {
        pDup = Cec_TranDupRootBundle( p, pSelected->pArray, vDirect );
        pClean = Cec_TranCleanupKeepRegs( pDup, NULL );
        nWithoutBuild = Gia_ManAndNum( pClean );
        Gia_ManStop( pClean );
        Gia_ManStop( pDup );
    }
    else
        nWithoutBuild = Gia_ManAndNum( pFinal );
    Abc_Print( 1, "sresub build reduction: scope=%s selected=%d and-before=%d and-without-build=%d and-after=%d ordered-and-gain=%d\n",
        Scope, nBuild, Gia_ManAndNum(p), nWithoutBuild,
        Gia_ManAndNum(pFinal), nWithoutBuild - Gia_ManAndNum(pFinal) );
    Vec_IntFree( vDirect );
}

// The exact q=1 frontier is a conservative portfolio member.  It includes
// ordinary non-resub candidates and candidates explicitly generated by the
// legacy/direct/boundary q=1 path, but never admits a root which exists only
// because q>1 explored additional choices.  Comparing its cleanup cost with
// the full gain portfolio gives large q a strict q=1 bundle fallback.
// Exact dry-run size for one proof-stage subset, using the same winner
// selection and cleanup as the unified commit.  In particular, evaluate both
// the local-gain portfolio and the q=1-primary fallback, because the real
// commit may choose either one after exact cleanup.
// Counterfactual size profiles use the same per-target winner selection and
// cleanup as the real commit.  With only three candidate kinds, the six
// proper nonempty subsets are enough to recover exact Shapley contributions;
// the empty size is the input and the full size is the actual committed
// result.  Additional subsets expose the marginal utility of raw resub ranks
// above one, CEGAR waves after wave one, and the two sources currently folded
// into the existing kind (global lookup versus zero-gate resub recipes).
// Split the exact cleanup gain by both proof stage and candidate kind.  The
// combinational characteristic function starts from the input network.  The
// sequential characteristic function starts from the full combinational
// bundle, so its Shapley values add up to the incremental temporal reduction
// instead of double-counting reductions already certified combinationally.
// Select the best proved recipe for each target, then commit all selected
// targets together.  Different proved alternatives of one target form one
// equivalence class, so only the highest exact-gain representative is needed.
static int Cec_TranRootCompare( const void * p0, const void * p1 )
{
    Cec_TranRoot_t const * pR0 = (Cec_TranRoot_t const *)p0;
    Cec_TranRoot_t const * pR1 = (Cec_TranRoot_t const *)p1;
    if ( pR0->nMffc != pR1->nMffc )
        return pR1->nMffc - pR0->nMffc;
    return pR1->iObj - pR0->iObj;
}

static void Cec_TranMffcScratchClear( char * pMark, Vec_Int_t * vMarked )
{
    int i, iObj;
    Vec_IntForEachEntry( vMarked, iObj, i )
        pMark[iObj] = 0;
    Vec_IntClear( vMarked );
}

static inline int Cec_TranMffcIsBoundary( int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary )
{
    return iObj != iRoot &&
        ((pCovered && pCovered[iObj]) || (pUsed && pUsed[iObj]) ||
         (vBoundary && Vec_IntFind((Vec_Int_t *)vBoundary, iObj) >= 0));
}

// Dereference and restore one root using scratch reference counts.  Testing a
// fanin's original ref count in isolation is incorrect for reconvergent MFFCs:
// removing an earlier parent can make a later shared fanin reach zero.  The
// paired traversals below reproduce Gia_NodeDeref_rec/Gia_NodeRef_rec while
// honoring virtual-selection and candidate-support cutpoints.
static int Cec_TranMffcDeref_rec( Gia_Man_t * p, int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, int * pRefs,
    char * pMark, Vec_Int_t * vMarked )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    int iFan, Count = 1;
    assert( Gia_ObjIsAnd(pObj) );
    assert( !pMark[iObj] );
    pMark[iObj] = 1;
    Vec_IntPush( vMarked, iObj );
    iFan = Gia_ObjFaninId0p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) )
    {
        assert( pRefs[iFan] > 0 );
        if ( --pRefs[iFan] == 0 )
            Count += Cec_TranMffcDeref_rec( p, iFan, iRoot, pCovered,
                pUsed, vBoundary, pRefs, pMark, vMarked );
    }
    iFan = Gia_ObjFaninId1p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) )
    {
        assert( pRefs[iFan] > 0 );
        if ( --pRefs[iFan] == 0 )
            Count += Cec_TranMffcDeref_rec( p, iFan, iRoot, pCovered,
                pUsed, vBoundary, pRefs, pMark, vMarked );
    }
    return Count;
}

static int Cec_TranMffcRef_rec( Gia_Man_t * p, int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, int * pRefs )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    int iFan, Count = 1;
    assert( Gia_ObjIsAnd(pObj) );
    iFan = Gia_ObjFaninId0p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) &&
         pRefs[iFan]++ == 0 )
        Count += Cec_TranMffcRef_rec( p, iFan, iRoot, pCovered, pUsed,
            vBoundary, pRefs );
    iFan = Gia_ObjFaninId1p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         !Cec_TranMffcIsBoundary(iFan, iRoot, pCovered, pUsed, vBoundary) &&
         pRefs[iFan]++ == 0 )
        Count += Cec_TranMffcRef_rec( p, iFan, iRoot, pCovered, pUsed,
            vBoundary, pRefs );
    return Count;
}

static void Cec_TranMarkDynamicMffcWithRefs( Gia_Man_t * p, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, int * pRefs,
    char * pMark, Vec_Int_t * vMarked )
{
    int nDeref, nRef;
    assert( pRefs != NULL );
    assert( Gia_ObjIsAnd(Gia_ManObj(p, iRoot)) );
    Cec_TranMffcScratchClear( pMark, vMarked );
    nDeref = Cec_TranMffcDeref_rec( p, iRoot, iRoot, pCovered, pUsed,
        vBoundary, pRefs, pMark, vMarked );
    nRef = Cec_TranMffcRef_rec( p, iRoot, iRoot, pCovered, pUsed,
        vBoundary, pRefs );
    assert( nDeref == nRef && nDeref == Vec_IntSize(vMarked) );
}

// Private reference snapshot.  Callers may reuse it while the graph and
// covered set are unchanged: each paired MFFC traversal restores its refs.
static int * Cec_TranMffcRefsStart( Gia_Man_t * p, char const * pCovered )
{
    Gia_Obj_t * pObj;
    int * pRefs;
    int i, iFan;
    assert( p->pRefs != NULL );
    pRefs = ABC_ALLOC( int, Gia_ManObjNum(p) );
    memcpy( pRefs, p->pRefs, sizeof(int) * Gia_ManObjNum(p) );
    // Covered objects have already been removed by earlier virtual choices.
    // Remove their structural fanin references from this scratch snapshot so
    // later roots see the true marginal MFFC.
    if ( pCovered )
    {
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
    }
    return pRefs;
}

static void Cec_TranMarkDynamicMffc( Gia_Man_t * p, int iRoot,
    char const * pCovered, char const * pUsed,
    Vec_Int_t const * vBoundary, char * pMark, Vec_Int_t * vMarked )
{
    int * pRefs = Cec_TranMffcRefsStart( p, pCovered );
    Cec_TranMarkDynamicMffcWithRefs( p, iRoot, pCovered, pUsed,
        vBoundary, pRefs, pMark, vMarked );
    ABC_FREE( pRefs );
}

static void Cec_TranCandCollectSupport( Cec_TranCand_t const * pCand,
    Vec_Int_t * vSupport )
{
    int i, Code, iObj;
    Vec_IntClear( vSupport );
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) )
            continue;
        iObj = Abc_Lit2Var( Code );
        if ( iObj && Vec_IntFind(vSupport, iObj) < 0 )
            Vec_IntPush( vSupport, iObj );
    }
}

// Profiling-only support interning.  A support is the exact sorted set of
// original GIA divisors used by one canonical Build recipe, paired with its
// target.  Dense entries keep the per-support counters compact; the separate
// open-addressed table contains only entry indices.  Full key comparison
// against vKeys makes the unique-support counts exact rather than hash-based.
typedef struct Cec_TranSuppProfEnt_t_ Cec_TranSuppProfEnt_t;
struct Cec_TranSuppProfEnt_t_
{
    word          Hash;
    int           iTarget;
    int           iOffset;
    int           nSupport;
    int           nValid;
    int           nAccepted;
    int           nSubmitted;
    int           nRefuted;
    int           nRefutedBmcBatch;
    int           nRefutedIndBatch;
    int           nRefutedNoSatBatch;
    int           nUnknown;
    int           nProved;
    int           nSelected;
    int           nAcceptedGateSum;
    unsigned char nMinGatesAccepted;
    unsigned char nMinGatesProved;
    unsigned char nMinGatesSelected;
    unsigned char StageValid;
    unsigned char StageAccepted;
    unsigned char StageSubmitted;
    unsigned char StageRefuted;
    unsigned char StageUnknown;
    unsigned char StageProved;
    unsigned char StageSelected;
    unsigned char fResidualGreedy;
};

struct Cec_TranSuppProf_t_
{
    Cec_TranSuppProfEnt_t * pEntries;
    int *                   pBins;
    int                     nEntries;
    int                     nEntriesCap;
    int                     nBins;
    int                     nObjs;
    Vec_Int_t *             vKeys;
    Vec_Int_t *             vScratch;
    int *                   pRootValidCands;
    int *                   pRootValidSupps;
    int *                   pRootAcceptedCands;
    int *                   pRootAcceptedSupps;
    int *                   pRootResidualOffset;
    int *                   pRootResidualSize;
    Vec_Int_t *             vResidualKeys;
    long long               nResidualEligibleRoots;
    long long               nResidualSampledRoots;
    long long               nResidualNoPairRoots;
    long long               nResidualPairs;
    long long               nResidualStaticCovered[CEC_TRAN_BUILD_RESIDUAL_DEPTH_BINS];
    long long               nResidualGreedyCovered[CEC_TRAN_BUILD_RESIDUAL_DEPTH_BINS];
    long long               nResidualStaticComplete;
    long long               nResidualGreedyComplete;
    long long               nResidualStaticSizeSum;
    long long               nResidualGreedySizeSum;
    long long               nResidualStaticSize[CEC_TRAN_BUILD_RESIDUAL_SIZE_BINS];
    long long               nResidualGreedySize[CEC_TRAN_BUILD_RESIDUAL_SIZE_BINS];
};

static word Cec_TranSuppProfHash( int iTarget, Vec_Int_t * vSupport )
{
    word Hash = ABC_CONST(0xcbf29ce484222325);
    int i, iObj;
    Hash = (Hash ^ (word)(unsigned)iTarget) * ABC_CONST(0x100000001b3);
    Vec_IntForEachEntry( vSupport, iObj, i )
        Hash = (Hash ^ (word)(unsigned)iObj) * ABC_CONST(0x100000001b3);
    Hash = (Hash ^ (word)(unsigned)Vec_IntSize(vSupport)) *
        ABC_CONST(0x100000001b3);
    return Hash ? Hash : 1;
}

static int Cec_TranSuppProfFindSlot( Cec_TranSuppProf_t const * p,
    word Hash, int iTarget, Vec_Int_t * vSupport, int * pfFound )
{
    int iEntry, iSlot = (int)(Hash & (word)(p->nBins - 1));
    Cec_TranSuppProfEnt_t const * pEntry;
    while ( p->pBins[iSlot] )
    {
        iEntry = p->pBins[iSlot] - 1;
        pEntry = p->pEntries + iEntry;
        if ( pEntry->Hash == Hash && pEntry->iTarget == iTarget &&
             pEntry->nSupport == Vec_IntSize(vSupport) &&
             !memcmp(Vec_IntArray(p->vKeys) + pEntry->iOffset,
                 Vec_IntArray(vSupport),
                 sizeof(int) * (size_t)pEntry->nSupport) )
        {
            *pfFound = 1;
            return iSlot;
        }
        iSlot = (iSlot + 1) & (p->nBins - 1);
    }
    *pfFound = 0;
    return iSlot;
}

static void Cec_TranSuppProfRehash( Cec_TranSuppProf_t * p )
{
    int i, iSlot, nBinsNew = 2 * p->nBins;
    int * pBinsNew = ABC_CALLOC( int, nBinsNew );
    for ( i = 0; i < p->nEntries; i++ )
    {
        iSlot = (int)(p->pEntries[i].Hash & (word)(nBinsNew - 1));
        while ( pBinsNew[iSlot] )
            iSlot = (iSlot + 1) & (nBinsNew - 1);
        pBinsNew[iSlot] = i + 1;
    }
    ABC_FREE( p->pBins );
    p->pBins = pBinsNew;
    p->nBins = nBinsNew;
}

static Cec_TranSuppProf_t * Cec_TranSuppProfStart( int nObjs )
{
    Cec_TranSuppProf_t * p = ABC_CALLOC( Cec_TranSuppProf_t, 1 );
    p->nEntriesCap = 512;
    p->nBins = 1024;
    p->nObjs = nObjs;
    p->pEntries = ABC_ALLOC( Cec_TranSuppProfEnt_t, p->nEntriesCap );
    p->pBins = ABC_CALLOC( int, p->nBins );
    p->vKeys = Vec_IntAlloc( 1024 );
    p->vScratch = Vec_IntAlloc( 16 );
    p->pRootValidCands = ABC_CALLOC( int, nObjs );
    p->pRootValidSupps = ABC_CALLOC( int, nObjs );
    p->pRootAcceptedCands = ABC_CALLOC( int, nObjs );
    p->pRootAcceptedSupps = ABC_CALLOC( int, nObjs );
    p->pRootResidualOffset = ABC_ALLOC( int, nObjs );
    p->pRootResidualSize = ABC_CALLOC( int, nObjs );
    p->vResidualKeys = Vec_IntAlloc( 256 );
    {
        int i;
        for ( i = 0; i < nObjs; i++ )
            p->pRootResidualOffset[i] = -3;
    }
    return p;
}

static void Cec_TranSuppProfStop( Cec_TranSuppProf_t * p )
{
    if ( p == NULL )
        return;
    ABC_FREE( p->pEntries );
    ABC_FREE( p->pBins );
    Vec_IntFree( p->vKeys );
    Vec_IntFree( p->vScratch );
    ABC_FREE( p->pRootValidCands );
    ABC_FREE( p->pRootValidSupps );
    ABC_FREE( p->pRootAcceptedCands );
    ABC_FREE( p->pRootAcceptedSupps );
    ABC_FREE( p->pRootResidualOffset );
    ABC_FREE( p->pRootResidualSize );
    Vec_IntFree( p->vResidualKeys );
    ABC_FREE( p );
}

static int Cec_TranSuppProfIsResidualGreedy( Cec_TranSuppProf_t const * p,
    int iTarget, Vec_Int_t * vSupport )
{
    int iOffset = p->pRootResidualOffset[iTarget];
    int nSize = p->pRootResidualSize[iTarget];
    return iOffset >= 0 && nSize == Vec_IntSize(vSupport) &&
        !memcmp( Vec_IntArray(p->vResidualKeys) + iOffset,
            Vec_IntArray(vSupport), sizeof(int) * (size_t)nSize );
}

static Cec_TranSuppProfEnt_t * Cec_TranSuppProfLookup( Cec_TranSuppProf_t * p,
    int iTarget, Vec_Int_t * vSupport )
{
    Cec_TranSuppProfEnt_t * pEntry;
    word Hash;
    int i, iObj, iSlot, fFound;
    Vec_IntSort( vSupport, 0 );
    Hash = Cec_TranSuppProfHash( iTarget, vSupport );
    iSlot = Cec_TranSuppProfFindSlot( p, Hash, iTarget, vSupport, &fFound );
    if ( fFound )
        return p->pEntries + p->pBins[iSlot] - 1;
    if ( 10LL * (p->nEntries + 1) > 7LL * p->nBins )
    {
        Cec_TranSuppProfRehash( p );
        iSlot = Cec_TranSuppProfFindSlot( p, Hash, iTarget,
            vSupport, &fFound );
        assert( !fFound );
    }
    if ( p->nEntries == p->nEntriesCap )
    {
        p->nEntriesCap *= 2;
        p->pEntries = ABC_REALLOC( Cec_TranSuppProfEnt_t,
            p->pEntries, p->nEntriesCap );
    }
    pEntry = p->pEntries + p->nEntries;
    memset( pEntry, 0, sizeof(*pEntry) );
    pEntry->Hash = Hash;
    pEntry->iTarget = iTarget;
    pEntry->iOffset = Vec_IntSize( p->vKeys );
    pEntry->nSupport = Vec_IntSize( vSupport );
    pEntry->nMinGatesAccepted = 255;
    pEntry->nMinGatesProved = 255;
    pEntry->nMinGatesSelected = 255;
    Vec_IntForEachEntry( vSupport, iObj, i )
        Vec_IntPush( p->vKeys, iObj );
    p->pBins[iSlot] = ++p->nEntries;
    return pEntry;
}

static void Cec_TranSuppProfRecord( Cec_TranSuppProf_t * p, int iTarget,
    Vec_Int_t * vSupport, int nGates, int Stage, int Event )
{
    Cec_TranSuppProfEnt_t * pEntry;
    unsigned char StageBit = Stage >= 0 && Stage < 8 ?
        (unsigned char)(1 << Stage) : 0;
    if ( p == NULL )
        return;
    assert( iTarget > 0 && iTarget < p->nObjs );
    assert( Vec_IntSize(vSupport) > 0 );
    assert( nGates >= 0 && nGates < 255 );
    pEntry = Cec_TranSuppProfLookup( p, iTarget, vSupport );
    pEntry->fResidualGreedy |=
        Cec_TranSuppProfIsResidualGreedy( p, iTarget, vSupport );
    if ( Event == CEC_TRAN_SUPP_VALID )
    {
        p->pRootValidCands[iTarget]++;
        if ( pEntry->nValid++ == 0 )
            p->pRootValidSupps[iTarget]++;
        pEntry->StageValid |= StageBit;
    }
    else if ( Event == CEC_TRAN_SUPP_ACCEPTED )
    {
        p->pRootAcceptedCands[iTarget]++;
        if ( pEntry->nAccepted++ == 0 )
            p->pRootAcceptedSupps[iTarget]++;
        pEntry->nAcceptedGateSum += nGates;
        pEntry->nMinGatesAccepted = (unsigned char)Abc_MinInt(
            pEntry->nMinGatesAccepted, nGates );
        pEntry->StageAccepted |= StageBit;
    }
    else if ( Event == CEC_TRAN_SUPP_SUBMITTED )
    {
        pEntry->nSubmitted++;
        pEntry->StageSubmitted |= StageBit;
    }
    else if ( Event == CEC_TRAN_SUPP_REFUTED_BMC_BATCH ||
              Event == CEC_TRAN_SUPP_REFUTED_IND_BATCH ||
              Event == CEC_TRAN_SUPP_REFUTED_NO_SAT_BATCH )
    {
        pEntry->nRefuted++;
        pEntry->nRefutedBmcBatch +=
            Event == CEC_TRAN_SUPP_REFUTED_BMC_BATCH;
        pEntry->nRefutedIndBatch +=
            Event == CEC_TRAN_SUPP_REFUTED_IND_BATCH;
        pEntry->nRefutedNoSatBatch +=
            Event == CEC_TRAN_SUPP_REFUTED_NO_SAT_BATCH;
        pEntry->StageRefuted |= StageBit;
    }
    else if ( Event == CEC_TRAN_SUPP_UNKNOWN )
    {
        pEntry->nUnknown++;
        pEntry->StageUnknown |= StageBit;
    }
    else if ( Event == CEC_TRAN_SUPP_PROVED )
    {
        pEntry->nProved++;
        pEntry->nMinGatesProved = (unsigned char)Abc_MinInt(
            pEntry->nMinGatesProved, nGates );
        pEntry->StageProved |= StageBit;
    }
    else
    {
        assert( Event == CEC_TRAN_SUPP_SELECTED );
        pEntry->nSelected++;
        pEntry->nMinGatesSelected = (unsigned char)Abc_MinInt(
            pEntry->nMinGatesSelected, nGates );
        pEntry->StageSelected |= StageBit;
    }
}

static void Cec_TranSuppProfRecordCand( Cec_TranSuppProf_t * p,
    Cec_TranCand_t const * pCand, int Event )
{
    if ( p == NULL )
        return;
    assert( pCand->nKind == CEC_TRAN_CAND_CONSTR );
    Cec_TranCandCollectSupport( pCand, p->vScratch );
    Cec_TranSuppProfRecord( p, pCand->iTarget, p->vScratch,
        pCand->nGates, pCand->nResubStage, Event );
}

static int Cec_TranSuppProfResidualSizeBin( int nSize )
{
    return nSize <= 1 ? 0 : nSize == 2 ? 1 : nSize <= 4 ? 2 :
        nSize <= 8 ? 3 : nSize <= 16 ? 4 : nSize <= 32 ? 5 : 6;
}
