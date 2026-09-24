// Shared combinational and sequential candidate proof.
// Private implementation fragment included only by cecTrans.c.

// The correspondence SRM can place constants, ROs, and internal ANDs into
// speculative classes, but a free PI cannot be a class node: unlike an RO it
// has no frame-to-frame definition for Gia_ManCorrSpecReal().  Preserve useful
// root=PI candidates by representing each PI literal with one unstrashed
// ordinary AND proxy (x&1=x) in this temporary proof network.  The query PO
// retains the proxy through cleanup, and sharing by PI phase avoids inflating a
// large batch with duplicate wrappers.
static int Cec_TranRootClassEndpoint( Gia_Man_t * pNew, int iLit,
    int nPis, int * pPiProxies )
{
    Gia_Obj_t * pObj = Gia_ManObj( pNew, Abc_Lit2Var(iLit) );
    int iIndex;
    if ( !Gia_ObjIsCi(pObj) || Gia_ObjCioId(pObj) >= nPis )
        return iLit;
    iIndex = 2 * Gia_ObjCioId(pObj) + Abc_LitIsCompl(iLit);
    if ( pPiProxies[iIndex] == -1 )
        pPiProxies[iIndex] = Gia_ManAppendAnd( pNew, iLit, 1 );
    return pPiProxies[iIndex];
}

// Build one signal-correspondence instance for a group of strict Direct
// candidates.  The source transition relation is copied only once.  Candidate
// endpoint pairs seed speculative equivalence classes.  Root-XOR-replacement
// POs are built only by the separate bounded reachable-CEX harvesting miter;
// correspondence status itself is read directly from the refined classes.
static Gia_Man_t * Cec_TranBuildRootBatch( Gia_Man_t * p,
    Cec_TranCand_t const * pHelpers, int nHelpers,
    Cec_TranCand_t const * pCands, int nCands,
    int fCreateQueries,
    Vec_Int_t ** pvPairs, Vec_Int_t ** pvCombPairs, Vec_Int_t ** pvQueries,
    Vec_Int_t ** pvAndLeaves, Vec_Str_t ** pvAndCounts )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int nRelations = nHelpers + nCands;
    Vec_Int_t * vPairs = Vec_IntAlloc( 2 * nRelations );
    Vec_Int_t * vCombPairs = Vec_IntAlloc( 2 * nCands );
    Vec_Int_t * vQueries = Vec_IntAlloc( nCands );
    Vec_Int_t * vAndLeaves = pvAndLeaves ? Vec_IntAlloc( 2 * nCands ) : NULL;
    Vec_Str_t * vAndCounts = pvAndCounts ? Vec_StrAlloc( nCands ) : NULL;
    int nPis = Gia_ManPiNum(p);
    int * pPiProxies = nPis ? ABC_FALLOC( int, 2 * nPis ) : NULL;
    int Gates[CEC_TRAN_RECIPE_NODES_MAX];
    int Leaves[2 * CEC_TRAN_RECIPE_NODES_MAX + 1];
    int i, k, nLeaves, iLit0, iLit1, iRoot, iRep, iQuery;
    assert( nCands > 0 );
    assert( (pvAndLeaves != NULL) == (pvAndCounts != NULL) );
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + 4 * nRelations + 16 );
    pNew->pName = Abc_UtilStrsav( "stran_direct_root_batch" );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Gia_ObjFanin0Copy( pObj );
        iLit1 = Gia_ObjFanin1Copy( pObj );
        pObj->Value = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
    }
    for ( i = 0; i < nRelations; i++ )
    {
        Cec_TranCand_t const * pCand = i < nHelpers ?
            pHelpers + i : pCands + i - nHelpers;
        int fObligation = i >= nHelpers;
        iRoot = Cec_TranCopyLit( p, Abc_Var2Lit(pCand->iTarget, 0) );
        iRep = Cec_TranRecipeBuildMapped( p, pNew, pCand, Gates );
        if ( fObligation )
            Vec_IntPushTwo( vCombPairs, iRoot, iRep );
        if ( fObligation && vAndCounts )
        {
            nLeaves = Cec_TranRecipeCollectAndLeaves( pCand, Leaves );
            assert( nLeaves <= 2 * CEC_TRAN_RECIPE_NODES_MAX + 1 );
            for ( k = 0; k < nLeaves; k++ )
                Vec_IntPush( vAndLeaves, Cec_TranRecipeCopyCode(
                    p, Leaves[k], Gates, pCand->nGates) );
            Vec_StrPush( vAndCounts, (char)nLeaves );
        }
        // Build ordinary CBS/BMC queries from the real recipe endpoint.  A PI
        // proxy is only a correspondence-class representation; exposing its
        // unstrashed x&1 gate to CBS would make the solver visit constant
        // fanins, which are not CBS candidate variables.
        if ( fObligation && fCreateQueries )
        {
            iQuery = Gia_ManHashXor( pNew, iRoot, iRep );
            Vec_IntPush( vQueries, iQuery );
        }
        // Shared induction must constrain both physical endpoints used by the
        // transition relation.  Isolated x&1 wrappers are combinationally
        // equivalent but cannot carry the relation across frames.
        iRep = Cec_TranRootClassEndpoint( pNew, iRep,
            nPis, pPiProxies );
        Vec_IntPushTwo( vPairs, iRoot, iRep );
    }
    Vec_IntForEachEntry( vQueries, iQuery, i )
        Gia_ManAppendCo( pNew, iQuery );
    // Endpoint COs only keep seeded class members alive through cleanup.  A
    // normal correspondence closure reads status from representatives and
    // needs no XOR property at all; the separate reachable-CEX miter requests
    // XOR queries and retains candidate endpoints through those queries.
    // Mode 2 is the ordinary-CBS A/B path: keep the class endpoints as well
    // as the XOR queries because the same graph continues into scorr.  Mode 1
    // is the standalone reachable-CEX miter and must expose only query POs.
    for ( i = 0; fCreateQueries != 1 && i < Vec_IntSize(vPairs); i++ )
        Gia_ManAppendCo( pNew, Vec_IntEntry(vPairs, i) );
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    // Original POs are intentionally omitted, so remove their now-dangling
    // cones before Cec's reference-counted simulator is started.  Query POs
    // and every RI remain roots; remap the saved query literals through the
    // cleanup copy left in pTemp->Value.
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManDupRemapLiterals( vPairs, pTemp );
    Gia_ManDupRemapLiterals( vCombPairs, pTemp );
    Gia_ManDupRemapLiterals( vQueries, pTemp );
    if ( vAndLeaves )
        Gia_ManDupRemapLiterals( vAndLeaves, pTemp );
    Gia_ManStop( pTemp );
    ABC_FREE( pPiProxies );

    *pvPairs = vPairs;
    *pvCombPairs = vCombPairs;
    *pvQueries = vQueries;
    if ( pvAndLeaves )
        *pvAndLeaves = vAndLeaves;
    if ( pvAndCounts )
        *pvAndCounts = vAndCounts;
    return pNew;
}

static int Cec_TranRootLitPhase( Gia_Man_t * p, int iLit )
{
    return Gia_ObjPhase(Gia_ManObj(p, Abc_Lit2Var(iLit))) ^
        Abc_LitIsCompl(iLit);
}

static int Cec_TranRootUfFind( int * pParent, int iObj )
{
    int iRoot = iObj;
    while ( pParent[iRoot] != iRoot )
        iRoot = pParent[iRoot];
    while ( pParent[iObj] != iObj )
    {
        int iNext = pParent[iObj];
        pParent[iObj] = iRoot;
        iObj = iNext;
    }
    return iRoot;
}

// Seed the transitive closure of candidate endpoint relations.  For example,
// a=b and a=c enter correspondence as one speculative class {a,b,c}; a CEX
// can split c without discarding a=b.  The smallest object ID is the class
// head, as required by Gia representatives.
static void Cec_TranSeedRootClasses( Gia_Man_t * p, Vec_Int_t * vPairs )
{
    int * pParent = ABC_ALLOC( int, Gia_ManObjNum(p) );
    int i, iLit0, iLit1, iObj0, iObj1, iRoot0, iRoot1;
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        pParent[i] = i;
    for ( i = 0; i < Vec_IntSize(vPairs); i += 2 )
    {
        iLit0 = Vec_IntEntry( vPairs, i );
        iLit1 = Vec_IntEntry( vPairs, i + 1 );
        if ( Cec_TranRootLitPhase(p, iLit0) !=
             Cec_TranRootLitPhase(p, iLit1) )
            continue;
        iObj0 = Abc_Lit2Var( iLit0 );
        iObj1 = Abc_Lit2Var( iLit1 );
        iRoot0 = Cec_TranRootUfFind( pParent, iObj0 );
        iRoot1 = Cec_TranRootUfFind( pParent, iObj1 );
        if ( iRoot0 == iRoot1 )
            continue;
        if ( iRoot0 < iRoot1 )
            pParent[iRoot1] = iRoot0;
        else
            pParent[iRoot0] = iRoot1;
    }
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
    {
        iRoot0 = Cec_TranRootUfFind( pParent, i );
        if ( iRoot0 != i )
            Gia_ObjSetRepr( p, i, iRoot0 );
    }
    ABC_FREE( pParent );
}

static int Cec_TranRootBatchPairProved( Gia_Man_t * p,
    int iLit0, int iLit1 )
{
    int iObj0 = Abc_Lit2Var( iLit0 );
    int iObj1 = Abc_Lit2Var( iLit1 );
    int iHead0, iHead1;
    if ( Cec_TranRootLitPhase(p, iLit0) != Cec_TranRootLitPhase(p, iLit1) )
        return 0;
    iHead0 = Gia_ObjRepr(p, iObj0) == GIA_VOID ?
        iObj0 : Gia_ObjRepr(p, iObj0);
    iHead1 = Gia_ObjRepr(p, iObj1) == GIA_VOID ?
        iObj1 : Gia_ObjRepr(p, iObj1);
    return iHead0 == iHead1;
}

// Solve one counterexample cube directly on the shared candidate graph.  CBS
// returns 1 for UNSAT, 0 for SAT, and -1 for UNKNOWN.
static int Cec_TranCombSolveCube( Cbs_Man_t * pCbs, int const * pLits,
    int nLits, int fSaveModel, Cec_TranProf_t * pProf )
{
    int Status = fSaveModel ?
        Cbs_ManSolveLits( pCbs, pLits, nLits ) :
        Cbs_ManSolveLitsNoModel( pCbs, pLits, nLits );
    pProf->nCombNoModelCalls += !fSaveModel;
    pProf->nCombConfUsed += Cbs_ManReadConflicts( pCbs );
    return Status;
}

// Correspondence represents a PI endpoint with an unstrashed x&1 proxy.
// Remove that proof-only wrapper before passing a literal to CBS.
static int Cec_TranCombUnwrapPiProxy( Gia_Man_t * pBatch, int iLit )
{
    Gia_Obj_t * pObj = Gia_ManObj( pBatch, Abc_Lit2Var(iLit) );
    int iLit0, iLit1, iReal = -1;
    if ( !Gia_ObjIsAnd(pObj) )
        return iLit;
    iLit0 = Gia_ObjFaninLit0p( pBatch, pObj );
    iLit1 = Gia_ObjFaninLit1p( pBatch, pObj );
    if ( iLit0 == 1 )
        iReal = iLit1;
    else if ( iLit1 == 1 )
        iReal = iLit0;
    return iReal == -1 ? iLit :
        Abc_LitNotCond( iReal, Abc_LitIsCompl(iLit) );
}

// Solve one explicitly constructed XOR query through CBS's ordinary
// single-root interface.  This path exists as an A/B baseline for the direct
// multi-literal interface above; both share the same manager and conflict cap.
static int Cec_TranCombSolveQuery( Cbs_Man_t * pCbs, Gia_Man_t * pBatch,
    int iQuery, int fSaveModel, Cec_TranProf_t * pProf )
{
    int Status = fSaveModel ?
        Cbs_ManSolve( pCbs, Gia_ObjFromLit(pBatch, iQuery) ) :
        Cbs_ManSolveNoModel( pCbs, Gia_ObjFromLit(pBatch, iQuery) );
    pProf->nCombNoModelCalls += !fSaveModel;
    pProf->nCombConfUsed += Cbs_ManReadConflicts( pCbs );
    return Status;
}

// Candidate-directed combinational equivalence.  Registers are treated as
// independent CIs, so every UNSAT result is valid in all states.  A generic
// a=h relation is two implication counterexample cubes.  If h is a recipe
// AND/NAND cone, flatten only that recipe cone into one short cube per leaf
// plus one long cube; the first SAT cube terminates the candidate immediately.
static Vec_Str_t * Cec_TranProveCombBatch( Gia_Man_t * pBatch,
    Cec_TranCand_t const * pCands, int nCands, Vec_Int_t * vPairs,
    Vec_Int_t * vQueries, Vec_Int_t * vAndLeaves, Vec_Str_t * vAndCounts,
    Cec_ParTran_t * pPars, Cec_TranProf_t * pProf,
    int fStopAtFirstProof, int * pnAttempted )
{
    Cbs_Man_t * pCbs = Cbs_ManAlloc( pBatch );
    Cec_TranFreeSim_t * pFree = NULL;
    Vec_Str_t * vStage = Vec_StrStart( nCands );
    int Cube[2 * CEC_TRAN_RECIPE_NODES_MAX + 2];
    int i, k, iBeg = 0, iEnd = 0, nLeaves, a, h, t;
    int Status, fSat, fUnknown, fSaveModel, FreeMismatch;
    abctime clk = Abc_Clock(), timeSolve = 0, clkSolve;
    if ( pPars->fUseFreeSim && (pPars->nFreeWords || pPars->nFreeCexMax) )
        pFree = Cec_TranFreeSimStart( pBatch, pPars->nFreeWords,
            pPars->nFreeCexMax );
    Cbs_ManSetConflictNum( pCbs, pPars->nCombBTLimit );
    assert( pPars->fUseCbsMultiLit || Vec_IntSize(vQueries) == nCands );
    if ( pnAttempted )
        *pnAttempted = 0;
    for ( i = 0; i < nCands; i++ )
    {
        if ( pnAttempted )
            (*pnAttempted)++;
        nLeaves = pPars->fUseCbsMultiLit ?
            (unsigned char)Vec_StrEntry(vAndCounts, i) : 0;
        iBeg = iEnd;
        iEnd += nLeaves;
        a = Vec_IntEntry( vPairs, 2*i );
        h = Vec_IntEntry( vPairs, 2*i + 1 );
        h = Cec_TranCombUnwrapPiProxy( pBatch, h );
        if ( a == h )
        {
            Vec_StrWriteEntry( vStage, i, 1 );
            pProf->nCombProved++;
            if ( fStopAtFirstProof )
                break;
            continue;
        }
        if ( pFree )
        {
            FreeMismatch = Cec_TranFreeSimMismatch( pFree, a, h );
            if ( FreeMismatch )
                continue;
        }
        // Model extraction is useful only while the batch CEGIS bank still
        // has room.  Once full, use the cheaper solve entry point for every
        // remaining cube/query instead of repeatedly collecting unused CIs.
        fSaveModel = pFree != NULL && pFree->nCexes < pFree->nCexMax;
        fSat = fUnknown = 0;
        if ( !pPars->fUseCbsMultiLit )
        {
            clkSolve = Abc_Clock();
            Status = Cec_TranCombSolveQuery( pCbs, pBatch,
                Vec_IntEntry(vQueries, i), fSaveModel, pProf );
            timeSolve += Abc_Clock() - clkSolve;
            if ( Status == 0 )
            {
                pProf->nCombDisproved++;
                if ( fSaveModel && pFree->nCexes < pFree->nCexMax )
                {
                    abctime clkFree = Abc_Clock();
                    if ( Cec_TranFreeSimAddModel(pFree, Cbs_ReadModel(pCbs), a, h) )
                        pProf->nCombFreeCexStored++;
                    else
                        pProf->nCombFreeCexInvalid++;
                    pProf->timeFreeCexSim += Abc_Clock() - clkFree;
                }
            }
            else if ( Status < 0 )
                pProf->nCombUnknown++;
            else
            {
                Vec_StrWriteEntry( vStage, i, 1 );
                pProf->nCombProved++;
                if ( fStopAtFirstProof )
                    break;
            }
            continue;
        }
        if ( nLeaves )
        {
            int iOutLit = Cec_TranRecipeGateLit( pCands[i].iOut );
            // If h = AND(leaves), a != h is covered by one short cube
            // a & !leaf[k] per leaf, plus one long cube !a & all(leaves).
            // For a complemented recipe output, replacing a by !a gives the
            // same cover.  Only recipe ANDs were flattened when the shared
            // proof graph was built; original divisor cones stay atomic.
            t = Abc_LitNotCond( a, Abc_LitIsCompl(iOutLit) );
            for ( k = iBeg; k < iEnd; k++ )
            {
                Cube[0] = t;
                Cube[1] = Abc_LitNot( Vec_IntEntry(vAndLeaves, k) );
                clkSolve = Abc_Clock();
                Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                    fSaveModel, pProf );
                timeSolve += Abc_Clock() - clkSolve;
                if ( Status == 0 ) { fSat = 1; break; }
                if ( Status < 0 )
                {
                    fUnknown = 1;
                    pProf->nCombUnknownEarly++;
                    pProf->nCombCubesSkippedUnknown += iEnd - k;
                    break;
                }
            }
            if ( !fSat && !fUnknown )
            {
                Cube[0] = Abc_LitNot( t );
                for ( k = 0; k < nLeaves; k++ )
                    Cube[k+1] = Vec_IntEntry( vAndLeaves, iBeg + k );
                clkSolve = Abc_Clock();
                Status = Cec_TranCombSolveCube( pCbs, Cube, nLeaves + 1,
                    fSaveModel, pProf );
                timeSolve += Abc_Clock() - clkSolve;
                if ( Status == 0 )
                    fSat = 1;
                else
                {
                    fUnknown = Status < 0;
                    pProf->nCombUnknownEarly += Status < 0;
                }
            }
        }
        else
        {
            Cube[0] = a;             Cube[1] = Abc_LitNot(h);
            clkSolve = Abc_Clock();
            Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                fSaveModel, pProf );
            timeSolve += Abc_Clock() - clkSolve;
            if ( Status == 0 )
                fSat = 1;
            else
            {
                fUnknown = Status < 0;
                if ( fUnknown )
                {
                    pProf->nCombUnknownEarly++;
                    pProf->nCombCubesSkippedUnknown++;
                }
            }
            if ( !fSat && !fUnknown )
            {
                Cube[0] = Abc_LitNot(a); Cube[1] = h;
                clkSolve = Abc_Clock();
                Status = Cec_TranCombSolveCube( pCbs, Cube, 2,
                    fSaveModel, pProf );
                timeSolve += Abc_Clock() - clkSolve;
                if ( Status == 0 )
                    fSat = 1;
                else
                {
                    fUnknown = Status < 0;
                    pProf->nCombUnknownEarly += Status < 0;
                }
            }
        }
        if ( fSat )
        {
            pProf->nCombDisproved++;
            if ( fSaveModel && pFree->nCexes < pFree->nCexMax )
            {
                abctime clkFree = Abc_Clock();
                if ( Cec_TranFreeSimAddModel(pFree, Cbs_ReadModel(pCbs), a, h) )
                    pProf->nCombFreeCexStored++;
                else
                    pProf->nCombFreeCexInvalid++;
                pProf->timeFreeCexSim += Abc_Clock() - clkFree;
            }
        }
        else if ( fUnknown )
            pProf->nCombUnknown++;
        else
        {
            Vec_StrWriteEntry( vStage, i, 1 );
            pProf->nCombProved++;
            if ( fStopAtFirstProof )
                break;
        }
    }
    pProf->timeCombSolve += timeSolve;
    pProf->timeRootCbsScreen += Abc_Clock() - clk - timeSolve;
    Cec_TranFreeSimStop( pFree );
    Cbs_ManStop( pCbs );
    return vStage;
}

// Return one status bit per candidate.  Seed candidate endpoints as ordinary
// equivalence classes and run one shared correspondence closure over exactly
// these relations.  This retains &scorr's standard BMC, SRM, CEX resimulation,
// class refinement, and induction fixed point without unrelated class search.
static Vec_Int_t * Cec_TranProveRootBatchPrepared( Gia_Man_t * pBatch,
    Cec_TranCand_t const * pCands, int nCands, int nHelpers,
    Cec_ParTran_t * pPars, Cec_TranProf_t * pProf, int fCombOnly,
    Vec_Str_t ** pvStage, Vec_Int_t * vPairs, Vec_Int_t * vCombPairs,
    Vec_Int_t * vQueries, Vec_Int_t * vAndLeaves, Vec_Str_t * vAndCounts )
{
    Cec_ParCor_t Cor;
    Gia_Obj_t * pObj;
    Vec_Int_t * vSeqPairs = NULL;
    Vec_Int_t * vStatus = Vec_IntStart( nCands );
    Vec_Str_t * vStage;
    Cec_ProfCor_t CorrBefore;
    int i, RetValue = 1, nSeq = 0;
    int nSeqSplit = 0, nSeqUnknown = 0, nSeqRoots = 0;
    int SuppRefuteEvent = CEC_TRAN_SUPP_REFUTED_NO_SAT_BATCH;
    abctime clk, timeSeq = 0;
    memset( &Cor, 0, sizeof(Cor) );
    pProf->nRootSrmNodesMax = Abc_MaxInt(
        pProf->nRootSrmNodesMax, Gia_ManObjNum(pBatch) );
    vStage = Cec_TranProveCombBatch( pBatch, pCands, nCands,
        vCombPairs, vQueries, vAndLeaves, vAndCounts, pPars, pProf,
        0, NULL );
    if ( !fCombOnly )
        for ( i = 0; i < nCands; i++ )
            if ( Vec_StrEntry(vStage, i) == 0 )
                nSeq++;
    pProf->nSeqCands += nSeq;
    if ( nSeq )
    {
        int iPrevTarget = -1, nClass = 0;
        for ( i = 0; i < nCands; i++ )
            {
                if ( pCands[i].iTarget != iPrevTarget )
                {
                    if ( nClass )
                    {
                        pProf->nSeqClassSum += nClass + 1;
                        pProf->nSeqClassMax = Abc_MaxInt(
                            pProf->nSeqClassMax, nClass + 1 );
                    }
                    nSeqRoots++;
                    iPrevTarget = pCands[i].iTarget;
                    nClass = 0;
                }
                nClass++;
            }
        if ( nClass )
        {
            pProf->nSeqClassSum += nClass + 1;
            pProf->nSeqClassMax = Abc_MaxInt(
                pProf->nSeqClassMax, nClass + 1 );
        }
        pProf->nSeqRoots += nSeqRoots;
        Gia_ManSetPhase( pBatch );
        pBatch->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(pBatch) );
        Gia_ManForEachObj( pBatch, pObj, i )
            Gia_ObjSetRepr( pBatch, i, GIA_VOID );
        Gia_ManCreateValueRefs( pBatch );
        // Universally proved combinational relations remain in the same
        // hypothesis as induction helpers.  They are not sequential proof
        // obligations, but removing them can break a shared invariant.
        vSeqPairs = Vec_IntAlloc( 2 * (nHelpers + nCands) );
        for ( i = 0; i < nHelpers + nCands; i++ )
            Vec_IntPushTwo( vSeqPairs, Vec_IntEntry(vPairs, 2*i),
                Vec_IntEntry(vPairs, 2*i + 1) );
        Cec_TranSeedRootClasses( pBatch, vSeqPairs );
        pProf->nSeqSeeded += Vec_IntSize(vSeqPairs) / 2;
        pBatch->pNexts = Gia_ManDeriveNexts( pBatch );
        Cec_ManCorSetDefaultParams( &Cor );
        Cor.nFrames   = pPars->nFrames;
        Cor.nBTLimit  = pPars->nBTLimit;
        // Root scorr intentionally has no shared conflict cap.  -C is the
        // per-output limit; an UNKNOWN output is removed from only its own
        // speculative class by ordinary scorr refinement.  A shared cap would
        // make solve order turn one hard relation into a global early stop.
        Cor.nConfTotal = 0;
        Cor.nStepsMax = pPars->nStepsMax;
        Cor.fVerbose  = 0;
        Cor.pProfile  = pPars->fProfile ? &pProf->Corr : NULL;
        if ( pProf->pStrictCex )
        {
            assert( !fCombOnly && pProf->DiagPhase == 1 );
            Cor.pCexFunc = Cec_TranStrictCexObserve;
            Cor.pCexData = pProf->pStrictCex;
        }
        CorrBefore = pProf->Corr;
        clk = Abc_Clock();
        RetValue = Cec_ManLSCorrespondenceClasses( pBatch, &Cor );
        timeSeq = Abc_Clock() - clk;
        // The correspondence profiler exposes aggregate SAT causes, not the
        // class split caused by each individual obligation.  Keep this label
        // explicitly batch-scoped: BMC dominates when both phases saw SAT;
        // "ind-only" means this batch saw no reset-reachable BMC SAT.
        if ( pPars->fProfile )
        {
            if ( pProf->Corr.nBmcSat > CorrBefore.nBmcSat )
                SuppRefuteEvent = CEC_TRAN_SUPP_REFUTED_BMC_BATCH;
            else if ( pProf->Corr.nIndSat > CorrBefore.nIndSat )
                SuppRefuteEvent = CEC_TRAN_SUPP_REFUTED_IND_BATCH;
        }
        // Detailed correspondence counters use nanosecond ticks.  Attribute
        // the complete base phase, inductive SAT, and resimulation separately;
        // the remaining wall time is class management and fixed-point control.
        {
            abctime TimeSrm = 0, TimeBmc = 0, TimeIndSat = 0;
            abctime TimeResim = 0, Remain = timeSeq, Use;
            if ( pPars->fProfile )
            {
                double BmcHr = pProf->Corr.timeBmc - CorrBefore.timeBmc;
                double BmcSrmHr = pProf->Corr.timeBmcSrm - CorrBefore.timeBmcSrm;
                double BmcSimHr = pProf->Corr.timeBmcSim - CorrBefore.timeBmcSim;
                double IndSrmHr = pProf->Corr.timeIndSrm - CorrBefore.timeIndSrm;
                double IndSatHr = pProf->Corr.timeIndSat - CorrBefore.timeIndSat;
                double IndSimHr = pProf->Corr.timeIndSim - CorrBefore.timeIndSim;
                double BmcOtherHr = BmcHr - BmcSrmHr - BmcSimHr;
                if ( BmcOtherHr < 0 )
                    BmcOtherHr = 0;
                TimeSrm = (abctime)(1.0e-9 * (BmcSrmHr + IndSrmHr) * CLOCKS_PER_SEC);
                TimeBmc = (abctime)(1.0e-9 * BmcOtherHr * CLOCKS_PER_SEC);
                TimeIndSat = (abctime)(1.0e-9 * IndSatHr * CLOCKS_PER_SEC);
                TimeResim = (abctime)(1.0e-9 * (BmcSimHr + IndSimHr) * CLOCKS_PER_SEC);
                Use = TimeSrm < Remain ? TimeSrm : Remain;
                pProf->timeRootScorrGraph += Use; Remain -= Use;
                Use = TimeBmc < Remain ? TimeBmc : Remain;
                pProf->timeRootScorrBmc += Use; Remain -= Use;
                Use = TimeIndSat < Remain ? TimeIndSat : Remain;
                pProf->timeRootScorrIndSat += Use; Remain -= Use;
                Use = TimeResim < Remain ? TimeResim : Remain;
                pProf->timeRootScorrResim += Use; Remain -= Use;
                pProf->timeRootScorrOther += Remain;
            }
            else
                pProf->timeRootScorrOther += timeSeq;
        }
        if ( Cor.fCompleted )
            pProf->nSeqFixedRounds += Cor.nRoundsDone;
    }
    for ( i = 0; i < nCands; i++ )
    {
        int fProved = Vec_StrEntry(vStage, i) == 1;
        int fBatchComplete = 0;
        if ( !fProved && nSeq )
        {
            int fSameClass = Cec_TranRootBatchPairProved( pBatch,
                Vec_IntEntry(vPairs, 2*(nHelpers+i)),
                Vec_IntEntry(vPairs, 2*(nHelpers+i)+1) );
            fBatchComplete = RetValue && Cor.fCompleted;
            // fConfStop can only accompany an incomplete correspondence run;
            // it is not the per-output UNKNOWN indication.  Keep the invariant
            // explicit so callers cannot accidentally reintroduce batch-wide
            // poisoning for ordinary solver UNKNOWNs.
            assert( !Cor.fConfStop || !Cor.fCompleted );
            fProved = fBatchComplete && fSameClass;
            if ( !fProved )
            {
                // As in ordinary &scorr, SAT counterexamples split only the
                // affected speculative class.  A global early stop is UNKNOWN;
                // a completed fixed point classifies each relation by whether
                // its endpoints survived in the same refined class.
                nSeqSplit += fBatchComplete && !fSameClass;
                nSeqUnknown += !fBatchComplete;
            }
        }
        if ( !fProved && !fCombOnly && nSeq &&
             pCands[i].nKind == CEC_TRAN_CAND_CONSTR )
            Cec_TranSuppProfRecordCand( pProf->pBuildSuppProf, pCands + i,
                fBatchComplete ? SuppRefuteEvent :
                    CEC_TRAN_SUPP_UNKNOWN );
        if ( fProved && Vec_StrEntry(vStage, i) == 0 )
        {
            Vec_StrWriteEntry( vStage, i, 2 );
            pProf->nSeqProved++;
        }
        Vec_IntWriteEntry( vStatus, i, fProved );
    }
    pProf->nRootBatchCalls++;
    pProf->nRootBatchMax = Abc_MaxInt( pProf->nRootBatchMax,
        nHelpers + nCands );
    pProf->nSeqSplit += nSeqSplit;
    pProf->nSeqUnknown += nSeqUnknown;
    Vec_IntFree( vPairs );
    Vec_IntFree( vCombPairs );
    Vec_IntFree( vQueries );
    Vec_IntFreeP( &vSeqPairs );
    Vec_IntFreeP( &vAndLeaves );
    Vec_StrFreeP( &vAndCounts );
    Gia_ManStop( pBatch );
    *pvStage = vStage;
    return vStatus;
}

static Vec_Int_t * Cec_TranProveRootBatch( Gia_Man_t * p,
    Cec_TranCand_t const * pHelpers, int nHelpers,
    Cec_TranCand_t const * pCands, int nCands, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, int fCombOnly, Vec_Str_t ** pvStage )
{
    Vec_Int_t * vPairs, * vCombPairs, * vQueries;
    Vec_Int_t * vAndLeaves = NULL;
    Vec_Str_t * vAndCounts = NULL;
    abctime clk = Abc_Clock();
    Gia_Man_t * pBatch = Cec_TranBuildRootBatch( p, pHelpers, nHelpers,
        pCands, nCands, !pPars->fUseCbsMultiLit ? 2 : 0,
        &vPairs, &vCombPairs, &vQueries,
        pPars->fUseCbsMultiLit ? &vAndLeaves : NULL,
        pPars->fUseCbsMultiLit ? &vAndCounts : NULL );
    pProf->timeRootCbsGraph += Abc_Clock() - clk;
    return Cec_TranProveRootBatchPrepared(pBatch,pCands,nCands,nHelpers,
        pPars,pProf,fCombOnly,pvStage,vPairs,vCombPairs,vQueries,
        vAndLeaves,vAndCounts);
}

// A correspondence counterexample produced during induction is a local SRM
// assignment and need not be reachable from reset.  Between construct waves,
// therefore, ask one bounded reset-reachable question over all failed
// constructed recipes.  One real trace is enough to rebuild every signature
// and dependency problem in the next wave.
static int Cec_TranRootCandidateGainEval( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, Cec_TranProf_t * pProf )
{
    Gia_Obj_t * pRoot = Gia_ManObj( p, pCand->iTarget );
    int Used[2 * CEC_TRAN_RECIPE_NODES_MAX + 1];
    int Gain, i, k, Code, iObj, nUsed = 0, fSeen;
    abctime clk = Abc_Clock();

    // Root scheduling needs the local structural gain, not a rebuilt copy of
    // the complete sequential network.  Temporarily add the replacement's
    // fanin references, dereference the target MFFC, and restore the original
    // reference counts.  This is O(affected MFFC), changes no graph objects,
    // and correctly keeps a divisor that lies inside the removed cone alive.
    // The recipe costs at most nGates new AIG nodes; structural hashing can
    // only improve the final gain.  Strict-root candidates cache the simpler
    // MFFC-nGates bound at discovery, so this affected-MFFC walk is only a
    // fallback for lanes whose divisors are not guaranteed outside the MFFC.
    // The one real bundle commit below still performs cleanup and checks the
    // exact combined AND+register gain.
    assert( p->pRefs != NULL );
    assert( Gia_ObjIsAnd(pRoot) );
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) )
            continue;
        iObj = Abc_Lit2Var( Code );
        if ( iObj == 0 || !Gia_ObjIsAnd(Gia_ManObj(p, iObj)) )
            continue;
        fSeen = 0;
        for ( k = 0; k < nUsed; k++ )
            fSeen |= Used[k] == iObj;
        if ( fSeen )
            continue;
        Used[nUsed++] = iObj;
        Gia_ObjRefIncId( p, iObj );
    }
    Gain = Gia_NodeMffcSize( p, pRoot );
    for ( i = 0; i < nUsed; i++ )
        Gia_ObjRefDecId( p, Used[i] );
    Gain -= pCand->nGates;
    pProf->timeGain += Abc_Clock() - clk;
    pProf->nGainCalls++;
    return Gain;
}

static int Cec_TranCandGainCompare( const void * p0, const void * p1 )
{
    Cec_TranCand_t const * pC0 = (Cec_TranCand_t const *)p0;
    Cec_TranCand_t const * pC1 = (Cec_TranCand_t const *)p1;
    if ( pC0->Gain != pC1->Gain )
        return pC1->Gain - pC0->Gain;
    if ( pC0->nKind != pC1->nKind )
        return pC0->nKind - pC1->nKind;
    if ( pC0->nGates != pC1->nGates )
        return pC0->nGates - pC1->nGates;
    if ( pC0->iOut != pC1->iOut )
        return pC0->iOut - pC1->iOut;
    return memcmp( pC0->Recipe, pC1->Recipe,
        sizeof(int) * 2 * pC0->nGates );
}
