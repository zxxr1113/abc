// TFI/TFO divisor collection and ranking.
// Private implementation fragment included only by cecTrans.c.

// This mask is only a divisor-routing heuristic, not an MFFC computation.
// Following the initial ref==1 tree reaches the external boundary without
// excluding reconvergent internal nodes that are legal replacement supports.
// Candidate gain and selection always use the exact deref/ref MFFC above.
static void Cec_TranMarkDivExclusion_rec( Gia_Man_t * p, int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    char * pMark, Vec_Int_t * vMarked )
{
    Gia_Obj_t * pObj;
    int iFan;
    if ( Cec_TranMffcIsBoundary(iObj, iRoot, pCovered, pUsed, NULL) ||
         pMark[iObj] )
        return;
    pMark[iObj] = 1;
    Vec_IntPush( vMarked, iObj );
    pObj = Gia_ManObj( p, iObj );
    if ( !Gia_ObjIsAnd(pObj) )
        return;
    iFan = Gia_ObjFaninId0p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         Gia_ObjRefNumId(p, iFan) == 1 )
        Cec_TranMarkDivExclusion_rec( p, iFan, iRoot, pCovered, pUsed,
            pMark, vMarked );
    iFan = Gia_ObjFaninId1p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         Gia_ObjRefNumId(p, iFan) == 1 )
        Cec_TranMarkDivExclusion_rec( p, iFan, iRoot, pCovered, pUsed,
            pMark, vMarked );
}

static int Cec_TranCandDynamicGainWithRefs( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, char const * pCovered,
    char const * pUsed, int * pRefs, char * pMffc, Vec_Int_t * vMffc,
    Vec_Int_t * vSupport )
{
    int i, iObj;
    if ( (pCovered && pCovered[pCand->iTarget]) ||
         (pUsed && pUsed[pCand->iTarget]) )
        return -1;
    Cec_TranCandCollectSupport( pCand, vSupport );
    Vec_IntForEachEntry( vSupport, iObj, i )
        if ( pCovered && pCovered[iObj] )
            return -1;
    // The current recipe creates references to its support too.  Treat that
    // support as a boundary while computing this candidate's kill-set; this
    // is what makes an earlier equivalent inside the static MFFC legal.
    if ( pRefs )
        Cec_TranMarkDynamicMffcWithRefs( p, pCand->iTarget, pCovered,
            pUsed, vSupport, pRefs, pMffc, vMffc );
    else
        Cec_TranMarkDynamicMffc( p, pCand->iTarget, pCovered, pUsed,
            vSupport, pMffc, vMffc );
    Vec_IntForEachEntry( vSupport, iObj, i )
        if ( pMffc[iObj] )
            return -1;
    return Vec_IntSize(vMffc) - pCand->nGates;
}

static int Cec_TranCandDynamicGain( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, char const * pCovered,
    char const * pUsed, char * pMffc, Vec_Int_t * vMffc,
    Vec_Int_t * vSupport )
{
    return Cec_TranCandDynamicGainWithRefs( p, pCand, pCovered, pUsed,
        NULL, pMffc, vMffc, vSupport );
}

static int Cec_TranCandFrozenGainWithRefs( Gia_Man_t * p,
    Cec_TranFrozenHash_t const * pHash, Cec_TranCand_t const * pCand,
    char const * pCovered, char const * pUsed, int * pRefs,
    char * pMffc, Vec_Int_t * vMffc, Vec_Int_t * vBoundary )
{
    int i, iObj, nNew;
    if ( (pCovered && pCovered[pCand->iTarget]) ||
         (pUsed && pUsed[pCand->iTarget]) )
        return -1;
    Cec_TranCandCollectSupport( pCand, vBoundary );
    Vec_IntForEachEntry( vBoundary, iObj, i )
        if ( pCovered && pCovered[iObj] )
            return -1;
    nNew = Cec_TranFrozenRecipeCost( p, pHash, pCand,
        pCovered, vBoundary );
    Cec_TranMarkDynamicMffcWithRefs( p, pCand->iTarget,
        pCovered, pUsed, vBoundary, pRefs, pMffc, vMffc );
    // A target used as its own replacement is the only boundary which the
    // MFFC traversal deliberately cannot cut.  Reject it as a cycle.
    Vec_IntForEachEntry( vBoundary, iObj, i )
        if ( pMffc[iObj] )
            return -1;
    return Vec_IntSize(vMffc) - nNew;
}

// Collect physical divisor nodes by increasing TFI distance.  The routing mask
// skips only the initial exclusive tree; reconvergent nodes deeper inside the
// exact MFFC remain legal because replacement support keeps them alive.  Exact
// dynamic gain later recomputes the kill-set with that support as a boundary.
// PI and RO objects are legal CIs, and all retained nodes precede the target.
static Vec_Int_t * Cec_TranCollectDivPool( Gia_Man_t * p, int iTarget,
    int nDepthMax, int nNodesMax, int fUseMffcDivs, char const * pCovered,
    char const * pUsed, char * pMffc, Vec_Int_t * vMffc,
    int fUseTfoDivs, int nTfoMax, Vec_Int_t * vTfo,
    Cec_TranTfoStats_t * pTfoStats )
{
    Vec_Int_t * vPool = Vec_IntAlloc( nNodesMax ? nNodesMax : 64 );
    Vec_Int_t * vFront = Vec_IntAlloc( 32 );
    Vec_Int_t * vNext = Vec_IntAlloc( 32 );
    Vec_Int_t * vSeeds = fUseTfoDivs ? Vec_IntAlloc( 64 ) : NULL;
    Gia_Obj_t * pObj, * pFan;
    int d, i, k, iObj, iFan, fFull = 0;
    abctime clkTfo = 0;
    assert( !fUseTfoDivs || (p->vFanoutNums && p->vFanout && vTfo) );
    if ( vTfo )
        Vec_IntClear( vTfo );
    if ( pTfoStats )
        memset( pTfoStats, 0, sizeof(*pTfoStats) );
    Cec_TranMffcScratchClear( pMffc, vMffc );
    if ( fUseMffcDivs )
        Cec_TranMarkDivExclusion_rec( p, iTarget, iTarget, pCovered, pUsed,
            pMffc, vMffc );
    else
        Cec_TranMarkDynamicMffc( p, iTarget, pCovered, pUsed, NULL,
            pMffc, vMffc );
    // The BFS used to allocate and clear one |G|-byte pSeen array per root.
    // Traversal IDs provide the same membership test with O(visited TFI)
    // writes and no per-root full-graph zeroing.
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrentId( p, iTarget );
    Vec_IntPush( vFront, iTarget );
    for ( d = 1; Vec_IntSize(vFront) && (!nDepthMax || d <= nDepthMax); d++ )
    {
        Vec_IntClear( vNext );
        Vec_IntForEachEntry( vFront, iObj, i )
        {
            pObj = Gia_ManObj( p, iObj );
            if ( !Gia_ObjIsAnd(pObj) )
                continue;
            for ( k = 0; k < 2; k++ )
            {
                iFan = k ? Gia_ObjFaninId1p(p, pObj) :
                           Gia_ObjFaninId0p(p, pObj);
                if ( Gia_ObjIsTravIdCurrentId(p, iFan) )
                    continue;
                Gia_ObjSetTravIdCurrentId( p, iFan );
                if ( vSeeds )
                    Vec_IntPush( vSeeds, iFan );
                pFan = Gia_ManObj( p, iFan );
                if ( iFan != 0 && iFan < iTarget && Gia_ObjIsCand(pFan) &&
                     !pMffc[iFan] && !fFull )
                {
                    Vec_IntPush( vPool, iFan );
                    fFull = nNodesMax && Vec_IntSize(vPool) >= nNodesMax;
                }
                if ( Gia_ObjIsAnd(pFan) )
                    Vec_IntPush( vNext, iFan );
            }
        }
        // The ranked divisor reservoir and the structural TFI membership have
        // different purposes.  Once the reservoir is full, TFI-only mode can
        // stop as before.  Complete-fanin TFO mode must keep walking to the
        // requested depth so a fanout is not rejected merely because one of
        // its fanins appeared after the reservoir budget was exhausted.
        if ( fFull && !fUseTfoDivs )
            break;
        ABC_SWAP( Vec_Int_t, *vFront, *vNext );
    }
    // Expand only through fanouts whose two physical AIG fanins are already
    // members of the root-local structural window.  The target and every true
    // target fanout are topologically later and are excluded by iFan<iTarget.
    // Additions never become membership witnesses: this is exactly the
    // one-hop shell requested by the complete-fanin rule, not a recursive
    // forward closure.  Legal-candidate filtering stays separate from
    // structural membership: MFFC nodes may justify completeness without
    // themselves entering the divisor reservoir.
    if ( fUseTfoDivs )
    {
        int nSeedSize = Vec_IntSize( vSeeds );
        int nTfoLimit = nTfoMax ? nTfoMax :
            (nNodesMax ? nNodesMax : 256);
        clkTfo = Abc_Clock();
        for ( i = 0; i < nSeedSize; i++ )
        {
            int f;
            iObj = Vec_IntEntry( vSeeds, i );
            if ( pTfoStats )
                pTfoStats->nScanned++;
            Gia_ObjForEachFanoutStaticId( p, iObj, iFan, f )
            {
                int iFan0, iFan1;
                if ( pTfoStats )
                    pTfoStats->nEdges++;
                if ( iFan >= iTarget ||
                     !Gia_ObjIsAndNotBuf(Gia_ManObj(p, iFan)) ||
                     Gia_ObjIsTravIdCurrentId(p, iFan) )
                    continue;
                pFan = Gia_ManObj( p, iFan );
                iFan0 = Gia_ObjFaninId0p( p, pFan );
                iFan1 = Gia_ObjFaninId1p( p, pFan );
                if ( !Gia_ObjIsTravIdCurrentId(p, iFan0) ||
                     !Gia_ObjIsTravIdCurrentId(p, iFan1) )
                    continue;
                // Additions are deliberately not marked, so suppress the
                // second encounter through the other fanin explicitly.
                if ( Vec_IntFind(vTfo, iFan) >= 0 )
                    continue;
                Vec_IntPush( vTfo, iFan );
                if ( pTfoStats )
                    pTfoStats->nAdded++;
                if ( Vec_IntSize(vTfo) >= nTfoLimit )
                {
                    if ( pTfoStats )
                        pTfoStats->fLimit = 1;
                    break;
                }
            }
            if ( Vec_IntSize(vTfo) >= nTfoLimit )
                break;
        }
        Vec_IntAppend( vPool, vTfo );
        if ( pTfoStats )
        {
            pTfoStats->nSeeds = nSeedSize;
            pTfoStats->Time = Abc_Clock() - clkTfo;
        }
    }
    Vec_IntFreeP( &vSeeds );
    Vec_IntFree( vFront );
    Vec_IntFree( vNext );
    return vPool;
}

static int Cec_TranCompleteFaninTfoSelfTest()
{
    Gia_Man_t * p = Gia_ManStart( 24 );
    Vec_Int_t * vMffc = Vec_IntAlloc( 16 );
    Vec_Int_t * vTfo = Vec_IntAlloc( 8 );
    Vec_Int_t * vPool;
    Cec_TranTfoStats_t Stats = {0};
    int iA = Gia_ManAppendCi( p );
    int iB = Gia_ManAppendCi( p );
    int iC = Gia_ManAppendCi( p );
    int iD = Gia_ManAppendCi( p );
    int iE = Gia_ManAppendCi( p );
    int iDeep = Gia_ManAppendAnd( p, iA, iD );
    int iT0 = Gia_ManAppendAnd( p, iDeep, iC );
    int iT1 = Gia_ManAppendAnd( p, iB, iC );
    int iSide = Gia_ManAppendAnd( p, iA, iB );
    int iNext = Gia_ManAppendAnd( p, iSide, iC );
    int iPartial = Gia_ManAppendAnd( p, iA, iE );
    int iRoot = Gia_ManAppendAnd( p, iT0, iT1 );
    char * pMark;
    Gia_ManAppendCo( p, iRoot );
    Gia_ManSetRegNum( p, 0 );
    Gia_ManCreateRefs( p );
    Gia_ManStaticFanoutStart( p );
    pMark = ABC_CALLOC( char, Gia_ManObjNum(p) );

    vPool = Cec_TranCollectDivPool( p, Abc_Lit2Var(iRoot), 0, 0, 0,
        NULL, NULL, pMark, vMffc, 1, 8, vTfo, &Stats );
    assert( Vec_IntFind(vTfo, Abc_Lit2Var(iSide)) >= 0 );
    assert( Vec_IntFind(vTfo, Abc_Lit2Var(iNext)) < 0 );
    assert( Vec_IntFind(vTfo, Abc_Lit2Var(iPartial)) < 0 );
    assert( Vec_IntFind(vTfo, Abc_Lit2Var(iRoot)) < 0 );
    Vec_IntFree( vPool );

    // A one-node legal reservoir fills before the deeper A fanin is visited.
    // TFO membership must nevertheless use the complete unlimited-depth TFI,
    // so the complete-fanin side node remains visible.
    vPool = Cec_TranCollectDivPool( p, Abc_Lit2Var(iRoot), 0, 1, 0,
        NULL, NULL, pMark, vMffc, 1, 8, vTfo, &Stats );
    assert( Vec_IntFind(vTfo, Abc_Lit2Var(iSide)) >= 0 );
    Vec_IntFree( vPool );

    Gia_ManStaticFanoutStop( p );
    ABC_FREE( pMark );
    Vec_IntFree( vMffc );
    Vec_IntFree( vTfo );
    ABC_FREE( p->pRefs );
    Gia_ManStop( p );
    return 1;
}

// Rank a physical divisor by the number of opposite-label simulation pairs
// it separates.  If O0/O1 and I0/I1 are the off/on-set counts in the two
// divisor cofactors, O0*I1 + O1*I0 is exactly the number of off/on pairs cut
// by this divisor.  The score is phase-independent and is therefore a cheap
// proxy for the reduction in the residual dependency ambiguity.
struct Cec_TranDivRank_t_
{
    word Score;
    int  CiOverlap;
    int  iPos;
};

// A paged iterator cursor is meaningful only for the exact ordered divisor
// set on which it was produced.  Freeze that set and its aligned rank metadata
// on page zero, then restore it verbatim before every continuation page.  This
// also keeps the root-batch teaching cache bound to the same object columns.
static void Cec_TranRootCursorBindBuildPool( Cec_TranRootCursor_t * pCursor,
    int iWave, Vec_Int_t * vPool, Cec_TranDivRank_t * pRanks )
{
    int i, nPool;
    if ( iWave == 0 )
    {
        assert( pCursor->vBuildPool == NULL );
        assert( pCursor->pBuildRanks == NULL );
        pCursor->vBuildPool = Vec_IntDup( vPool );
        nPool = Vec_IntSize( vPool );
        if ( nPool )
        {
            assert( pRanks != NULL );
            pCursor->pBuildRanks = ABC_ALLOC( Cec_TranDivRank_t, nPool );
            memcpy( pCursor->pBuildRanks, pRanks,
                sizeof(Cec_TranDivRank_t) * nPool );
        }
        return;
    }
    assert( pCursor->vBuildPool != NULL );
    nPool = Vec_IntSize( pCursor->vBuildPool );
    assert( nPool == 0 || (pRanks != NULL && pCursor->pBuildRanks != NULL) );
    Vec_IntClear( vPool );
    Vec_IntAppend( vPool, pCursor->vBuildPool );
    if ( nPool )
        memcpy( pRanks, pCursor->pBuildRanks,
            sizeof(Cec_TranDivRank_t) * nPool );
    for ( i = 0; i < nPool; i++ )
        assert( Vec_IntEntry(vPool, i) ==
                Vec_IntEntry(pCursor->vBuildPool, i) &&
                pRanks[i].iPos == i );
}

static void Cec_TranRootCursorStop( Cec_TranRootCursor_t * pCursor )
{
    Cec_TranRootCursorCacheStop( pCursor );
    Cec_TranTeachCacheStop( pCursor->pTeachCache );
    pCursor->pTeachCache = NULL;
    Vec_IntFreeP( &pCursor->vBuildPool );
    ABC_FREE( pCursor->pBuildRanks );
}

static int Cec_TranDivRankCompare( const void * p1, const void * p2 )
{
    Cec_TranDivRank_t const * pR1 = (Cec_TranDivRank_t const *)p1;
    Cec_TranDivRank_t const * pR2 = (Cec_TranDivRank_t const *)p2;
    if ( pR1->Score > pR2->Score )
        return -1;
    if ( pR1->Score < pR2->Score )
        return 1;
    if ( pR1->CiOverlap != pR2->CiOverlap )
        return pR2->CiOverlap - pR1->CiOverlap;
    return pR1->iPos - pR2->iPos;
}

static Cec_TranDivRank_t * Cec_TranRankDivReservoir( Cec_TranSim_t * pSim,
    int iTarget, Vec_Int_t * vReservoir, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, word const * pCare )
{
    Gia_Man_t * p = pSim->pGia;
    Cec_TranDivRank_t * pRanks = ABC_CALLOC( Cec_TranDivRank_t,
        Vec_IntSize(vReservoir) );
    word * pTarget = Cec_TranSimObj( pSim, iTarget );
    word * pDiv;
    word nOff0, nOff1, nOn0, nOn1, nOff = 0, nOn = 0;
    Vec_Int_t * vRootSupp = Vec_IntAlloc( 32 );
    Vec_Int_t * vDivSupp = Vec_IntAlloc( 32 );
    int i, k, s, iObj, RootNode = iTarget;
    int nRank = Vec_IntSize(vReservoir), nKeep = nRank;
    abctime clk = Abc_Clock();
    // Target marginals are shared by every divisor. The two zero-divisor
    // quadrants are exact complements of the one-divisor quadrants, including
    // masked care. Preserve the score and all ranking ties with half as many
    // per-divisor popcounts; no cross-root signature cache is needed.
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        word Care = pCare ? pCare[s] : ~(word)0;
        nOff += Abc_TtCountOnes( ~pTarget[s] & Care );
        nOn  += Abc_TtCountOnes(  pTarget[s] & Care );
    }
    Vec_IntForEachEntry( vReservoir, iObj, i )
    {
        pDiv = Cec_TranSimObj( pSim, iObj );
        nOff1 = nOn1 = 0;
        for ( s = 0; s < pSim->nSlots; s++ )
        {
            word Care = pCare ? pCare[s] : ~(word)0;
            nOff1 += Abc_TtCountOnes( ~pTarget[s] &  pDiv[s] & Care );
            nOn1  += Abc_TtCountOnes(  pTarget[s] &  pDiv[s] & Care );
        }
        nOff0 = nOff - nOff1;
        nOn0 = nOn - nOn1;
        pRanks[i].Score = nOff0 * nOn1 + nOff1 * nOn0;
        pRanks[i].iPos = i;
    }
    pProf->timeExpRankScore += Abc_Clock() - clk;
    clk = Abc_Clock();
    if ( pPars->nExplore & 1 )
    {
        if ( pSim->pCiCounts == NULL )
            pSim->pCiCounts = ABC_CALLOC( int, Gia_ManObjNum(p) );
        qsort( pRanks, nRank, sizeof(Cec_TranDivRank_t), Cec_TranDivRankCompare );
        if ( pPars->nConstrBaseMax && nKeep > pPars->nConstrBaseMax )
        {
            nKeep = pPars->nConstrBaseMax;
            while ( nKeep < nRank && pRanks[nKeep].Score == pRanks[nKeep-1].Score )
                nKeep++;
        }
    }
    if ( !(pPars->nExplore & 1) || (pPars->nExplore & 8) )
        Gia_ManCollectCis( p, &RootNode, 1, vRootSupp );
    for ( i = 0; i < nKeep; i++ )
    {
        iObj = Vec_IntEntry( vReservoir, pRanks[i].iPos );
        if ( (pPars->nExplore & 1) && pSim->pCiCounts[iObj] )
        {
            pRanks[i].CiOverlap = pSim->pCiCounts[iObj] - 1;
            pProf->nExpCiHit++;
            if ( !(pPars->nExplore & 8) )
                continue;
        }
        else
            pProf->nExpCiMiss++;
        Vec_IntClear( vDivSupp );
        Gia_ManCollectCis( p, &iObj, 1, vDivSupp );
        if ( pPars->nExplore & 1 )
        {
            // Every reservoir entry comes from this root's combinational TFI,
            // so its CI support is a subset of the root's CI support.
            pRanks[i].CiOverlap = Vec_IntSize( vDivSupp );
            pSim->pCiCounts[iObj] = pRanks[i].CiOverlap + 1;
            if ( pPars->nExplore & 8 )
                Vec_IntForEachEntry( vDivSupp, iObj, k )
                    assert( Vec_IntFind(vRootSupp, iObj) >= 0 );
        }
        else
        {
            pRanks[i].CiOverlap = 0;
            Vec_IntForEachEntry( vDivSupp, iObj, k )
                pRanks[i].CiOverlap += Vec_IntFind(vRootSupp, iObj) >= 0;
        }
    }
    pProf->timeExpRankCi += Abc_Clock() - clk;
    qsort( pRanks, Vec_IntSize(vReservoir),
        sizeof(Cec_TranDivRank_t), Cec_TranDivRankCompare );
    Vec_IntFree( vRootSupp );
    Vec_IntFree( vDivSupp );
    return pRanks;
}

// Ranking must choose the actual iterator input, not merely annotate an
// already-truncated BFS prefix.  Rewrite the reservoir in rank order and only
// then shrink it to B.  B=0 intentionally keeps the complete allowed TFI.
static int Cec_TranSelectRankedDivPool( Vec_Int_t * vReservoir,
    Cec_TranDivRank_t * pRanks, int nPoolMax, Vec_Int_t * vPinned )
{
    Vec_Int_t * vRanked;
    int i, nKeep = nPoolMax ?
        Abc_MinInt(nPoolMax, Vec_IntSize(vReservoir)) :
        Vec_IntSize(vReservoir);
    int nRescued = 0;
    // Normally the globally ranked prefix is the final Build pool.  A
    // root-local exact core may pin a few complementary nodes which would
    // otherwise fall below B.  Preserve the global order among all retained
    // nodes and keep the final pool size unchanged.
    if ( vPinned && nPoolMax && Vec_IntSize(vPinned) <= nKeep )
    {
        Cec_TranDivRank_t * pKept = ABC_ALLOC( Cec_TranDivRank_t, nKeep );
        char * pChosen = ABC_CALLOC( char, Vec_IntSize(vReservoir) );
        int k, iObj, iPos, nChosen = 0;
        Vec_IntForEachEntry( vPinned, iObj, i )
        {
            iPos = Vec_IntFind( vReservoir, iObj );
            if ( iPos < 0 || pChosen[iPos] )
                continue;
            pChosen[iPos] = 1;
            nChosen++;
            for ( k = 0; k < nKeep; k++ )
                if ( pRanks[k].iPos == iPos )
                    break;
            nRescued += k == nKeep;
        }
        if ( nRescued )
        {
            for ( i = 0; i < Vec_IntSize(vReservoir) && nChosen < nKeep; i++ )
                if ( !pChosen[pRanks[i].iPos] )
                    pChosen[pRanks[i].iPos] = 1, nChosen++;
            vRanked = Vec_IntAlloc( nKeep );
            for ( i = k = 0; i < Vec_IntSize(vReservoir); i++ )
                if ( pChosen[pRanks[i].iPos] )
                {
                    Vec_IntPush( vRanked, Vec_IntEntry(vReservoir,
                        pRanks[i].iPos) );
                    pKept[k] = pRanks[i];
                    pKept[k].iPos = k;
                    k++;
                }
            assert( k == nKeep );
            Vec_IntClear( vReservoir );
            Vec_IntAppend( vReservoir, vRanked );
            memcpy( pRanks, pKept, sizeof(Cec_TranDivRank_t) * nKeep );
            Vec_IntFree( vRanked );
            ABC_FREE( pChosen );
            ABC_FREE( pKept );
            return nRescued;
        }
        ABC_FREE( pChosen );
        ABC_FREE( pKept );
    }
    vRanked = Vec_IntAlloc( Vec_IntSize(vReservoir) );
    for ( i = 0; i < nKeep; i++ )
        Vec_IntPush( vRanked, Vec_IntEntry(vReservoir, pRanks[i].iPos) );
    Vec_IntClear( vReservoir );
    Vec_IntAppend( vReservoir, vRanked );
    // pRanks is already sorted in exactly the order copied into vReservoir.
    // Normalize its positions so the selected pool and its rank metadata can
    // be reused by constructed discovery without ranking the same divisors a
    // second time.
    for ( i = 0; i < nKeep; i++ )
        pRanks[i].iPos = i;
    Vec_IntFree( vRanked );
    return 0;
}
