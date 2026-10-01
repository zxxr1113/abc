// Build construction and root discovery.
// Private implementation fragment included only by cecTrans.c.

static void Cec_TranCexTranspose( word a[64] );

static void Cec_TranObservationRows( Cec_TranSim_t * pSim,
    Vec_Int_t * vPool, int iSlot, word * pRows, int nKeyWords )
{
    int k, d, b, nDivs = Vec_IntSize(vPool);
    for ( k = 0; k < nKeyWords; k++ )
    {
        word Matrix[64] = {0};
        for ( d = 0; d < 64 && 64*k + d < nDivs; d++ )
            Matrix[63-d] = Cec_TranSimObj(pSim,
                Vec_IntEntry(vPool, 64*k + d))[iSlot];
        Cec_TranCexTranspose( Matrix );
        for ( b = 0; b < 64; b++ )
            pRows[b*nKeyWords + k] = Matrix[63-b];
    }
}

static word Cec_TranResidualMix( word Value )
{
    Value ^= Value >> 30;
    Value *= ABC_CONST(0xbf58476d1ce4e5b9);
    Value ^= Value >> 27;
    Value *= ABC_CONST(0x94d049bb133111eb);
    return Value ^ (Value >> 31);
}

// Exact projection of shared observations, not a hash-only certificate.
// Keys use as many words as the physical divisor pool requires; the hash only
// chooses a probe position and every collision is resolved by full comparison.
static int Cec_TranObservationConflict( Cec_TranSim_t * pSim, int iTarget,
    Vec_Int_t * vPool, int * pnUnique )
{
    word * pRows;
    word Value, Hash;
    int k, b, s, h, Label, fConflict = 0;
    int nCap = 1, nDivs = Vec_IntSize(vPool);
    int nKeyWords = Abc_MaxInt( 1, (nDivs + 63) >> 6 );
    *pnUnique = 0;
    while ( nCap < 128 * pSim->nSlots )
        nCap <<= 1;
    if ( pSim->nObsCap < nCap || pSim->nObsKeyWords < nKeyWords )
    {
        pSim->nObsCap = Abc_MaxInt( pSim->nObsCap, nCap );
        pSim->nObsKeyWords = Abc_MaxInt(
            pSim->nObsKeyWords, nKeyWords );
        ABC_FREE( pSim->pObsKeys );
        ABC_FREE( pSim->pObsLabels );
        pSim->pObsKeys = ABC_ALLOC( word,
            (size_t)pSim->nObsCap * pSim->nObsKeyWords );
        pSim->pObsLabels = ABC_ALLOC( unsigned char, pSim->nObsCap );
    }
    memset( pSim->pObsLabels, 0, nCap );
    pRows = ABC_ALLOC( word, 64 * nKeyWords );
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        Cec_TranObservationRows( pSim, vPool, s, pRows, nKeyWords );
        Value = Cec_TranSimObj(pSim, iTarget)[s];
        for ( b = 0; b < 64; b++ )
        {
            word * pKey = pRows + b*nKeyWords;
            Label = 1 << ((Value >> b) & 1);
            Hash = Cec_TranResidualMix( pKey[0] );
            for ( k = 1; k < nKeyWords; k++ )
                Hash = Cec_TranResidualMix(Hash ^
                    Cec_TranResidualMix(pKey[k] + (word)k));
            h = (int)(Hash & (nCap - 1));
            while ( pSim->pObsLabels[h] &&
                    memcmp(pSim->pObsKeys + h*pSim->nObsKeyWords,
                        pKey, sizeof(word) * nKeyWords) )
                h = (h + 1) & (nCap - 1);
            if ( !(pSim->pObsLabels[h] & Label) )
                (*pnUnique)++;
            if ( pSim->pObsLabels[h] && !(pSim->pObsLabels[h] & Label) )
                fConflict = 1;
            memcpy( pSim->pObsKeys + h*pSim->nObsKeyWords,
                pKey, sizeof(word) * nKeyWords );
            pSim->pObsLabels[h] |= Label;
        }
    }
    ABC_FREE( pRows );
    return fConflict;
}

static int Cec_TranObservationSelfTest()
{
    Cec_TranSim_t Sim = {0};
    Vec_Int_t * vPool = Vec_IntAlloc( 65 );
    word Sims[66] = {0};
    int nUnique, i;
    Sim.nSlots = 1;
    Sim.pSims = Sims;
    Sims[0] = ABC_CONST(0x6666666666666666);
    Sims[1] = ABC_CONST(0xaaaaaaaaaaaaaaaa);
    Sims[2] = ABC_CONST(0xcccccccccccccccc);
    Vec_IntPush( vPool, 1 );
    assert( Cec_TranObservationConflict(&Sim, 0, vPool, &nUnique) == 1 );
    assert( nUnique == 4 );
    Vec_IntPush( vPool, 2 );
    assert( Cec_TranObservationConflict(&Sim, 0, vPool, &nUnique) == 0 );
    assert( nUnique == 4 );
    // The 64th divisor must participate in the exact key too.
    Vec_IntClear( vPool );
    for ( i = 1; i <= 64; i++ )
        Vec_IntPush( vPool, i );
    Sims[1] = Sims[2] = 0;
    Sims[64] = Sims[0];
    assert( Cec_TranObservationConflict(&Sim, 0, vPool, &nUnique) == 0 );
    assert( nUnique == 2 );
    // The 65th divisor lives in the second exact-key word.
    Sims[64] = 0;
    Vec_IntPush( vPool, 65 );
    Sims[65] = Sims[0];
    assert( Cec_TranObservationConflict(&Sim, 0, vPool, &nUnique) == 0 );
    assert( nUnique == 2 );
    Sims[65] = 0;
    assert( Cec_TranObservationConflict(&Sim, 0, vPool, &nUnique) == 1 );
    assert( nUnique == 2 );
    ABC_FREE( Sim.pObsKeys );
    ABC_FREE( Sim.pObsLabels );
    Vec_IntFree( vPool );
    // Independently check natural lane/divisor order, padding and multiple
    // words against scalar bit extraction, including empty and partial tiles.
    {
        Cec_TranSim_t Test = {0};
        Vec_Int_t * vTest = Vec_IntAlloc( 129 );
        word Data[130*3], Rows[64*3], State = 1;
        int n, s, b, k, d;
        Test.nSlots = 3;
        Test.pSims = Data;
        for ( i = 0; i < 130*3; i++ )
            Data[i] = State = Cec_TranResidualMix(State);
        for ( n = 0; n <= 129; n++ )
        {
            int nWords = Abc_MaxInt(1, (n+63)/64);
            if ( n ) Vec_IntPush(vTest, n);
            for ( s = 0; s < 3; s++ )
            {
                memset(Rows, 0xff, sizeof(Rows));
                Cec_TranObservationRows(&Test, vTest, s, Rows, nWords);
                for ( b = 0; b < 64; b++ )
                    for ( k = 0; k < nWords; k++ )
                    {
                        word Expected = 0;
                        for ( d = 0; d < 64 && 64*k+d < n; d++ )
                            Expected |= ((Data[(64*k+d+1)*3+s] >> b) & 1) << d;
                        assert(Rows[b*nWords+k] == Expected);
                    }
            }
        }
        Vec_IntFree(vTest);
    }
    return 1;
}

static int Cec_TranResidualSimBit( word const * pSim, int iSample )
{
    return (int)((pSim[iSample >> 6] >> (iSample & 63)) & 1);
}

static void Cec_TranResidualSampleInsert( int iSample, word Score,
    int * pSamples, word * pScores, int * pnSamples )
{
    int i, iWorst = 0;
    if ( *pnSamples < CEC_TRAN_BUILD_RESIDUAL_SAMPLE_VALUES )
    {
        pSamples[*pnSamples] = iSample;
        pScores[(*pnSamples)++] = Score;
        return;
    }
    for ( i = 1; i < *pnSamples; i++ )
        if ( pScores[i] > pScores[iWorst] ||
             (pScores[i] == pScores[iWorst] &&
              pSamples[i] > pSamples[iWorst]) )
            iWorst = i;
    if ( Score > pScores[iWorst] ||
         (Score == pScores[iWorst] && iSample >= pSamples[iWorst]) )
        return;
    pSamples[iWorst] = iSample;
    pScores[iWorst] = Score;
}

// Profiling-only counterfactual: compare the current static ranking prefix
// against conditional greedy selection from the complete pre-truncation
// reservoir.  At most 8 off and 8 on samples give an exact 64-bit residual
// pair mask.  Root sampling bounds overhead without changing discovery.
static void Cec_TranSuppProfResidualSample( Cec_TranSuppProf_t * p,
    Cec_TranSim_t * pSim, int iTarget, Vec_Int_t * vReservoir,
    Cec_TranDivRank_t const * pRanks, int nSupportMax )
{
    static int const Depth[CEC_TRAN_BUILD_RESIDUAL_DEPTH_BINS] = {
        1, 2, 4, 8, 16, 32 };
    int Off[CEC_TRAN_BUILD_RESIDUAL_SAMPLE_VALUES];
    int On[CEC_TRAN_BUILD_RESIDUAL_SAMPLE_VALUES];
    word OffScore[CEC_TRAN_BUILD_RESIDUAL_SAMPLE_VALUES];
    word OnScore[CEC_TRAN_BUILD_RESIDUAL_SAMPLE_VALUES];
    word * pCovers, Full, Covered, BestGainMask;
    char * pSelected;
    Vec_Int_t * vGreedy;
    word * pTarget, * pDiv;
    int nOff = 0, nOn = 0, nPairs, nReservoir, nSelect;
    int i, k, d, iRank, iObj, iBest, nBest, nStaticSize = 0;
    int nGreedySize = 0, iDepth;
    if ( p == NULL || Vec_IntSize(vReservoir) == 0 )
        return;
    assert( iTarget > 0 && iTarget < p->nObjs );
    if ( p->pRootResidualOffset[iTarget] != -3 )
        return;
    p->nResidualEligibleRoots++;
    if ( p->nResidualSampledRoots &&
         Cec_TranResidualMix((word)(unsigned)iTarget) %
            CEC_TRAN_BUILD_RESIDUAL_SAMPLE_RATE )
    {
        p->pRootResidualOffset[iTarget] = -2;
        return;
    }
    p->pRootResidualOffset[iTarget] = -1;
    p->nResidualSampledRoots++;
    pTarget = Cec_TranSimObj( pSim, iTarget );
    for ( i = 0; i < 64 * pSim->nSlots; i++ )
    {
        word Score = Cec_TranResidualMix(
            ((word)(unsigned)iTarget << 32) ^ (word)(unsigned)i );
        if ( Cec_TranResidualSimBit(pTarget, i) )
            Cec_TranResidualSampleInsert( i, Score,
                On, OnScore, &nOn );
        else
            Cec_TranResidualSampleInsert( i, Score,
                Off, OffScore, &nOff );
    }
    if ( nOff == 0 || nOn == 0 )
    {
        p->nResidualNoPairRoots++;
        return;
    }
    nPairs = nOff * nOn;
    Full = nPairs == 64 ? ~(word)0 : (((word)1 << nPairs) - 1);
    p->nResidualPairs += nPairs;
    nReservoir = Vec_IntSize( vReservoir );
    nSelect = Abc_MinInt( nReservoir, Abc_MinInt(nSupportMax, 32) );
    pCovers = ABC_CALLOC( word, nReservoir );
    pSelected = ABC_CALLOC( char, nReservoir );
    vGreedy = Vec_IntAlloc( nSelect );
    for ( iRank = 0; iRank < nReservoir; iRank++ )
    {
        iObj = Vec_IntEntry( vReservoir, pRanks[iRank].iPos );
        pDiv = Cec_TranSimObj( pSim, iObj );
        for ( i = 0; i < nOff; i++ )
            for ( k = 0; k < nOn; k++ )
                if ( Cec_TranResidualSimBit(pDiv, Off[i]) !=
                     Cec_TranResidualSimBit(pDiv, On[k]) )
                    pCovers[iRank] |= (word)1 << (i * nOn + k);
    }
    Covered = 0;
    iDepth = 0;
    for ( iRank = 0; iRank < nSelect; iRank++ )
    {
        Covered |= pCovers[iRank];
        while ( iDepth < CEC_TRAN_BUILD_RESIDUAL_DEPTH_BINS &&
                Depth[iDepth] == iRank + 1 )
            p->nResidualStaticCovered[iDepth++] +=
                Abc_TtCountOnes( Covered );
        if ( Covered == Full && nStaticSize == 0 )
            nStaticSize = iRank + 1;
    }
    while ( iDepth < CEC_TRAN_BUILD_RESIDUAL_DEPTH_BINS )
        p->nResidualStaticCovered[iDepth++] += Abc_TtCountOnes( Covered );
    Covered = 0;
    iDepth = 0;
    for ( d = 0; d < nSelect; d++ )
    {
        iBest = -1;
        nBest = 0;
        BestGainMask = 0;
        for ( iRank = 0; iRank < nReservoir; iRank++ )
            if ( !pSelected[iRank] )
            {
                word GainMask = pCovers[iRank] & ~Covered;
                int nGain = Abc_TtCountOnes( GainMask );
                if ( nGain > nBest )
                    iBest = iRank, nBest = nGain, BestGainMask = GainMask;
            }
        if ( iBest < 0 )
            break;
        pSelected[iBest] = 1;
        Covered |= BestGainMask;
        Vec_IntPush( vGreedy, Vec_IntEntry(vReservoir,
            pRanks[iBest].iPos) );
        while ( iDepth < CEC_TRAN_BUILD_RESIDUAL_DEPTH_BINS &&
                Depth[iDepth] == d + 1 )
            p->nResidualGreedyCovered[iDepth++] +=
                Abc_TtCountOnes( Covered );
        if ( Covered == Full )
        {
            nGreedySize = d + 1;
            break;
        }
    }
    while ( iDepth < CEC_TRAN_BUILD_RESIDUAL_DEPTH_BINS )
        p->nResidualGreedyCovered[iDepth++] += Abc_TtCountOnes( Covered );
    if ( nStaticSize )
    {
        p->nResidualStaticComplete++;
        p->nResidualStaticSizeSum += nStaticSize;
        p->nResidualStaticSize[
            Cec_TranSuppProfResidualSizeBin(nStaticSize)]++;
    }
    if ( nGreedySize )
    {
        p->nResidualGreedyComplete++;
        p->nResidualGreedySizeSum += nGreedySize;
        p->nResidualGreedySize[
            Cec_TranSuppProfResidualSizeBin(nGreedySize)]++;
        Vec_IntSort( vGreedy, 0 );
        p->pRootResidualOffset[iTarget] = Vec_IntSize(p->vResidualKeys);
        p->pRootResidualSize[iTarget] = Vec_IntSize(vGreedy);
        Vec_IntAppend( p->vResidualKeys, vGreedy );
    }
    Vec_IntFree( vGreedy );
    ABC_FREE( pCovers );
    ABC_FREE( pSelected );
}

// Select at most eight divisors that exactly separate every currently
// observed OFF sample from every ON sample.  Groups represent assignments to
// the already selected core which still contain both labels.  The next
// divisor maximizes the number of opposite-label pairs split inside these
// unresolved groups, retaining observation multiplicity and mixed-rank ties.
// A nonnegative return is an exact separator size; -1 means the bound was
// exhausted.  This remains a simulation feature, not a proof.
static int Cec_TranSelectCareObservedCoreExcept( Cec_TranSim_t * pSim,
    int iTarget, Vec_Int_t * vPool, int nCoreMax, Vec_Int_t * vCoreRanks,
    int iForbiddenRank, word const * pCare )
{
    int Totals[256][2] = {{0}}, NextTotals[256][2];
    int Slots[256] = {0}, NextSlots[256];
    long long Suffix[257];
    int nSlots = pSim->nSlots, nDivs = Vec_IntSize(vPool);
    int nGroups = 1, nCore = 0, nGroupsMax = 1 << nCoreMax;
    // Only indexed words of active groups are read. Initialization and
    // splitting write each indexed word before the group becomes active.
    word * pCurrent = ABC_ALLOC( word, 2 * nGroupsMax * nSlots );
    word * pNext = ABC_ALLOC( word, 2 * nGroupsMax * nSlots );
    int * pCurrentSlots = ABC_ALLOC( int, nGroupsMax * nSlots );
    int * pNextSlots = ABC_ALLOC( int, nGroupsMax * nSlots );
    char * pSelected = ABC_CALLOC( char, nDivs );
    word * pTarget = Cec_TranSimObj( pSim, iTarget );
    int g, i, j, k, s, iBest, nNextGroups;
    assert( nCoreMax > 0 && nCoreMax <= 8 );
    Vec_IntClear( vCoreRanks );
    for ( s = 0; s < nSlots; s++ )
    {
        pCurrent[s] = ~pTarget[s] & (pCare ? pCare[s] : ~(word)0);
        pCurrent[nSlots + s] = pTarget[s] & (pCare ? pCare[s] : ~(word)0);
        if ( pCurrent[s] | pCurrent[nSlots + s] )
            pCurrentSlots[Slots[0]++] = s;
        Totals[0][0] += Abc_TtCountOnes( pCurrent[s] );
        Totals[0][1] += Abc_TtCountOnes( pCurrent[nSlots + s] );
    }
    if ( Totals[0][0] == 0 || Totals[0][1] == 0 )
        nGroups = 0;
    while ( nGroups && nCore < nCoreMax )
    {
        long long BestScore = 0, MaxScore = 0;
        Suffix[nGroups] = 0;
        for ( g = nGroups - 1; g >= 0; g-- )
            Suffix[g] = Suffix[g+1] + (long long)Totals[g][0] * Totals[g][1];
        MaxScore = Suffix[0];
        iBest = -1;
        for ( i = 0; i < nDivs; i++ )
            if ( i != iForbiddenRank && !pSelected[i] )
            {
                long long Score = 0;
                word * pDiv = Cec_TranSimObj( pSim,
                    Vec_IntEntry(vPool, i) );
                for ( g = 0; g < nGroups; g++ )
                {
                    int nOff1 = 0, nOn1 = 0;
                    // Even separating all remaining opposite-label pairs
                    // cannot beat the earlier rank; preserve first-rank ties.
                    if ( Score + Suffix[g] <= BestScore ) break;
                    // Inactive words contain no OFF/ON observations and
                    // contribute exactly zero to every divisor's score.
                    for ( j = 0; j < Slots[g]; j++ )
                    {
                        s = pCurrentSlots[g*nSlots + j];
                        nOff1 += Abc_TtCountOnes(
                            pCurrent[(2*g)*nSlots + s] & pDiv[s] );
                        nOn1 += Abc_TtCountOnes(
                            pCurrent[(2*g+1)*nSlots + s] & pDiv[s] );
                    }
                    Score += (long long)nOff1 *
                        (Totals[g][1] - nOn1) +
                        (long long)nOn1 * (Totals[g][0] - nOff1);
                }
                if ( Score > BestScore )
                    iBest = i, BestScore = Score;
                // All unresolved opposite-label pairs are separated. Later
                // ranks cannot improve this score, including its stable tie.
                if ( BestScore == MaxScore )
                    break;
            }
        if ( iBest < 0 )
            break;
        pSelected[iBest] = 1;
        Vec_IntPush( vCoreRanks, iBest );
        nCore++;
        if ( BestScore == MaxScore )
        {
            nGroups = 0;
            break;
        }
        // Preserve the selected partial core on failure without materializing
        // a partition that cannot be examined after the core bound is reached.
        if ( nCore == nCoreMax )
            break;
        nNextGroups = 0;
        for ( g = 0; g < nGroups; g++ )
            for ( k = 0; k < 2; k++ )
            {
                int nOff = 0, nOn = 0, nActive = 0;
                word * pDiv = Cec_TranSimObj( pSim,
                    Vec_IntEntry(vPool, iBest) );
                for ( j = 0; j < Slots[g]; j++ )
                {
                    s = pCurrentSlots[g*nSlots + j];
                    word Phase = k ? pDiv[s] : ~pDiv[s];
                    word Off = pCurrent[(2*g)*nSlots + s] & Phase;
                    word On = pCurrent[(2*g+1)*nSlots + s] & Phase;
                    if ( Off | On )
                    {
                        pNextSlots[nNextGroups*nSlots + nActive++] = s;
                        pNext[(2*nNextGroups)*nSlots + s] = Off;
                        pNext[(2*nNextGroups+1)*nSlots + s] = On;
                        nOff += Abc_TtCountOnes( Off );
                        nOn += Abc_TtCountOnes( On );
                    }
                }
                if ( nOff && nOn )
                {
                    NextTotals[nNextGroups][0] = nOff;
                    NextTotals[nNextGroups][1] = nOn;
                    NextSlots[nNextGroups] = nActive;
                    nNextGroups++;
                    assert( nNextGroups <= nGroupsMax );
                }
            }
        {
            word * pTemp = pCurrent;
            int * pTempSlots = pCurrentSlots;
            pCurrent = pNext;
            pNext = pTemp;
            pCurrentSlots = pNextSlots;
            pNextSlots = pTempSlots;
        }
        memcpy( Totals, NextTotals, sizeof(Totals[0]) * nNextGroups );
        memcpy( Slots, NextSlots, sizeof(Slots[0]) * nNextGroups );
        nGroups = nNextGroups;
    }
    ABC_FREE( pSelected );
    ABC_FREE( pNextSlots );
    ABC_FREE( pCurrentSlots );
    ABC_FREE( pNext );
    ABC_FREE( pCurrent );
    return nGroups ? -1 : nCore;
}

static int Cec_TranSelectExactObservedCoreExcept( Cec_TranSim_t * pSim,
    int iTarget, Vec_Int_t * vPool, int nCoreMax, Vec_Int_t * vCoreRanks,
    int iForbiddenRank )
{
    return Cec_TranSelectCareObservedCoreExcept(pSim, iTarget, vPool,
        nCoreMax, vCoreRanks, iForbiddenRank, NULL);
}

static int Cec_TranSelectExactObservedCore( Cec_TranSim_t * pSim,
    int iTarget, Vec_Int_t * vPool, int nCoreMax, Vec_Int_t * vCoreRanks )
{
    return Cec_TranSelectExactObservedCoreExcept( pSim, iTarget, vPool,
        nCoreMax, vCoreRanks, -1 );
}

static int Cec_TranExactCoreSelfTest()
{
    Cec_TranSim_t Sim = {0};
    Vec_Int_t * vPool = Vec_IntAlloc( 2 );
    Vec_Int_t * vCore = Vec_IntAlloc( 2 );
    word Sims[3] = {0};
    Sim.nSlots = 1;
    Sim.pSims = Sims;
    Sims[0] = ABC_CONST(0xcccccccccccccccc);
    Sims[1] = Sims[0];
    Sims[2] = ~Sims[0];
    Vec_IntPush( vPool, 1 );
    Vec_IntPush( vPool, 2 );
    assert( Cec_TranSelectExactObservedCore(
        &Sim, 0, vPool, 2, vCore) == 1 );
    assert( Vec_IntSize(vCore) == 1 && Vec_IntEntry(vCore, 0) == 0 );
    assert( Cec_TranSelectExactObservedCoreExcept(
        &Sim, 0, vPool, 2, vCore, 0) == 1 );
    assert( Vec_IntSize(vCore) == 1 && Vec_IntEntry(vCore, 0) == 1 );
    assert( Cec_TranSelectExactObservedCoreExcept(
        &Sim, 0, vPool, 2, vCore, 1) == 1 );
    assert( Vec_IntSize(vCore) == 1 && Vec_IntEntry(vCore, 0) == 0 );
    Vec_IntFree( vCore );
    Vec_IntFree( vPool );
    return 1;
}

static int Cec_TranKitEdgeToRecipeCode( Kit_Edge_t Edge,
    Vec_Int_t * vPool, Vec_Int_t * vCoreRanks, int nLeaves )
{
    if ( Edge.Node < (unsigned)nLeaves )
        return Abc_Var2Lit( Vec_IntEntry(vPool,
            Vec_IntEntry(vCoreRanks, Edge.Node)), Edge.fCompl );
    return Cec_TranRecipeGateCode( Edge.Node - nLeaves, Edge.fCompl );
}

// BDC's resub vector uses literals 0/1 for constants, variables 2..n+1 for
// the selected core, and subsequent variables for newly created AND gates.
static int Cec_TranBdcLitToRecipeCode( int Lit, Vec_Int_t * vPool,
    Vec_Int_t * vCoreRanks, int nLeaves )
{
    int iVar = Abc_Lit2Var( Lit );
    if ( iVar < 2 )
        return Lit;
    if ( iVar < nLeaves + 2 )
        return Abc_Var2Lit( Vec_IntEntry(vPool,
            Vec_IntEntry(vCoreRanks, iVar - 2)), Abc_LitIsCompl(Lit) );
    return Cec_TranRecipeGateCode( iVar - (nLeaves + 2),
        Abc_LitIsCompl(Lit) );
}

// Project the current observations onto one exact core.  Kit and BDC consume
// the same deterministic core and the same projected ISF, so compute it once
// per root instead of repeating both operations for each portfolio member.
static void Cec_TranProjectRootIsfCareRaw( Cec_TranSim_t * pSim,
    Cec_TranRoot_t const * pRoot, Vec_Int_t * vPool,
    Vec_Int_t * vCoreRanks, int nCore, unsigned * pOff, unsigned * pOn,
    word const * pCare )
{
    unsigned char Labels[256] = {0};
    word * pTarget = Cec_TranSimObj( pSim, pRoot->iObj );
    int nBits, i, s, Value, Label;
    assert( nCore > 0 && nCore <= 8 );
    for ( s = 0; s < 64 * pSim->nSlots; s++ )
    {
        if ( pCare && !Cec_TranResidualSimBit((word *)pCare, s) )
            continue;
        Value = 0;
        for ( i = 0; i < nCore; i++ )
            Value |= Cec_TranResidualSimBit(Cec_TranSimObj(pSim,
                Vec_IntEntry(vPool, Vec_IntEntry(vCoreRanks, i))), s) << i;
        Label = Cec_TranResidualSimBit( pTarget, s ) ? 2 : 1;
        Labels[Value] |= Label;
        assert( Labels[Value] != 3 );
    }
    nBits = nCore < 5 ? 32 : 1 << nCore;
    for ( Value = 0; Value < nBits; Value++ )
    {
        Label = Labels[Value % (1 << nCore)];
        if ( Label == 1 )
            pOff[Value >> 5] |= 1u << (Value & 31);
        else if ( Label == 2 )
            pOn[Value >> 5] |= 1u << (Value & 31);
    }
}

static void Cec_TranProjectRootIsfRaw( Cec_TranSim_t * pSim,
    Cec_TranRoot_t const * pRoot, Vec_Int_t * vPool,
    Vec_Int_t * vCoreRanks, int nCore, unsigned * pOff, unsigned * pOn )
{
    Cec_TranProjectRootIsfCareRaw(pSim, pRoot, vPool, vCoreRanks,
        nCore, pOff, pOn, NULL);
}

static int Cec_TranCareIsfSelfTest()
{
    Cec_TranSim_t Sim = {0};
    Cec_TranRoot_t Root = {0};
    Vec_Int_t * vPool = Vec_IntAlloc(2), * vCore = Vec_IntAlloc(2);
    word Sims[3] = {0}, Care;
    unsigned Off[8] = {0}, On[8] = {0};
    int a;
    Sim.nSlots = 1; Sim.pSims = Sims; Root.iObj = 0;
    Sims[1] = ABC_CONST(0xaaaaaaaaaaaaaaaa);
    Sims[2] = ABC_CONST(0xcccccccccccccccc);
    Sims[0] = Sims[1] ^ Sims[2];
    Vec_IntPush(vPool, 1); Vec_IntPush(vPool, 2);
    assert(Cec_TranSelectExactObservedCore(&Sim, 0, vPool, 1, vCore) == -1);
    Care = ~Sims[2];
    assert(Cec_TranSelectCareObservedCoreExcept(&Sim, 0, vPool, 1,
        vCore, -1, &Care) == 1);
    assert(Vec_IntEntry(vCore, 0) == 0);
    Cec_TranProjectRootIsfCareRaw(&Sim, &Root, vPool, vCore, 1, Off, On, &Care);
    assert(Off[0] == 0x55555555u && On[0] == 0xaaaaaaaau);
    Care = ~(word)0;
    assert(Cec_TranSelectCareObservedCoreExcept(&Sim, 0, vPool, 1,
        vCore, -1, &Care) == -1);
    // Exhaust every care mask of this complete two-input truth table.
    for ( a = 0; a < 16; a++ )
    {
        int i, nCore;
        Care = 0;
        for ( i = 0; i < 64; i++ )
            if ( a & (1 << (i % 4)) ) Care |= (word)1 << i;
        nCore = Cec_TranSelectCareObservedCoreExcept(&Sim, 0, vPool, 2,
            vCore, -1, &Care);
        assert(nCore >= 0);
        if ( nCore > 0 )
        {
            memset(Off, 0, sizeof(Off)); memset(On, 0, sizeof(On));
            Cec_TranProjectRootIsfCareRaw(&Sim, &Root, vPool, vCore,
                nCore, Off, On, &Care);
            assert(!(Off[0] & On[0]));
            for ( i = 0; i < 64; i++ ) if ( (Care >> i) & 1 )
            {
                int j, v = 0;
                for ( j = 0; j < nCore; j++ )
                    v |= ((Sims[Vec_IntEntry(vPool, Vec_IntEntry(vCore, j))] >> i) & 1) << j;
                assert(((Sims[0] >> i) & 1) ? ((On[0] >> v) & 1) : ((Off[0] >> v) & 1));
            }
        }
    }
    Vec_IntFree(vCore); Vec_IntFree(vPool);
    Abc_Print(1, "stran care-aware ISF/core mask regression: PASS\n");
    return 1;
}

static void Cec_TranProjectRootIsf( Cec_TranSim_t * pSim,
    Cec_TranRoot_t const * pRoot, Vec_Int_t * vPool,
    Vec_Int_t * vCoreRanks, int nCore, unsigned * pOff, unsigned * pOn,
    Cec_TranProf_t * pProf )
{
    abctime clk = Abc_Clock();
    Cec_TranProjectRootIsfRaw( pSim, pRoot, vPool, vCoreRanks,
        nCore, pOff, pOn );
    pProf->timeRootIsfProjection += Abc_Clock() - clk;
}

// Return the smaller valid Kit/BDC gate count for one exact observed core.
// This is a construction-value query only; no candidate or proof is created.
static int Cec_TranRootIsfGateCost( Cec_TranSim_t * pSim,
    Cec_ParTran_t * pPars, Cec_TranRoot_t const * pRoot,
    Vec_Int_t * vPool, Vec_Int_t * vCoreRanks, int nCore )
{
    unsigned Off[8] = {0}, On[8] = {0}, Care[8] = {0};
    Vec_Int_t * vMemory = Vec_IntAlloc( 0 );
    Vec_Int_t * vBdc = NULL;
    Kit_Graph_t * pGraph;
    int i, nGates, nLimit = Abc_MinInt(
        pPars->nDepNodesMax, pRoot->nMffc - 1 );
    int Best = 0x3fffffff;
    Cec_TranProjectRootIsfRaw( pSim, pRoot, vPool, vCoreRanks,
        nCore, Off, On );
    pGraph = Kit_TruthToGraph2( Off, On, nCore, vMemory );
    if ( pGraph && !Kit_GraphIsConst(pGraph) && !Kit_GraphIsVar(pGraph) )
    {
        nGates = Kit_GraphNodeNum( pGraph );
        if ( nGates > 0 && nGates <= nLimit &&
             nGates <= CEC_TRAN_RECIPE_NODES_MAX )
            Best = nGates;
    }
    if ( pGraph )
        Kit_GraphFree( pGraph );
    // No valid construction can beat one gate, so BDC cannot improve this
    // value query after Kit has already reached the realizable lower bound.
    if ( Best == 1 )
    {
        Vec_IntFree( vMemory );
        return Best;
    }
    if ( pPars->fBdcPortfolio && nCore >= 2 )
    {
        for ( i = 0; i < 8; i++ )
            Care[i] = Off[i] | On[i];
        vBdc = Bdc_ManBidecResub( (word *)On, (word *)Care, nCore );
        if ( vBdc && Vec_IntSize(vBdc) >= 3 &&
             (Vec_IntSize(vBdc) & 1) )
        {
            nGates = (Vec_IntSize(vBdc) - 1) / 2;
            if ( nGates > 0 && nGates <= nLimit &&
                 nGates <= CEC_TRAN_RECIPE_NODES_MAX )
                Best = Abc_MinInt( Best, nGates );
        }
    }
    Vec_IntFreeP( &vBdc );
    Vec_IntFree( vMemory );
    return Best;
}

// Add one care-aware Kit or BDC factorization as an extra portfolio member.
// Native Build runs first and keeps its complete q budget; this candidate never
// displaces a baseline construction slot.  The projected ISF is accepted only
// when the selected core is an exact separator of every current observation,
// the exported graph fits the unchanged positive-gain bound, and independent
// full-observation recipe simulation succeeds.  Formal proof and commit are
// unchanged downstream.
static void Cec_TranCollectRootIsfCandidate( Cec_TranSim_t * pSim,
    Cec_ParTran_t * pPars, Cec_TranRoot_t const * pRoot,
    Vec_Int_t * vPool, Cec_TranDivRank_t const * pRanks,
    Cec_TranCandVec_t const * pKnown, Cec_TranCandVec_t const * pExist,
    Cec_TranCandVec_t * pBuild, Cec_TranProf_t * pProf,
    Vec_Int_t * vCoreRanks, int nCore, unsigned const * pOff,
    unsigned const * pOn, int fBdc, word * pCare )
{
    unsigned Off[8] = {0}, On[8] = {0}, Care[8] = {0};
    Vec_Int_t * vMemory = NULL;
    Vec_Int_t * vBdc = NULL;
    Kit_Graph_t * pGraph = NULL;
    Cec_TranCand_t Cand;
    int nGates, nLimit, i, Code;
    abctime clk;
    if ( fBdc )
        pProf->nRootBdcCoreCalls++;
    else
        pProf->nRootKitCoreCalls++;
    if ( nCore <= 0 || (fBdc && nCore < 2) )
        goto cleanup;
    assert( Vec_IntSize(vCoreRanks) >= nCore );
    if ( fBdc )
        pProf->nRootBdcCoreSeparated++;
    else
        pProf->nRootKitCoreSeparated++;
    memcpy( Off, pOff, sizeof(Off) );
    memcpy( On, pOn, sizeof(On) );
    if ( fBdc )
    {
        for ( i = 0; i < 8; i++ )
            Care[i] = Off[i] | On[i];
        clk = Abc_Clock();
        vBdc = Bdc_ManBidecResub( (word *)On, (word *)Care, nCore );
        pProf->timeRootBdcSynthesis += Abc_Clock() - clk;
        if ( vBdc == NULL || Vec_IntSize(vBdc) < 3 ||
             !(Vec_IntSize(vBdc) & 1) )
            goto cleanup;
        nGates = (Vec_IntSize(vBdc) - 1) / 2;
    }
    else
    {
        vMemory = Vec_IntAlloc( 0 );
        clk = Abc_Clock();
        pGraph = Kit_TruthToGraph2( Off, On, nCore, vMemory );
        pProf->timeRootKitSynthesis += Abc_Clock() - clk;
        if ( pGraph == NULL || Kit_GraphIsConst(pGraph) ||
             Kit_GraphIsVar(pGraph) )
            goto cleanup;
        assert( pGraph->nLeaves == nCore );
        nGates = Kit_GraphNodeNum( pGraph );
    }
    nLimit = Abc_MinInt( pPars->nDepNodesMax, pRoot->nMffc - 1 );
    if ( nGates <= 0 || nGates > nLimit ||
         nGates > CEC_TRAN_RECIPE_NODES_MAX )
        goto cleanup;
    memset( &Cand, 0, sizeof(Cand) );
    Cand.iTarget = pRoot->iObj;
    Cand.iDiv0 = Cand.iDiv1 = -1;
    Cand.nMffc = pRoot->nMffc;
    Cand.nGates = nGates;
    Cand.Recipe = Cec_TranRecipeAlloc( 2 * nGates );
    if ( fBdc )
    {
        for ( i = 0; i < 2 * nGates; i++ )
            Cand.Recipe[i] = Cec_TranBdcLitToRecipeCode(
                Vec_IntEntry(vBdc, i), vPool, vCoreRanks, nCore );
        Cand.iOut = Cec_TranBdcLitToRecipeCode(
            Vec_IntEntryLast(vBdc), vPool, vCoreRanks, nCore );
    }
    else
    {
        for ( i = 0; i < nGates; i++ )
        {
            Kit_Node_t const * pNode = pGraph->pNodes + nCore + i;
            Cand.Recipe[2*i] = Cec_TranKitEdgeToRecipeCode( pNode->eEdge0,
                vPool, vCoreRanks, nCore );
            Cand.Recipe[2*i+1] = Cec_TranKitEdgeToRecipeCode( pNode->eEdge1,
                vPool, vCoreRanks, nCore );
        }
        Cand.iOut = Cec_TranKitEdgeToRecipeCode( pGraph->eRoot,
            vPool, vCoreRanks, nCore );
    }
    Cand.nKind = CEC_TRAN_CAND_CONSTR;
    Cand.fStrict = pCare == NULL;
    Cand.fKitPortfolio = !fBdc;
    Cand.fBdcPortfolio = fBdc;
    Cand.fExactTemplate = 0;
    Cand.nResubStage = 2;
    Cand.nResubRank = 0x3fffffff;
    Cand.nDiagDiscoveryMffc = pRoot->nMffc;
    Cand.nDiagDiscoveryPhase = pProf->DiagPhase;
    Cec_TranCandCanonicalizeRecipe( &Cand );
    if ( Cand.nGates <= 0 || Cand.nGates > nLimit ||
         !Cec_TranRecipeStructurallyValid(pSim, &Cand) ||
         !Cec_TranRecipeMatchesRoot(pSim, &Cand, pCare) )
    {
        Cec_TranCandRecipeRelease( &Cand );
        goto cleanup;
    }
    Cand.Gain = Cand.nMffc - Cand.nGates;
    Cand.nDiscoveryGain = Cand.Gain;
    if ( fBdc )
        pProf->nRootBdcSynthesized++;
    else
        pProf->nRootKitSynthesized++;
    for ( i = 0; i < nCore; i++ )
    {
        int iRank = Vec_IntEntry( vCoreRanks, i );
        Cand.nCiOverlap += pRanks[iRank].CiOverlap;
        Cand.nDivRankMax = Abc_MaxInt( Cand.nDivRankMax, iRank + 1 );
        Cand.nDivRankSum += iRank + 1;
    }
    for ( i = -1; i < 2 * Cand.nGates; i++ )
    {
        Code = i < 0 ? Cand.iOut : Cand.Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) || Abc_Lit2Var(Code) == 0 )
            continue;
        if ( Cand.iDiv0 == -1 )
            Cand.iDiv0 = Code;
        else if ( Abc_Lit2Var(Cand.iDiv0) != Abc_Lit2Var(Code) )
        {
            Cand.iDiv1 = Code;
            break;
        }
    }
    if ( !Cec_TranCandVecContains(pKnown, &Cand) &&
         !Cec_TranCandVecContains(pExist, &Cand) &&
         !Cec_TranCandVecContains(pBuild, &Cand) )
    {
        Cec_TranCandVecPush( pBuild, Cand );
        if ( fBdc )
            pProf->nRootBdcAccepted++;
        else
            pProf->nRootKitAccepted++;
    }
    Cec_TranCandRecipeRelease( &Cand );
cleanup:
    if ( pGraph )
        Kit_GraphFree( pGraph );
    Vec_IntFreeP( &vBdc );
    Vec_IntFreeP( &vMemory );
}

// A zero-gate existing replacement does not need the resub cover engine.
// Scan all structural routes for an exact full-signature match and return the
// first local/diverse/global divisor (including complemented phase).  This is
// both broader than selecting 2B first and much cheaper than initializing the
// unate/pair machinery for a direct literal answer.
// Pool zero is byte-for-byte the former BFS prefix, preserving the strong
// first candidate.  Pools one through three first draw from boundary, local,
// and global routes respectively.  Later pools mix all unused routes.  Every
// alternate keeps a small set of informative BFS anchors so the dependency
// engine can combine new information with strong local divisors.
static int Cec_TranRecipeCodeFromResub( int iLit, int nVars,
    Vec_Int_t * vPool )
{
    int iVar = Abc_Lit2Var( iLit );
    if ( iVar == 0 )
        return Abc_LitIsCompl( iLit );
    if ( iVar < nVars )
    {
        assert( iVar >= 2 && iVar - 2 < Vec_IntSize(vPool) );
        return Abc_Var2Lit( Vec_IntEntry(vPool, iVar - 2),
            Abc_LitIsCompl(iLit) );
    }
    return Cec_TranRecipeGateCode( iVar - nVars, Abc_LitIsCompl(iLit) );
}

typedef struct Cec_TranDepScratch_t_ Cec_TranDepScratch_t;
struct Cec_TranDepScratch_t_
{
    Vec_Ptr_t * vDivs;
    Vec_Wec_t * vRecipes;
    word *      pOff;
    word *      pOn;
    int         nAttemptsLast;
    abctime     timeInitLast;
    abctime     timeSearchLast;
    abctime *   timeAttemptLast;
    int *       fAttemptUniqueLast;
    int         nAttemptCap;
};

static void Cec_TranDepScratchStart( Cec_TranDepScratch_t * p,
    int nSlots, int nDivsMax, int nChoices )
{
    p->vDivs = Vec_PtrAlloc( nDivsMax + 2 );
    p->vRecipes = Vec_WecAlloc( nChoices );
    p->pOff = ABC_ALLOC( word, nSlots );
    p->pOn  = ABC_ALLOC( word, nSlots );
    p->nAttemptsLast = 0;
    p->timeInitLast = p->timeSearchLast = 0;
    p->nAttemptCap = nChoices;
    p->timeAttemptLast = ABC_CALLOC( abctime, nChoices );
    p->fAttemptUniqueLast = ABC_CALLOC( int, nChoices );
}

static void Cec_TranDepScratchStop( Cec_TranDepScratch_t * p )
{
    Vec_PtrFree( p->vDivs );
    Vec_WecFree( p->vRecipes );
    ABC_FREE( p->pOff );
    ABC_FREE( p->pOn );
    ABC_FREE( p->timeAttemptLast );
    ABC_FREE( p->fAttemptUniqueLast );
}

static int Cec_TranCandFromDependency( Cec_TranSim_t * pSim,
    Cec_TranRoot_t const * pRoot, Vec_Int_t * vPool, word * pCare,
    int fStrict, Vec_Ptr_t * vDivs, Vec_Int_t * vRecipe,
    Cec_TranCand_t * pCand )
{
    int RawRecipe[2 * CEC_TRAN_RECIPE_NODES_MAX];
    int i, Code, RawOut, RawKind, RawGates;
    int nArray = Vec_IntSize(vRecipe);
    int nVars = Vec_PtrSize(vDivs);
    memset( pCand, 0, sizeof(*pCand) );
    pCand->iTarget = pRoot->iObj;
    pCand->nMffc = pRoot->nMffc;
    pCand->Gain = -1;
    pCand->fStrict = fStrict;
    pCand->nGates = nArray / 2;
    assert( pCand->nGates <= CEC_TRAN_RECIPE_NODES_MAX );
    if ( pCand->nGates )
        pCand->Recipe = Cec_TranRecipeAlloc( 2 * pCand->nGates );
    for ( i = 0; i < 2 * pCand->nGates; i++ )
        pCand->Recipe[i] = Cec_TranRecipeCodeFromResub(
            Vec_IntEntry(vRecipe, i), nVars, vPool );
    pCand->iOut = Cec_TranRecipeCodeFromResub(
        Vec_IntEntryLast(vRecipe), nVars, vPool );
    pCand->nKind = pCand->nGates ? CEC_TRAN_CAND_CONSTR :
        (Abc_Lit2Var(pCand->iOut) == 0 ?
            CEC_TRAN_CAND_CONST : CEC_TRAN_CAND_EXIST);
    if ( !Cec_TranRecipeStructurallyValid(pSim, pCand) )
    {
        Cec_TranCandRecipeRelease( pCand );
        memset( pCand, 0, sizeof(*pCand) );
        return 0;
    }
    RawGates = pCand->nGates;
    RawOut = pCand->iOut;
    RawKind = pCand->nKind;
    if ( RawGates )
        memcpy( RawRecipe, pCand->Recipe, sizeof(int) * 2 * RawGates );
    Cec_TranCandCanonicalizeRecipe( pCand );
    // Canonicalization is an optimization, never a semantic pruning rule.
    // If a future identity/compaction change alters the function, restore
    // and audit the raw recipe before deciding whether to reject it.
    if ( !Cec_TranRecipeStructurallyValid(pSim, pCand) ||
         !Cec_TranRecipeMatchesRoot(pSim, pCand, pCare) )
    {
        Cec_TranCandRecipeRelease( pCand );
        pCand->nGates = RawGates;
        pCand->iOut = RawOut;
        pCand->nKind = RawKind;
        if ( RawGates )
        {
            pCand->Recipe = Cec_TranRecipeAlloc( 2 * RawGates );
            memcpy( pCand->Recipe, RawRecipe,
                sizeof(int) * 2 * RawGates );
        }
        if ( !Cec_TranRecipeStructurallyValid(pSim, pCand) ||
             !Cec_TranRecipeMatchesRoot(pSim, pCand, pCare) )
        {
            Cec_TranCandRecipeRelease( pCand );
            memset( pCand, 0, sizeof(*pCand) );
            return 0;
        }
    }
    pCand->iDiv0 = pCand->iDiv1 = -1;
    for ( i = -1; i < 2 * pCand->nGates; i++ )
    {
        Code = i < 0 ? pCand->iOut : pCand->Recipe[i];
        if ( Cec_TranRecipeCodeIsGate(Code) || Abc_Lit2Var(Code) == 0 )
            continue;
        if ( pCand->iDiv0 == -1 )
            pCand->iDiv0 = Code;
        else if ( Abc_Lit2Var(pCand->iDiv0) != Abc_Lit2Var(Code) )
        {
            pCand->iDiv1 = Code;
            break;
        }
    }
    return 1;
}

// -1 preserves the ordinary positive raw-gate bound.  An explicit nonnegative
// budget is for callers which separately price the recipe in the frozen DAG:
// raw gates may then exceed MFFC-1 because some gates already exist.  The
// user's N limit still applies, and malformed negative overrides fail closed.
static int Cec_TranDependencyGateLimit( Cec_ParTran_t const * pPars,
    Cec_TranRoot_t const * pRoot, int nRawBudget )
{
    if ( !pPars->fUseConstr || nRawBudget < -1 )
        return 0;
    return Abc_MinInt( pPars->nDepNodesMax,
        nRawBudget == -1 ? pRoot->nMffc - 1 : nRawBudget );
}

static void * Cec_TranDependencyIteratorStartWithRawBudget( Cec_TranSim_t * pSim,
    Cec_ParTran_t * pPars, Cec_TranRoot_t const * pRoot,
    Vec_Int_t * vPool, word * pCare, Cec_TranDepScratch_t * pScratch,
    int * pCursor, void ** ppRootCache, int nRawBudget )
{
    Vec_Ptr_t * vDivs = pScratch->vDivs;
    word Target, Care;
    int s, i, iObj, nLimit;
    Vec_PtrClear( vDivs );
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        Target = Cec_TranSimLit( pSim,
            Abc_Var2Lit(pRoot->iObj, 0), s );
        Care = pCare ? pCare[s] : ~(word)0;
        pScratch->pOff[s] = ~Target & Care;
        pScratch->pOn[s]  =  Target & Care;
    }
    Vec_PtrPushTwo( vDivs, pScratch->pOff, pScratch->pOn );
    Vec_IntForEachEntry( vPool, iObj, i )
        Vec_PtrPush( vDivs, Cec_TranSimObj(pSim, iObj) );
    // Ordinary callers retain the original syntactic positive-gain budget.
    // Cost-aware callers may explicitly widen it, without changing the real
    // MFFC or granting any proof/commit authority to the constructed recipe.
    nLimit = Cec_TranDependencyGateLimit( pPars, pRoot, nRawBudget );
    return Abc_ResubIteratorResumeStart( Vec_PtrArray(vDivs),
        Vec_PtrSize(vDivs), pSim->nSlots, nLimit, Vec_IntSize(vPool),
        0, 0, pPars->fUseSolvSched, pPars->nStage5Paths,
        pPars->fProfile, pCursor,
        ppRootCache );
}

static void * Cec_TranDependencyIteratorStart( Cec_TranSim_t * pSim,
    Cec_ParTran_t * pPars, Cec_TranRoot_t const * pRoot,
    Vec_Int_t * vPool, word * pCare, Cec_TranDepScratch_t * pScratch,
    int * pCursor, void ** ppRootCache )
{
    return Cec_TranDependencyIteratorStartWithRawBudget( pSim, pPars, pRoot,
        vPool, pCare, pScratch, pCursor, ppRootCache, -1 );
}

static int Cec_TranDependencyIteratorNext( Cec_TranSim_t * pSim,
    Cec_TranRoot_t const * pRoot, Vec_Int_t * vPool, word * pCare,
    int fStrict, Cec_TranDepScratch_t * pScratch, void * pIter,
    Cec_TranCand_t * pCand, int * pAttempt, int * pfExhausted,
    long long * pPivotInfo, int * pRawGates, abctime * pIterTime )
{
    abctime clkDiag = pPivotInfo ? Abc_Clock() : 0;
    Vec_Int_t Recipe = {0};
    // Each route has its own iterator and therefore its own divisor-number
    // space.  pScratch->vDivs is only construction scratch and is overwritten
    // when the next route is initialized; using its final size here would
    // misclassify a recipe divisor as an internal gate.  Candidate decoding
    // only needs the current route's divisor count, not the truth-table
    // pointers, so provide a route-local header.
    Vec_Ptr_t Divs = {Vec_IntSize(vPool) + 2,
        Vec_IntSize(vPool) + 2, NULL};
    int * pArray = NULL, nArray, fInvalid;
    (void)pScratch;
    memset( pCand, 0, sizeof(*pCand) );
    nArray = Abc_ResubIteratorNext( pIter, &pArray, pAttempt,
        pfExhausted, &fInvalid );
    *pRawGates = -1;
    if ( pPivotInfo )
        *pIterTime = Abc_Clock() - clkDiag;
    if ( pPivotInfo )
        assert( Abc_ResubIteratorReadPivotProfile(pIter, pPivotInfo) ==
            CEC_TRAN_PIVOT_PROFILE_SIZE );
    if ( *pfExhausted )
        return 0;
    if ( fInvalid )
        return -1;
    *pRawGates = nArray / 2;
    Recipe.nSize = Recipe.nCap = nArray;
    Recipe.pArray = pArray;
    if ( !Cec_TranCandFromDependency(pSim, pRoot, vPool, pCare, fStrict,
            &Divs, &Recipe, pCand) )
        return -1;
    if ( pCand->nGates == 0 )
    {
        Cec_TranCandRecipeRelease( pCand );
        return 0;
    }
    if ( pPivotInfo && *pAttempt == 5 &&
         pPivotInfo[CEC_TRAN_PIVOT_CURRENT_VALID] )
    {
        pCand->nGreedyPivotKind =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_KIND];
        pCand->nGreedyPivotRank =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_RANK];
        pCand->nGreedyPivotCover =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_COVER];
        pCand->nGreedyPivotTotal =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_TOTAL];
        pCand->nGreedyPivotNovel =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_NOVEL];
        pCand->nGreedyPivotRemain =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_REMAIN];
        pCand->fGreedyPivotDuplicate =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_DUPLICATE];
        pCand->nGreedyPathIndex =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_PATH];
        pCand->nGreedySecondRank =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_SECOND_RANK];
        pCand->nGreedySecondCover =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_SECOND_COVER];
        pCand->nGreedyDiversityNew =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_DIVERSITY_NEW];
        pCand->nGreedyDiversitySym =
            (int)pPivotInfo[CEC_TRAN_PIVOT_CURRENT_DIVERSITY_SYM];
    }
    return 1;
}

static int Cec_TranCandDivFeatures( Cec_TranCand_t const * pCand,
    Vec_Int_t * vSupport, int const * pCiKeys,
    int const * pCiScores, int const * pDivRanks, int nCiMask,
    int * pRankMax, int * pRankSum )
{
    int i, iObj, k, Overlap = 0;
    *pRankMax = *pRankSum = 0;
    Vec_IntClear( vSupport );
    Cec_TranCandCollectSupport( pCand, vSupport );
    Vec_IntForEachEntry( vSupport, iObj, i )
    {
        k = (int)(((unsigned)iObj * 0x9E3779B1u) & (unsigned)nCiMask);
        while ( pCiKeys[k] && pCiKeys[k] != iObj + 1 )
            k = (k + 1) & nCiMask;
        if ( pCiKeys[k] )
        {
            Overlap += pCiScores[k];
            *pRankMax = Abc_MaxInt( *pRankMax, pDivRanks[k] );
            *pRankSum += pDivRanks[k];
        }
    }
    return Overlap;
}

// Remove divisors already consumed by the current virtual bundle.
static void Cec_TranFilterCoveredDivPool( Vec_Int_t * vPool,
    char const * pCovered )
{
    int i, iObj, nKeep = 0;
    if ( pCovered == NULL )
        return;
    Vec_IntForEachEntry( vPool, iObj, i )
        if ( !pCovered[iObj] )
            Vec_IntWriteEntry( vPool, nKeep++, iObj );
    Vec_IntShrink( vPool, nKeep );
}

// Constant and Existing are independent lanes.  Constants contain exactly
// const0/const1.  Sequential Existing replacements are restricted to the same
// legal TFI divisor pool used by Build: global equivalences have already had
// their opportunity in the preceding &scorr pass.
static void Cec_TranCollectRootDirectTfi( Gia_Man_t * p,
    Cec_TranSim_t * pSim, Cec_ParTran_t * pPars,
    Cec_TranRoot_t const * pRoot, Vec_Int_t * vPool,
    word * pCare, int fStrict,
    Cec_TranCandVec_t const * pKnown, Cec_TranCandVec_t * pExist,
    Cec_TranDiscStat_t * pStat, Cec_TranProf_t * pProf )
{
    Cec_TranCand_t Cand;
    int f, i, iObj, iStart = pExist->nSize;
    for ( f = 0; f < 2; f++ )
    {
        pStat->nConstants++;
        pStat->nSigChecks++;
        if ( !Cec_TranSigMatchesRoot(pSim, pRoot->iObj,
                Abc_Var2Lit(0, f), pCare) )
        {
            pStat->nSigRejected++;
            continue;
        }
        pStat->nSigMatched++;
        Cand = Cec_TranCandCreateLiteral( pRoot->iObj,
            Abc_Var2Lit(0, f), pRoot->nMffc,
            CEC_TRAN_CAND_CONST, fStrict );
        Cand.Gain = pRoot->nMffc;
        if ( !Cec_TranCandVecContains(pKnown, &Cand) )
            Cec_TranCandVecPush( pExist, Cand );
    }
    if ( pPars->fUseExisting )
        Vec_IntForEachEntry( vPool, iObj, i )
            for ( f = 0; f < 2; f++ )
            {
                int iLit = Abc_Var2Lit( iObj, f );
                pStat->nExisting++;
                pStat->nSigChecks++;
                if ( !Cec_TranSigMatchesRoot(pSim, pRoot->iObj, iLit, pCare) )
                {
                    pStat->nSigRejected++;
                    continue;
                }
                pStat->nSigMatched++;
                Cand = Cec_TranCandCreateLiteral( pRoot->iObj, iLit,
                    pRoot->nMffc, CEC_TRAN_CAND_EXIST, fStrict );
                Cand.Gain = pRoot->nMffc;
                if ( !Cec_TranCandVecContains(pKnown, &Cand) &&
                     !Cec_TranCandVecContains(pExist, &Cand) )
                    Cec_TranCandVecPush( pExist, Cand );
            }
    Cec_TranCandVecEvalSortTail( p, pExist, iStart, pProf );
    Cec_TranDiscFinishRoot( pStat, 0, pExist->nSize - iStart );
}

// MFFC=1 cannot pay for a newly constructed AND.  The experimental ODC
// Direct lane checks only constants and the two immediate fanins here: this
// exposes fanin redundancy without ranking a divisor reservoir or entering
// any Build iterator.  Larger roots keep the unchanged ranked B/q portfolio.
static void Cec_TranOdcDirectMffcOne( Gia_Man_t * p,
    Cec_TranSim_t * pSource, Cec_ParTran_t * pPars,
    Cec_TranRoot_t const * pRoot, int fUseCare,
    Cec_TranCandVec_t const * pKnown, Cec_TranCandVec_t * pOut,
    Cec_TranDiscStat_t * pDisc, Cec_TranProf_t * pProf )
{
    Gia_Obj_t * pRootObj = Gia_ManObj(p, pRoot->iObj);
    Vec_Int_t * vPool = Vec_IntAlloc(2);
    word * pCare = fUseCare ?
        Cec_TranFirstLevelCare(pSource, pRoot->iObj, NULL) : NULL;
    int iObj = Gia_ObjFaninId0p(p, pRootObj);
    assert(pRoot->nMffc == 1);
    Cec_TranCandVecClear(pOut);
    if ( iObj ) Vec_IntPushUnique(vPool, iObj);
    if ( !Gia_ObjIsBuf(pRootObj) )
    {
        iObj = Gia_ObjFaninId1p(p, pRootObj);
        if ( iObj ) Vec_IntPushUnique(vPool, iObj);
    }
    Cec_TranCollectRootDirectTfi(p, pSource, pPars, pRoot, vPool,
        pCare, !fUseCare, pKnown, pOut, pDisc, pProf);
    ABC_FREE(pCare);
    Vec_IntFree(vPool);
}

// Root-only constructed discovery uses one paper-style TFI divisor pool.  A
// lightweight local iterator yields candidates in gate-count/template/coverage
// order; q bounds the per-root frontier.  Six scalar cursors survive this
// call: the historical first four, a Stage-5 rank/flattened-slot cursor, and
// the classified Stage-5 frontier length; all heavyweight resub scratch is
// shared by the pass.
static void Cec_TranCollectRootConstructedIter( Gia_Man_t * p,
    Cec_TranSim_t * pSim, Cec_ParTran_t * pPars,
    Cec_TranRoot_t * pRoot, Cec_TranRootCursor_t * pCursor, int iWave,
    Cec_TranCandVec_t const * pKnown,
    char const * pCovered, char const * pUsed,
    char * pMffc, Vec_Int_t * vMffc, Vec_Int_t * vPool,
    word * pCare, int fStrict,
    Cec_TranDivRank_t const * pRanks,
    Cec_TranCandVec_t const * pExist,
    Cec_TranCandVec_t * pConstr, Cec_TranDepScratch_t * pDep,
    Cec_TranDiscStat_t * pStat, Cec_TranProf_t * pProf )
{
    int i, iAttempt, fExhausted = 0, fUnlimited;
    int nCiHash = 128, nCiMask;
    int IterStatus, fAccepted, iMffcBin, RawGates;
    abctime IterTime = 0, EnumTimeStart;
    Cec_TranDiagGate_t * pDiagGate = NULL;
    int fKnownDuplicate, fExistDuplicate, fPageDuplicate;
    int nNextStart;
    long long nAcceptedStart;
    int iConstrStart = pConstr->nSize;
    int nBudget, iProfWave = Abc_MinInt(iWave, 63);
    Vec_Int_t * vCandSupport = Vec_IntAlloc( 16 );
    int * pCiKeys, * pCiScores, * pDivRanks;
    long long PivotInfo[CEC_TRAN_PIVOT_PROFILE_SIZE];
    void * pIter = NULL;
    Cec_TranCand_t Cand;
    abctime clk, clkAll, clkMffc, timePart;
    (void)p;
    (void)pCovered;
    (void)pUsed;
    (void)pMffc;
    (void)vMffc;
    // In legacy mode q is this call's frontier and q=0 drains the iterator.
    // In micro-batch mode -j is this call's frontier while q is the cumulative
    // number of accepted Build candidates allowed before the snapshot's one
    // selection/commit point.  The last call may therefore be smaller than j.
    fUnlimited = pPars->nRootProofBatch == 0 &&
        pPars->nRootConstrTop == 0;
    nBudget = Cec_TranRootBuildBudget( pPars, pCursor );
    pStat->nConstructed++;
    pStat->nSigChecks++;
    if ( pCursor->fExhausted || (!fUnlimited && nBudget <= 0) ||
         Vec_IntSize(vPool) == 0 )
    {
        pStat->nSigRejected++;
        Vec_IntFree( vCandSupport );
        return;
    }
    assert( pRanks != NULL );
    iMffcBin = Cec_TranBuildMffcBin( pRoot->nMffc );
    EnumTimeStart = pProf->timeRootDepSearch;
    nNextStart = pProf->nRootResubIterNext;
    nAcceptedStart = pProf->nRootBuildAccepted;
    clkMffc = Abc_Clock();
    clkAll = Abc_Clock();
    while ( nCiHash < 2 * Vec_IntSize(vPool) )
        nCiHash <<= 1;
    nCiMask = nCiHash - 1;
    pCiKeys = ABC_CALLOC( int, nCiHash );
    pCiScores = ABC_CALLOC( int, nCiHash );
    pDivRanks = ABC_CALLOC( int, nCiHash );
    for ( i = 0; i < Vec_IntSize(vPool); i++ )
    {
        int iObj = Vec_IntEntry(vPool, pRanks[i].iPos);
        int iHash = (int)(((unsigned)iObj * 0x9E3779B1u) &
            (unsigned)nCiMask);
        while ( pCiKeys[iHash] )
            iHash = (iHash + 1) & nCiMask;
        pCiKeys[iHash] = iObj + 1;
        pCiScores[iHash] = pRanks[i].CiOverlap;
        pDivRanks[iHash] = i + 1;
    }
    timePart = Abc_Clock() - clkAll;
    pProf->timeRootDivPool += timePart;
    pProf->timeRootDivHash += timePart;
    clk = Abc_Clock();
    pIter = Cec_TranDependencyIteratorStart( pSim,
        pPars, pRoot, vPool, pCare, pDep, pCursor->State,
        &pCursor->pBuildCache );
    pCursor->nPages++;
    timePart = Abc_Clock() - clk;
    pProf->timeRootDepInit += timePart;
    pProf->timeRootWaveConstruct[iProfWave] += timePart;
    pProf->nRootResubIterInit++;
    pProf->nRootResubIterLive++;
    pProf->nRootResubIterLiveMax = Abc_MaxInt(
        pProf->nRootResubIterLiveMax, pProf->nRootResubIterLive );
    pProf->nRootWaveDepCalls[iProfWave]++;
    while ( fUnlimited || pConstr->nSize - iConstrStart < nBudget )
    {
        clk = Abc_Clock();
        iAttempt = 0;
        pProf->nRootResubIterNext++;
        IterStatus = Cec_TranDependencyIteratorNext(pSim, pRoot,
            vPool, pCare, fStrict, pDep, pIter, &Cand, &iAttempt, &fExhausted,
            pPars->fProfile ? PivotInfo : NULL, &RawGates, &IterTime);
        timePart = Abc_Clock() - clk;
        if ( pPars->fProfile )
        {
            Cec_TranProfilePivotAttempts( pProf, PivotInfo );
            pCursor->nDiagNext++;
            pCursor->nDiagRaw += RawGates >= 0;
            pCursor->nDiagInvalid += IterStatus < 0;
            pCursor->nDiagCollapsed += IterStatus == 0 && !fExhausted;
            pCursor->nDiagPivots += PivotInfo[CEC_TRAN_PIVOT_ATTEMPT_TOTAL];
            pCursor->timeDiagEnum += timePart;
            pProf->DiagIteratorTime += IterTime;
            pProf->DiagDecodeTime += timePart - IterTime;
            if ( fExhausted ) pProf->DiagExhaustTime += IterTime;
            pDiagGate = NULL;
            if ( RawGates >= 0 && IterStatus >= 0 )
            {
                pDiagGate = &pProf->DiagGates[Cec_TranDiagGateBin(RawGates)]
                    [Cec_TranDiagGateBin(Cand.nGates)];
                pDiagGate->Count++;
                pDiagGate->Time += timePart;
                pDiagGate->Boundary += RawGates == pRoot->nMffc;
                pDiagGate->Rescued += RawGates == pRoot->nMffc &&
                    Cand.nGates < pRoot->nMffc;
            }
        }
        pProf->timeRootDepSearch += timePart;
        pProf->timeRootWaveConstruct[iProfWave] += timePart;
        if ( IterStatus <= 0 )
        {
            if ( IterStatus < 0 )
                pProf->nRootResubInvalid++;
            else if ( !fExhausted )
                pProf->nRootBuildCollapsedDirect++;
            if ( fExhausted )
            {
                pCursor->fExhausted = 1;
                pProf->nRootResubIterExhausted++;
                break;
            }
            continue;
        }
        Cand.nResubRank = ++pCursor->nBuildYield;
        Cand.nResubStage = iAttempt;
        Cand.fExactTemplate = iAttempt != 5;
        Cand.fDivRescue = 0;
        Cand.fPrimaryFrontier = pCursor->nBuildYield == 1;
        Cand.nWave = iWave;
        Cand.Gain = Cand.nMffc - Cand.nGates;
        Cand.nDiagDiscoveryMffc = pRoot->nMffc;
        Cand.nDiagDiscoveryPhase = pProf->DiagPhase;
        Cand.nDiscoveryGain = Cand.Gain;
        if ( pPars->fProfile )
        {
            pCursor->nDiagPositive += Cand.Gain > 0;
            if ( Cand.Gain <= 0 )
            {
                Cec_TranDiagGate_t * pReject =
                    &pProf->DiagReject[iAttempt][Cec_TranDiagGateBin(pRoot->nMffc)];
                pReject->Count++;
                pReject->Time += timePart;
                if ( pDiagGate ) pDiagGate->Nonpositive++;
            }
        }
        Cand.nCiOverlap = Cec_TranCandDivFeatures( &Cand,
            vCandSupport, pCiKeys, pCiScores, pDivRanks, nCiMask,
            &Cand.nDivRankMax, &Cand.nDivRankSum );
        pProf->nRootBuildStageValid[iAttempt]++;
        if ( pPars->fProfile )
            Cec_TranProfilePivotCandidate( pProf, &Cand, -2 );
        Cec_TranSuppProfRecord( pProf->pBuildSuppProf, Cand.iTarget,
            vCandSupport, Cand.nGates, Cand.nResubStage,
            CEC_TRAN_SUPP_VALID );
        pProf->timeRootBuildStage[iAttempt] += timePart;
        fAccepted = 0;
        fKnownDuplicate = Cec_TranCandVecContains(pKnown, &Cand);
        fExistDuplicate = Cec_TranCandVecContains(pExist, &Cand);
        fPageDuplicate = Cec_TranCandVecContains(pConstr, &Cand);
        if ( pPars->fProfile && Cand.nGreedyPathIndex > 1 &&
             (fKnownDuplicate || fExistDuplicate || fPageDuplicate) )
            pProf->nRootMultiPathFingerprintDuplicates++;
        if ( Cand.Gain <= 0 )
            pProf->nRootBuildRejectNonPositive++;
        else if ( fKnownDuplicate )
            pProf->nRootBuildRejectKnown++;
        else if ( fExistDuplicate )
            pProf->nRootBuildRejectDirect++;
        else if ( fPageDuplicate )
            pProf->nRootBuildRejectPage++;
        else
        {
            Cec_TranCandVecPush( pConstr, Cand );
            pCursor->nBuildAccepted++;
            if ( pPars->fProfile && pDiagGate ) pDiagGate->Accepted++;
            pProf->nRootBuildAccepted++;
            pProf->nRootBuildStageAccepted[iAttempt]++;
            if ( pPars->fProfile )
                Cec_TranProfilePivotCandidate( pProf, &Cand, -1 );
            pProf->nRootWaveRecipes[iProfWave]++;
            pStat->nSigMatched++;
            if ( pPars->fProfile && Cand.nGreedyPathIndex > 1 )
            {
                pProf->nRootMultiPathAccepted++;
                // q=0 is an unlimited cumulative horizon even when -j
                // paginates proof work; do not mislabel those j slots as q.
                pProf->nRootMultiPathQSlots +=
                    pPars->nRootConstrTop > 0;
            }
            fAccepted = 1;
        }
        if ( !fAccepted )
            pStat->nSigRejected++;
        Cec_TranCandRecipeRelease( &Cand );
    }
    if ( !fUnlimited && !fExhausted &&
         pConstr->nSize - iConstrStart >= nBudget )
        pProf->nRootResubIterCapped++;
    if ( pConstr->nSize == iConstrStart )
        pStat->nSigRejected++;
    Cec_TranDiscFinishRoot( pStat, 0, pConstr->nSize - iConstrStart );
    Abc_ResubIteratorResumeStop( pIter, pCursor->State );
    if ( pCursor->fExhausted ||
         (pPars->nRootProofBatch > 0 &&
          Cec_TranRootBuildHorizonReached(pPars, pCursor)) )
        Cec_TranRootCursorCacheStop( pCursor );
    assert( pProf->nRootResubIterLive > 0 );
    pProf->nRootResubIterLive--;
    pProf->nRootBuildMffcCalls[iMffcBin]++;
    pProf->nRootBuildMffcNext[iMffcBin] +=
        pProf->nRootResubIterNext - nNextStart;
    pProf->nRootBuildMffcAccepted[iMffcBin] +=
        pProf->nRootBuildAccepted - nAcceptedStart;
    pProf->timeRootBuildMffc[iMffcBin] += Abc_Clock() - clkMffc;
    pCursor->timeExpBuild += Abc_Clock() - clkMffc;
    if ( pPars->fProfile )
    {
        Cec_TranDiagMffc_t * d = &pProf->DiagMffc[Cec_TranDiagGateBin(pRoot->nMffc)];
        d->Calls++;
        d->Next += pProf->nRootResubIterNext - nNextStart;
        d->Accepted += pProf->nRootBuildAccepted - nAcceptedStart;
        d->EnumTime += pProf->timeRootDepSearch - EnumTimeStart;
        d->BuildTime += Abc_Clock() - clkMffc;
    }
    if ( pCursor->fExpConflict )
        assert( pCursor->nBuildAccepted == 0 );
    ABC_FREE( pCiKeys );
    ABC_FREE( pCiScores );
    ABC_FREE( pDivRanks );
    Vec_IntFree( vCandSupport );
}

static int Cec_TranCandRootHeuristicCompare( const void * p0, const void * p1 )
{
    Cec_TranCand_t const * pC0 = (Cec_TranCand_t const *)p0;
    Cec_TranCand_t const * pC1 = (Cec_TranCand_t const *)p1;
    if ( pC0->nMffc != pC1->nMffc )
        return pC1->nMffc - pC0->nMffc;
    if ( pC0->iTarget != pC1->iTarget )
        return pC1->iTarget - pC0->iTarget;
    return Cec_TranCandHeuristicCompare( p0, p1 );
}

#include "cecTranCexProbe.h"
#include "cecTranSigGuide.h"
#include "cecTranSigGuideTest.h"
#include "cecTranStrictCexActive.h"
#include "cecTranStrictGuide.h"

static void Cec_TranRootDiscoverOne( Gia_Man_t * p, Cec_TranSim_t * pSim,
    Cec_TranSim_t * pSource, Cec_TranPatDb_t * pDb, int fRootBatch,
    Cec_ParTran_t * pPars, Cec_TranRoot_t * pRoot,
    Cec_TranRootCursor_t * pCursor, int iWave,
    int fUseTfoDivs, int nTfoMax, int fOdc,
    Cec_TranCandVec_t const * pKnown, char const * pSolved,
    char const * pCovered, char const * pUsed,
    char * pMffc, Vec_Int_t * vMffc, Cec_TranDepScratch_t * pDep,
    Cec_TranDiscStat_t * pDisc, Cec_TranProf_t * pProf,
    Cec_TranCandVec_t * pOut, Cec_TranSigGuide_t * pSigGuide )
{
    Cec_TranCandVec_t Exist = {0}, Build = {0};
    Vec_Int_t * vPool, * vTfo = fUseTfoDivs ? Vec_IntAlloc( 32 ) : NULL;
    Vec_Int_t * vForcedCoreRanks = NULL;
    Cec_TranTfoStats_t TfoStats = {0};
    Cec_TranDivRank_t * pRanks = NULL;
    word * pCareSource = NULL, * pCareBuild = NULL;
    word * pGuideCare=NULL, * pGuideLongCare=NULL;
    Cec_TranSim_t * pGuideSim=pSim;
    int fGuide=0, fGuideImpossible=0;
    int i, nReservoirMax, nReservoirSize;
    int fObsSample = (pPars->nExplore & 2) && iWave == 0 &&
        Cec_TranRootBuildEligible(pRoot) &&
        Cec_TranResidualMix((word)pRoot->iObj) % 16 == 0;
    int nUnique, fConflict;
    abctime clk, clkAll = Abc_Clock(), timePart;
    Cec_TranCandVecClear( pOut );
    // The heavyweight iterator manager is local to this call.  A later
    // no-commit wave restores only this root's scalar cursor onto the shared
    // manager, preserving exact continuation with bounded resident memory.
    (void)pSolved;
    nReservoirMax = pPars->nConstrBaseMax ?
        Abc_MaxInt(4 * pPars->nConstrBaseMax,
            pPars->nConstrBaseMax + 32) : 0;
    clk = Abc_Clock();
    vPool = Cec_TranCollectDivPool( p, pRoot->iObj,
        pPars->nConstrMax, nReservoirMax,
        pPars->fUseMffcDivs,
        pCovered, pUsed, pMffc, vMffc, fUseTfoDivs, nTfoMax,
        vTfo, &TfoStats );
    Cec_TranFilterCoveredDivPool( vPool, pCovered );
    pProf->timeRootDivCollect += Abc_Clock() - clk;
    if ( fUseTfoDivs )
    {
        pProf->nRootTfoCalls++;
        pProf->nRootTfoSeeds += TfoStats.nSeeds;
        pProf->nRootTfoScanned += TfoStats.nScanned;
        pProf->nRootTfoEdges += TfoStats.nEdges;
        pProf->nRootTfoAdded += TfoStats.nAdded;
        pProf->nRootTfoLimitHits += TfoStats.fLimit;
        pProf->nRootTfoAddedMax = Abc_MaxInt( pProf->nRootTfoAddedMax,
            (int)TfoStats.nAdded );
        pProf->timeRootDivTfo += TfoStats.Time;
    }
    nReservoirSize = Vec_IntSize( vPool );
    if ( fOdc )
        pCareSource = (pPars->nExplore & 134217728) ?
            Cec_TranWindowCare(pSource,pRoot->iObj,pPars,pProf) :
            Cec_TranFirstLevelCare(pSource,pRoot->iObj,NULL);
    if ( fObsSample )
    {
        clk = Abc_Clock();
        fConflict = Cec_TranObservationConflict( pSource, pRoot->iObj,
            vPool, &nUnique );
        if ( fConflict >= 0 )
        {
            pProf->nExpFullRoots++;
            pProf->nExpFullConflict += fConflict;
        }
        pProf->timeExpObs += Abc_Clock() - clk;
    }
    if ( Vec_IntSize(vPool) )
    {
        clk = Abc_Clock();
        pRanks = Cec_TranRankDivReservoir(
            fRootBatch ? pSource : pSim, pRoot->iObj, vPool, pPars, pProf,
            pCareSource );
        timePart = Abc_Clock() - clk;
        pCursor->timeExpRank += timePart;
        pProf->timeRootDivRank += timePart;
        if ( Cec_TranRootBuildEligible(pRoot) )
        {
            if ( iWave == 0 )
            {
                pProf->timeRootDivRankEligibleFirst += timePart;
                pProf->nRootDivRankEligibleFirstCalls++;
            }
            else
            {
                pProf->timeRootDivRankEligibleCont += timePart;
                pProf->nRootDivRankEligibleContCalls++;
            }
        }
        else if ( iWave == 0 )
        {
            pProf->timeRootDivRankMffcOneFirst += timePart;
            pProf->nRootDivRankMffcOneFirstCalls++;
        }
        else
        {
            pProf->timeRootDivRankMffcOneCont += timePart;
            pProf->nRootDivRankMffcOneContCalls++;
        }
        clk = Abc_Clock();
        // The independent score ranks each divisor in isolation.  Before
        // truncating to B, give rejected complete-fanin TFOs one conditional
        // chance: search top-B plus all legal TFOs for an exact observed core.
        // Only a complete core can replace ranked nodes, so this does not
        // reserve a blind TFO quota or expand any downstream budget.
        if ( fOdc && (pPars->nExplore & 33554432) &&
             pPars->nKitCoreMax > 0 && Cec_TranRootBuildEligible(pRoot) &&
             pPars->nConstrBaseMax > 0 )
        {
            Vec_Int_t * vCore = Vec_IntAlloc(pPars->nKitCoreMax);
            Vec_Int_t * vPinned = Vec_IntAlloc(pPars->nKitCoreMax);
            int nCore = Cec_TranSelectCareObservedCoreExcept(pSource,
                pRoot->iObj, vPool, pPars->nKitCoreMax, vCore, -1, pCareSource);
            int j, k;
            if ( nCore > 0 )
                Vec_IntForEachEntry(vCore, k, j)
                    Vec_IntPush(vPinned, Vec_IntEntry(vPool, k));
            pProf->nOdcCarePoolChanged += Cec_TranSelectRankedDivPool(
                vPool, pRanks, pPars->nConstrBaseMax, vPinned) != 0;
            Vec_IntFree(vCore);
            Vec_IntFree(vPinned);
        }
        else if ( fUseTfoDivs && iWave == 0 && pPars->nKitCoreMax > 0 &&
             Cec_TranRootBuildEligible(pRoot) && pPars->nConstrBaseMax > 0 )
        {
            Vec_Int_t * vCorePool = Vec_IntAlloc(
                pPars->nConstrBaseMax + Vec_IntSize(vTfo) );
            Vec_Int_t * vCoreRanks = Vec_IntAlloc( pPars->nKitCoreMax );
            Vec_Int_t * vPinned = Vec_IntAlloc( pPars->nKitCoreMax );
            int k, iObj, nCore, nTop = Abc_MinInt(pPars->nConstrBaseMax,
                Vec_IntSize(vPool));
            abctime clkCore;
            for ( i = 0; i < nTop; i++ )
                Vec_IntPush( vCorePool,
                    Vec_IntEntry(vPool, pRanks[i].iPos) );
            Vec_IntForEachEntry( vTfo, iObj, i )
                if ( Vec_IntFind(vPool, iObj) >= 0 &&
                     Vec_IntFind(vCorePool, iObj) < 0 )
                    Vec_IntPush( vCorePool, iObj );
            // Without a legal TFO outside top-B, rescue cannot change the
            // physical Build pool.  The regular portfolio selector below
            // will still evaluate top-B, so skip this redundant full search.
            if ( Vec_IntSize(vCorePool) == nTop )
            {
                pProf->nRootTfoCoreRescueNoExtra++;
                nCore = -1;
                Cec_TranSelectRankedDivPool( vPool, pRanks,
                    pPars->nConstrBaseMax, NULL );
            }
            else
            {
                pProf->nRootTfoCoreRescueCalls++;
                // Root-batch pSim is not populated until after the final pool
                // is known.  Select rescue members on the same complete
                // source observations used by reservoir ranking; teaching
                // later copies a subset of these exact columns into pSim.
                clkCore = Abc_Clock();
                nCore = Cec_TranSelectExactObservedCore(
                    fRootBatch ? pSource : pSim, pRoot->iObj,
                    vCorePool, pPars->nKitCoreMax, vCoreRanks );
                pProf->timeRootTfoCoreSelect += Abc_Clock() - clkCore;
                // Experimental construction-guided membership: retain the
                // current greedy core as the baseline, but test one
                // stable leave-one-out cores over top-B plus rejected TFOs.
                // A different pool is chosen only for a strictly smaller
                // realizable Kit/BDC graph, or when the baseline greedy core
                // failed and the alternative is both exact and realizable.
                if ( pPars->nExplore & 16 )
                {
                    Cec_TranSim_t * pCoreSim = fRootBatch ? pSource : pSim;
                    Vec_Int_t * vBestCore = nCore > 0 ?
                        Vec_IntDup(vCoreRanks) : NULL;
                    int nChoices = Vec_IntSize( vCoreRanks );
                    int nTrials;
                    int fPrimaryExact = nCore > 0;
                    int fBestChanged = 0;
                    abctime clkValue = Abc_Clock();
                    int BestCost = nCore > 0 ?
                        Cec_TranRootIsfGateCost(pCoreSim, pPars, pRoot,
                            vCorePool, vCoreRanks, nCore) : 0x3fffffff;
                    int iTrial;
                    // One gate is the realizable lower bound accepted by the
                    // unchanged positive-gain checks.  No alternative can
                    // strictly improve it, so avoid an exact-core search that
                    // is provably unable to change membership.
                    nTrials = BestCost == 1 ? 0 :
                        Abc_MinInt( 1, nChoices );
                    for ( iTrial = 0; iTrial < nTrials; iTrial++ )
                    {
                        Vec_Int_t * vAltCore = Vec_IntAlloc(
                            pPars->nKitCoreMax );
                        int j, nAltCore, fHasRejectedTfo = 0, AltCost;
                        pProf->nRootTfoCoreValueTrials++;
                        nAltCore = Cec_TranSelectExactObservedCoreExcept(
                            pCoreSim, pRoot->iObj, vCorePool,
                            pPars->nKitCoreMax, vAltCore,
                            Vec_IntEntry(vCoreRanks, iTrial) );
                        if ( nAltCore > 0 )
                            Vec_IntForEachEntry( vAltCore, j, k )
                                fHasRejectedTfo |= j >= nTop;
                        if ( nAltCore > 0 && fHasRejectedTfo )
                        {
                            pProf->nRootTfoCoreValueExact++;
                            AltCost = Cec_TranRootIsfGateCost( pCoreSim,
                                pPars, pRoot, vCorePool, vAltCore, nAltCore );
                            if ( AltCost < BestCost )
                            {
                                Vec_IntFreeP( &vBestCore );
                                vBestCore = Vec_IntDup( vAltCore );
                                BestCost = AltCost;
                                fBestChanged = 1;
                            }
                        }
                        Vec_IntFree( vAltCore );
                    }
                    if ( vBestCore && fBestChanged )
                    {
                        Vec_IntClear( vCoreRanks );
                        Vec_IntAppend( vCoreRanks, vBestCore );
                        nCore = Vec_IntSize( vCoreRanks );
                        pProf->nRootTfoCoreValueChanged++;
                        pProf->nRootTfoCoreValueUnlocked += !fPrimaryExact;
                    }
                    Vec_IntFreeP( &vBestCore );
                    pProf->timeRootTfoCoreValue += Abc_Clock() - clkValue;
                }
                if ( nCore > 0 )
                {
                    pProf->nRootTfoCoreRescueExact++;
                    Vec_IntForEachEntry( vCoreRanks, k, i )
                        Vec_IntPush( vPinned, Vec_IntEntry(vCorePool, k) );
                    k = Cec_TranSelectRankedDivPool( vPool, pRanks,
                        pPars->nConstrBaseMax, vPinned );
                    if ( k )
                    {
                        pProf->nRootTfoCoreRescueRoots++;
                        pProf->nRootTfoCoreRescueNodes += k;
                        vForcedCoreRanks = Vec_IntAlloc( nCore );
                        Vec_IntForEachEntry( vPinned, iObj, i )
                        {
                            k = Vec_IntFind( vPool, iObj );
                            assert( k >= 0 );
                            Vec_IntPush( vForcedCoreRanks, k );
                        }
                    }
                }
                if ( nCore <= 0 )
                    Cec_TranSelectRankedDivPool( vPool, pRanks,
                        pPars->nConstrBaseMax, NULL );
            }
            Vec_IntFree( vPinned );
            Vec_IntFree( vCoreRanks );
            Vec_IntFree( vCorePool );
        }
        else
            Cec_TranSelectRankedDivPool( vPool, pRanks,
                pPars->nConstrBaseMax, NULL );
        pProf->timeRootDivSelect += Abc_Clock() - clk;
    }
    if ( pPars->fUseConstr && Cec_TranRootBuildEligible(pRoot) )
        Cec_TranRootCursorBindBuildPool( pCursor, iWave, vPool, pRanks );
    if ( fUseTfoDivs )
        Vec_IntForEachEntry( vPool, nUnique, i )
            pProf->nRootTfoSelected += Vec_IntFind(vTfo, nUnique) >= 0;
    // Teaching must see the actual ranked Build pool, not an arbitrary BFS
    // prefix that may be discarded immediately afterwards.
    if ( fRootBatch )
        Cec_TranTeachBuildSignature( pSource, pSim, pDb,
            pRoot->iObj, vPool, &pCursor->pTeachCache, pProf, pCareSource );
    if ( fOdc )
    {
        if ( pSim == pSource )
            pCareBuild = pCareSource;
        else
        {
            assert( pCursor->pTeachCache->pCare );
            pCareBuild = ABC_ALLOC( word, pSim->nSlots );
            memcpy( pCareBuild, pCursor->pTeachCache->pCare,
                sizeof(word) * pSim->nSlots );
        }
    }
    if ( fObsSample || ((pPars->nExplore & 4) && iWave == 0 &&
            Cec_TranRootBuildEligible(pRoot)) )
    {
        clk = Abc_Clock();
        fConflict = Cec_TranObservationConflict( pSim, pRoot->iObj,
            vPool, &nUnique );
        if ( fConflict >= 0 )
        {
            pProf->nExpObsRoots++;
            pProf->nExpObsConflict += fConflict;
            pProf->nExpObsTotal += 64 * pSim->nSlots;
            pProf->nExpObsUnique += nUnique;
            pCursor->fExpConflict = fConflict;
            if ( fConflict && (pPars->nExplore & 4) )
            {
                pCursor->fExhausted = 1;
                pProf->nExpPruned++;
            }
        }
        pProf->timeExpObs += Abc_Clock() - clk;
    }
    if ( Vec_IntSize(vPool) )
    {
        if ( pPars->fUseConstr && Cec_TranRootBuildEligible(pRoot) &&
             iWave == 0 )
            Cec_TranSuppProfResidualSample( pProf->pBuildSuppProf, pSim,
                pRoot->iObj, vPool, pRanks,
                pPars->nConstrBaseMax ? pPars->nConstrBaseMax : 32 );
    }
    if ( pPars->fUseConstr )
    {
        pProf->nRootDivReservoirCalls++;
        pProf->nRootDivReservoirNodes += nReservoirSize;
        pProf->nRootDivReservoirMax = Abc_MaxInt(
            pProf->nRootDivReservoirMax, nReservoirSize );
        pProf->nRootDivPoolNodes += Vec_IntSize(vPool);
        pProf->nRootDivPoolMax = Abc_MaxInt(
            pProf->nRootDivPoolMax, Vec_IntSize(vPool) );
        pProf->nRootDivPoolEmpty += Vec_IntSize(vPool) == 0;
        pProf->nRootBuildMffcSum += pRoot->nMffc;
        pProf->nRootBuildMffcMax = Abc_MaxInt(
            pProf->nRootBuildMffcMax, pRoot->nMffc );
    }
    timePart = Abc_Clock() - clkAll;
    pProf->timeRootDivPool += timePart;
    clk = Abc_Clock();
    // Under SEQ proof micro-batching Direct belongs only to the first batch.
    // The snapshot is immutable until the q horizon, so no later Constant or
    // Existing relation can become newly visible.  Legacy mode keeps its old
    // behavior, including the harmless Known-filtered rescan on later waves.
    if ( !pPars->fBuildOnly &&
         (pPars->nRootProofBatch == 0 || iWave == 0) )
        Cec_TranCollectRootDirectTfi( p, pSource, pPars, pRoot, vPool,
            pCareSource, !fOdc,
            pKnown, &Exist, pDisc, pProf );
    for ( i = 0; i < Exist.nSize; i++ )
        Exist.pArray[i].nWave = iWave;
    pProf->timeRootDirect += Abc_Clock() - clk;
    fGuide=fOdc && s_CexMode && s_CexCompress>=4 && Vec_IntSize(vPool)>0;
    if(fGuide) {
        abctime cg=Abc_Clock();
        assert(iWave==0 && !pCursor->State[0] && !pCursor->pBuildCache);
        pGuideLongCare=Cec_TranWindowCare(s_CexLong,pRoot->iObj,pPars,NULL);
        pGuideCare=Cec_TranCexCompact(pSim,pCareBuild,s_CexLong,pGuideLongCare,pRoot->iObj,vPool);
        pGuideSim=s_CexPacked; fGuideImpossible=s_CexThisConflict;
        s_CexTime+=Abc_Clock()-cg;
        Cec_TranSigGuideApply( pSigGuide, pRoot->iObj, vPool,
            &pGuideSim, &pGuideCare, &fGuideImpossible );
    }
    if ( pPars->fUseConstr && Cec_TranRootBuildEligible(pRoot) && !fGuideImpossible ) {
        Cec_TranDepScratch_t GuideDep;
        Cec_TranSim_t * pNativeSim=pGuideSim, * pNarrow=NULL;
        Vec_Int_t * vNativePool=vPool, * vNarrow=NULL;
        Cec_TranDivRank_t * pNativeRanks=pRanks, * pNarrowRanks=NULL;
        Cec_TranRootCursor_t NarrowCursor={0}, * pNativeCursor=pCursor;
        word * pNativeCare=fGuide?pGuideCare:pCareBuild, * pNarrowCare=NULL;
        abctime cn=Abc_Clock();
        if(fGuide && s_CexCompress>=5) {
            Vec_Int_t * core=Vec_IntAlloc(8);
            int nc=Cec_TranSelectCareObservedCoreExcept(pGuideSim,pRoot->iObj,vPool,pPars->nKitCoreMax,core,-1,pGuideCare);
            if(nc>0) {
                int j,k,primarySize=nc;
                Vec_Int_t * members=Vec_IntDup(core);
                if(s_CexCompress==6) {
                    for(j=0;j<primarySize;++j) {
                        Vec_Int_t * alt=Vec_IntAlloc(8);
                        int h,d,na=Cec_TranSelectCareObservedCoreExcept(pGuideSim,pRoot->iObj,vPool,pPars->nKitCoreMax,alt,Vec_IntEntry(core,j),pGuideCare);
                        if(na>0) Vec_IntForEachEntry(alt,d,h) Vec_IntPushUnique(members,d);
                        Vec_IntFree(alt);
                    }
                    Vec_IntSort(members,0);
                }
                nc=Vec_IntSize(members);
                vNarrow=Vec_IntAlloc(nc); pNarrowRanks=ABC_ALLOC(Cec_TranDivRank_t,nc);
                Vec_IntForEachEntry(members,k,j) {
                    Vec_IntPush(vNarrow,Vec_IntEntry(vPool,k));
                    pNarrowRanks[j]=pRanks[k]; pNarrowRanks[j].iPos=j;
                }
                Vec_IntFree(members);
                pNarrow=Cec_TranSimStartRootBatch(p,s_CexCompress==5?4:pGuideSim->nSlots,1);
                s_CexPacked=pNarrow; s_CexNarrowing=1;
                pNarrowCare=Cec_TranCexCompact(pGuideSim,pGuideCare,NULL,NULL,pRoot->iObj,vNarrow);
                s_CexNarrowing=0; s_CexPacked=pGuideSim;
                assert(!s_CexThisConflict && (s_CexCompress!=5 || pNarrow->nSlots<=4));
                pNativeSim=pNarrow; pNativeCare=pNarrowCare;
                vNativePool=vNarrow; pNativeRanks=pNarrowRanks;
                pNativeCursor=&NarrowCursor;
                Cec_TranRootCursorBindBuildPool(pNativeCursor,0,vNativePool,pNativeRanks);
                s_CexNarrowRoots++; s_CexNarrowDivsBefore+=Vec_IntSize(vPool); s_CexNarrowDivsAfter+=nc;
            }
            Vec_IntFree(core);
        }
        if(fGuide) {
            Abc_ResubPrepareManager(pNativeSim->nSlots);
            Cec_TranDepScratchStart(&GuideDep,pNativeSim->nSlots,Vec_IntSize(vNativePool),1);
        }
        Cec_TranCollectRootConstructedIter( p, pNativeSim, pPars, pRoot,
            pNativeCursor, iWave,
            pKnown, pCovered, pUsed, pMffc, vMffc, vNativePool,
            pNativeCare, !fOdc, pNativeRanks,
            &Exist, &Build,
            fGuide?&GuideDep:pDep, pDisc, pProf );
        if(fGuide) {
            Cec_TranDepScratchStop(&GuideDep);
            Abc_ResubPrepareManager(pSim->nSlots);
            for(i=0;i<Build.nSize;++i) {
                assert(Cec_TranRecipeMatchesRoot(pSim,Build.pArray+i,pCareBuild));
                assert(Cec_TranRecipeMatchesRoot(s_CexLong,Build.pArray+i,pGuideLongCare));
            }
        }
        if(pNarrow) {
            Cec_TranRootCursorStop(&NarrowCursor);
            Cec_TranSimStop(pNarrow); ABC_FREE(pNarrowCare);
            Vec_IntFree(vNarrow); ABC_FREE(pNarrowRanks);
        }
        if(fOdc) s_CexNativeTime+=Abc_Clock()-cn;
    }
    else if ( pPars->fUseConstr && !fGuideImpossible )
        pProf->nRootBuildMffcOneSkipped++;
    if ( pProf->DiagPhase && pPars->nKitCoreMax > 0 && iWave == 0 &&
         pPars->fUseConstr && Cec_TranRootBuildEligible(pRoot) &&
         Vec_IntSize(vPool) > 0 && !fGuideImpossible )
    {
        unsigned Off[8] = {0}, On[8] = {0};
        Vec_Int_t * vIsfCoreRanks = vForcedCoreRanks;
        int nCore;
        clk = Abc_Clock();
        if ( vIsfCoreRanks )
            nCore = Vec_IntSize( vIsfCoreRanks );
        else
        {
            abctime clkCore = Abc_Clock();
            vIsfCoreRanks = Vec_IntAlloc( pPars->nKitCoreMax );
            nCore = Cec_TranSelectExactObservedCore( pSim, pRoot->iObj,
                vPool, pPars->nKitCoreMax, vIsfCoreRanks );
            pProf->timeRootIsfCoreSelect += Abc_Clock() - clkCore;
        }
        if ( nCore > 0 )
            Cec_TranProjectRootIsf( pSim, pRoot, vPool,
                vIsfCoreRanks, nCore, Off, On, pProf );
        Cec_TranCollectRootIsfCandidate( pSim, pPars, pRoot, vPool,
            pRanks, pKnown, &Exist, &Build, pProf,
            vIsfCoreRanks, nCore, Off, On, 0, NULL );
        if ( pPars->fBdcPortfolio )
            Cec_TranCollectRootIsfCandidate( pSim, pPars, pRoot, vPool,
                pRanks, pKnown, &Exist, &Build, pProf,
                vIsfCoreRanks, nCore, Off, On, 1, NULL );
        // Add a genuinely care-aware core/ISF portfolio without removing
        // the strict incumbent. All recipes still require the normal proof.
        if ( (fGuide?pGuideCare:pCareBuild) && (pPars->nExplore & 8192) )
        {
            Vec_Int_t * vCareCore = Vec_IntAlloc(pPars->nKitCoreMax);
            unsigned CareOff[8] = {0}, CareOn[8] = {0};
            int nCareCore = Cec_TranSelectCareObservedCoreExcept(pGuideSim,
                pRoot->iObj, vPool, pPars->nKitCoreMax, vCareCore, -1, (fGuide?pGuideCare:pCareBuild));
            if ( nCareCore > 0 )
            {
                Cec_TranProjectRootIsfCareRaw(pGuideSim, pRoot, vPool,
                    vCareCore, nCareCore, CareOff, CareOn, (fGuide?pGuideCare:pCareBuild));
                Cec_TranCollectRootIsfCandidate(pGuideSim, pPars, pRoot, vPool,
                    pRanks, pKnown, &Exist, &Build, pProf, vCareCore,
                    nCareCore, CareOff, CareOn, 0, (fGuide?pGuideCare:pCareBuild));
                if ( pPars->fBdcPortfolio )
                    Cec_TranCollectRootIsfCandidate(pGuideSim, pPars, pRoot, vPool,
                        pRanks, pKnown, &Exist, &Build, pProf, vCareCore,
                        nCareCore, CareOff, CareOn, 1, (fGuide?pGuideCare:pCareBuild));
            }
            if ( nCareCore > 0 && (pPars->nExplore & 67108864) )
            {
                int j, excluded;
                Vec_IntForEachEntry(vCareCore, excluded, j)
                {
                    Vec_Int_t * vAlt = Vec_IntAlloc(pPars->nKitCoreMax);
                    unsigned AltOff[8] = {0}, AltOn[8] = {0};
                    int nAlt = Cec_TranSelectCareObservedCoreExcept(pGuideSim,
                        pRoot->iObj, vPool, pPars->nKitCoreMax, vAlt, excluded, (fGuide?pGuideCare:pCareBuild));
                    if ( nAlt > 0 )
                    {
                        pProf->nOdcCoreVariants++;
                        Cec_TranProjectRootIsfCareRaw(pGuideSim, pRoot, vPool,
                            vAlt, nAlt, AltOff, AltOn, (fGuide?pGuideCare:pCareBuild));
                        Cec_TranCollectRootIsfCandidate(pGuideSim, pPars, pRoot,
                            vPool, pRanks, pKnown, &Exist, &Build, pProf,
                            vAlt, nAlt, AltOff, AltOn, 0, (fGuide?pGuideCare:pCareBuild));
                        if ( pPars->fBdcPortfolio )
                            Cec_TranCollectRootIsfCandidate(pGuideSim, pPars, pRoot,
                                vPool, pRanks, pKnown, &Exist, &Build, pProf,
                                vAlt, nAlt, AltOff, AltOn, 1, (fGuide?pGuideCare:pCareBuild));
                    }
                    Vec_IntFree(vAlt);
                }
            }
            Vec_IntFree(vCareCore);
        }
        if ( vIsfCoreRanks != vForcedCoreRanks )
            Vec_IntFree( vIsfCoreRanks );
        pProf->timeRootIsf += Abc_Clock() - clk;
    }
    for ( i = 0; i < Exist.nSize; i++ )
        if ( !Cec_TranCandVecContains(pOut, Exist.pArray + i) )
            Cec_TranCandVecPush( pOut, Exist.pArray[i] );
    for ( i = 0; i < Build.nSize; i++ )
        if ( !Cec_TranCandVecContains(pOut, Build.pArray + i) )
            Cec_TranCandVecPush( pOut, Build.pArray[i] );
    if ( pOut->nSize > 1 )
        qsort( pOut->pArray, pOut->nSize, sizeof(Cec_TranCand_t),
            Cec_TranCandHeuristicCompare );
    if (fOdc && s_CexMode && !fGuide) {
        Cec_TranCexReconstruct(pSim,pPars,pRoot,vPool,pRanks,pCareBuild,pKnown,pOut,pProf);
        if (pOut->nSize>1) qsort(pOut->pArray,pOut->nSize,sizeof(Cec_TranCand_t),Cec_TranCandHeuristicCompare);
    }
    if(fGuide) {
        if(getenv("ABC_CEX_DETAIL") && Cec_TranResidualMix(pRoot->iObj)%64==0) {
            Vec_Int_t * nodes=Vec_IntAlloc(32), * ends=Vec_IntAlloc(16);
            int ov,j,obj;
            Cec_TranWindowCollect(p,pRoot->iObj,Cec_TranWindowDepth(pPars),
                100-pPars->nDepNodesMax,nodes,ends,&ov);
            Abc_Print(1,"cex-window root=%d nodes=",pRoot->iObj);
            Vec_IntForEachEntry(nodes,obj,j) Abc_Print(1,"%s%d",j?",":"",obj);
            Abc_Print(1," ends=");
            Vec_IntForEachEntry(ends,obj,j) Abc_Print(1,"%s%d",j?",":"",obj);
            Abc_Print(1,"\n");
            Vec_IntFree(nodes); Vec_IntFree(ends);
            for(i=0;i<Build.nSize;++i) {
                Cec_TranCand_t * c=Build.pArray+i;
                Abc_Print(1,"cex-guide-recipe root=%d hash=%u long-match=%d out=%d recipe=",pRoot->iObj,Cec_TranCandHash(c),Cec_TranRecipeMatchesRoot(s_CexLong,c,pGuideLongCare),c->iOut);
                for(j=0;j<2*c->nGates;++j) Abc_Print(1,"%s%d",j?",":"",c->Recipe[j]);
                Abc_Print(1,"\n");
            }
        }
        ABC_FREE(pGuideCare); ABC_FREE(pGuideLongCare);
    }
    Cec_TranCandVecStop( &Exist );
    Cec_TranCandVecStop( &Build );
    ABC_FREE( pRanks );
    Vec_IntFreeP( &vForcedCoreRanks );
    if ( pCareBuild != pCareSource )
        ABC_FREE( pCareBuild );
    ABC_FREE( pCareSource );
    Vec_IntFree( vPool );
    Vec_IntFreeP( &vTfo );
}

static int Cec_TranRootRefreshPotential( Gia_Man_t * p,
    Cec_TranRoot_t * pRoots, int nRoots, char const * pCovered,
    char const * pUsed, char * pMffc, Vec_Int_t * vMffc,
    Cec_TranProf_t * pProf )
{
    int r, nPositive = 0, nOld;
    for ( r = 0; r < nRoots; r++ )
    {
        nOld = pRoots[r].nMffc;
        if ( pCovered[pRoots[r].iObj] || pUsed[pRoots[r].iObj] )
        {
            if ( pProf && nOld > 0 )
                pProf->nDirtyRootFreed++;
            pRoots[r].nMffc = 0;
            continue;
        }
        Cec_TranMarkDynamicMffc( p, pRoots[r].iObj, pCovered, pUsed,
            NULL, pMffc, vMffc );
        pRoots[r].nMffc = Vec_IntSize( vMffc );
        if ( pProf && nOld > 0 && pRoots[r].nMffc != nOld )
            pProf->nDirtyMffcChanged++;
        nPositive += pRoots[r].nMffc > 0;
    }
    qsort( pRoots, nRoots, sizeof(Cec_TranRoot_t), Cec_TranRootCompare );
    return nPositive;
}

static void Cec_TranRootPrepareSeqFrontier( Gia_Man_t * p,
    Cec_TranRoot_t * pRoots, int nRoots, Cec_TranCandVec_t const * pCands,
    char const * pCovered, char const * pUsed, char * pMffc,
    Vec_Int_t * vMffc, Vec_Int_t * vSupport,
    int fRefreshRoots, Cec_TranCandVec_t * pSeq, Cec_TranProf_t * pProf )
{
    int r, i, k, iObj, Gain, fSupportFreed;
    int fFirstFrontier = pProf->nRootFrontCalls++ == 0;
    int * pRefs = NULL;
    Vec_Int_t * vHeads, * vNext;
    abctime clk, clkLoop;
    Cec_TranCandVecClear( pSeq );
    clk = Abc_Clock();
    for ( i = 0; i < pCands->nSize; i++ )
        if ( pCands->pArray[i].nStatus == CEC_TRAN_STATE_CANDIDATE &&
             (pCovered[pCands->pArray[i].iTarget] ||
              pUsed[pCands->pArray[i].iTarget]) )
            pProf->nDirtyRootFreed++;
    pProf->timeRootFrontDead += Abc_Clock() - clk;
    // Generic callers may supply changed virtual-selection sets.  The main
    // pass reuses its initial MFFCs because discovery never changes those sets.
    if ( fRefreshRoots )
    {
        clk = Abc_Clock();
        Cec_TranRootRefreshPotential( p, pRoots, nRoots, pCovered, pUsed,
            pMffc, vMffc, pProf );
        pProf->timeRootPotentialRefresh += Abc_Clock() - clk;
    }
    clkLoop = Abc_Clock();
    vHeads = Vec_IntStartFull( Gia_ManObjNum(p) );
    vNext = Vec_IntStartFull( pCands->nSize );
    // Prepend in reverse Page order.  Visiting roots in the old root order
    // and each list in Page order preserves the exact pre-sort sequence,
    // including comparator ties, without the root x candidate scan.
    for ( i = pCands->nSize - 1; i >= 0; i-- )
    {
        Cec_TranCand_t const * pCand = pCands->pArray + i;
        if ( pCand->nStatus != CEC_TRAN_STATE_CANDIDATE )
            continue;
        assert( pCand->iTarget >= 0 && pCand->iTarget < Gia_ManObjNum(p) );
        Vec_IntWriteEntry( vNext, i, Vec_IntEntry(vHeads, pCand->iTarget) );
        Vec_IntWriteEntry( vHeads, pCand->iTarget, i );
    }
    for ( r = 0; r < nRoots && pRoots[r].nMffc > 0; r++ )
    {
        for ( i = Vec_IntEntry(vHeads, pRoots[r].iObj); i >= 0;
              i = Vec_IntEntry(vNext, i) )
        {
            Cec_TranCand_t Cand = pCands->pArray[i];
            assert( Cand.iTarget == pRoots[r].iObj &&
                Cand.nStatus == CEC_TRAN_STATE_CANDIDATE );
            pProf->nRootFrontPairScans++;
            if ( fFirstFrontier )
                pProf->nRootFrontPairScansFirst++;
            else
                pProf->nRootFrontPairScansCont++;
            pProf->nRootFrontMatched++;
            if ( pCovered[Cand.iTarget] || pUsed[Cand.iTarget] )
            {
                pProf->nDirtyRootFreed++;
                continue;
            }
            clk = Abc_Clock();
            Cec_TranCandCollectSupport( &Cand, vSupport );
            fSupportFreed = 0;
            Vec_IntForEachEntry( vSupport, iObj, k )
                fSupportFreed |= pCovered[iObj] != 0;
            pProf->timeRootFrontSupport += Abc_Clock() - clk;
            if ( fSupportFreed )
            {
                pProf->nDirtySupportFreed++;
                continue;
            }
            clk = Abc_Clock();
            // Every candidate has its own support boundary, but the graph
            // and virtual-selection sets are fixed for this entire Page.
            // Prepare global refs only on the first gain evaluation; local
            // dereference/reference traversals restore them for the next one.
            if ( pRefs == NULL )
                pRefs = Cec_TranMffcRefsStart( p, pCovered );
            Gain = Cec_TranCandDynamicGainWithRefs( p, &Cand, pCovered,
                pUsed, pRefs, pMffc, vMffc, vSupport );
            pProf->timeRootFrontGain += Abc_Clock() - clk;
            if ( Gain <= 0 )
            {
                pProf->nDirtyMffcChanged++;
                continue;
            }
            if ( Gain != Cand.Gain || Vec_IntSize(vMffc) != Cand.nMffc )
                pProf->nDirtyMffcChanged++;
            Cand.Gain = Gain;
            Cand.nMffc = pRoots[r].nMffc;
            Cec_TranCandVecPush( pSeq, Cand );
        }
    }
    ABC_FREE( pRefs );
    Vec_IntFree( vHeads );
    Vec_IntFree( vNext );
    clk = Abc_Clock() - clkLoop;
    pProf->timeRootFrontLoop += clk;
    if ( fFirstFrontier )
        pProf->timeRootFrontLoopFirst += clk;
    else
        pProf->timeRootFrontLoopCont += clk;
    if ( pSeq->nSize > 1 )
    {
        clk = Abc_Clock();
        qsort( pSeq->pArray, pSeq->nSize, sizeof(Cec_TranCand_t),
            Cec_TranCandRootHeuristicCompare );
        pProf->timeRootFrontSort += Abc_Clock() - clk;
    }
}
