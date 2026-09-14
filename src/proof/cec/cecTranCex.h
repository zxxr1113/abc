// CEX storage, trace simulation, selection, and free-state screening.
// Private implementation fragment included only by cecTrans.c.

// A signature is a collection of independent reset-reachable traces.  Every
// word carries 64 traces in parallel; consecutive frame groups carry the
// successive states of each trace.  stran2 gives the fixed trace lanes to
// scorr CEX first and fills only the unused lanes randomly.  These signatures
// only guide search: all accepted edits are still discharged by the
// sequential proof oracle.
typedef struct Cec_TranSim_t_ Cec_TranSim_t;
struct Cec_TranSim_t_
{
    Gia_Man_t *     pGia;
    int             nBudgetWords;   // configured Q: words consumed by Build
    int             nWords;
    int             nFrames;
    int             nSlots;
    word *          pSims;          // [object ID][frame * nWords + word]
    word *          pState;         // current values of the ROs
    int *           pCiCounts;      // support size + 1, immutable snapshot only
    word *          pObsKeys;
    unsigned char * pObsLabels;
    int             nObsCap;
    int             nObsKeyWords;
};

// The stran2 pattern database owns the reset-reachable CEX traces collected by
// its preliminary default scorr.  The bank is frozen before transduction: CEX
// occupy the fixed Build trace lanes directly, or feed root-local trace
// selection only when the bank overflows Q.  They are never a post-build
// filter and never cross-wave feedback in this version.
typedef struct Cec_TranPatDb_t_ Cec_TranPatDb_t;
struct Cec_TranPatDb_t_
{
    Vec_Ptr_t *      vCexes;
    Vec_Int_t *      vBatchEnds;    // groups of at most 64 packed CEX traces
    int              nPis;
    int              nRegs;
    int              nMax;
    int              nFramesMax;
    int              nSeen;
    int              nDup;
    int              nIgnoredInd;
    int              nTooLong;
};

static Cec_TranPatDb_t * Cec_TranPatDbStart( Gia_Man_t * p, int nMax )
{
    Cec_TranPatDb_t * pDb = ABC_CALLOC( Cec_TranPatDb_t, 1 );
    pDb->vCexes = Vec_PtrAlloc( nMax );
    pDb->vBatchEnds = Vec_IntAlloc( 8 );
    pDb->nPis = Gia_ManPiNum(p);
    pDb->nRegs = Gia_ManRegNum(p);
    pDb->nMax = nMax;
    return pDb;
}

static void Cec_TranPatDbStop( Cec_TranPatDb_t * pDb )
{
    Abc_Cex_t * pCex;
    int i;
    Vec_PtrForEachEntry( Abc_Cex_t *, pDb->vCexes, pCex, i )
        Abc_CexFree( pCex );
    Vec_PtrFree( pDb->vCexes );
    Vec_IntFree( pDb->vBatchEnds );
    ABC_FREE( pDb );
}

static int Cec_TranPatDbCexEqual( Abc_Cex_t * p0, Abc_Cex_t * p1 )
{
    return p0->nRegs == p1->nRegs && p0->nPis == p1->nPis &&
        p0->iFrame == p1->iFrame && p0->nBits == p1->nBits &&
        !memcmp( p0->pData, p1->pData,
            sizeof(unsigned) * Abc_BitWordNum(p0->nBits) );
}

static int Cec_TranPatDbAppend( Cec_TranPatDb_t * pDb, Abc_Cex_t * pCex )
{
    Abc_Cex_t * pOld;
    int i;
    Vec_PtrForEachEntry( Abc_Cex_t *, pDb->vCexes, pOld, i )
        if ( Cec_TranPatDbCexEqual(pOld, pCex) )
        {
            pDb->nDup++;
            Abc_CexFree( pCex );
            return 0;
        }
    if ( Vec_PtrSize(pDb->vCexes) >= pDb->nMax )
    {
        Abc_CexFree( pCex );
        return 0;
    }
    Vec_PtrPush( pDb->vCexes, pCex );
    return 1;
}

// Observe scorr's already packed simulation lanes.  Several compatible SAT
// cubes may share one lane; retaining the dense lane preserves that compression
// and avoids solving or simulating again during candidate construction.
static void Cec_TranPatDbObserveScorr( void * pData, Gia_Man_t * pAig,
    Vec_Ptr_t * vSimInfo, Vec_Int_t * vOutBits, int nFrames,
    int fInduction )
{
    Cec_TranPatDb_t * pDb = (Cec_TranPatDb_t *)pData;
    Abc_Cex_t * pCex;
    unsigned * pInfo;
    char * pUsed;
    int i, r, f, iPi, Out, iBit;
    int nRegs = Gia_ManRegNum(pAig);
    int nPis = Gia_ManPiNum(pAig);
    int nBits = 32 * Vec_PtrReadWordsSimInfo(vSimInfo);
    if ( fInduction )
    {
        pDb->nIgnoredInd += Vec_IntSize(vOutBits) / 2;
        return;
    }
    if ( pDb->nFramesMax && nFrames > pDb->nFramesMax )
    {
        pDb->nTooLong += Vec_IntSize(vOutBits) / 2;
        return;
    }
    if ( nPis != pDb->nPis || nRegs != pDb->nRegs )
        return;
    pUsed = ABC_CALLOC( char, nBits );
    for ( i = 0; i + 1 < Vec_IntSize(vOutBits); i += 2 )
    {
        Out = Vec_IntEntry( vOutBits, i );
        iBit = Vec_IntEntry( vOutBits, i + 1 );
        if ( iBit < 0 || iBit >= nBits || pUsed[iBit] )
            continue;
        pUsed[iBit] = 1;
        pDb->nSeen++;
        pCex = Abc_CexAlloc( nRegs, nPis, nFrames );
        pCex->iPo = Out;
        pCex->iFrame = nFrames - 1;
        for ( r = 0; r < nRegs; r++ )
        {
            pInfo = (unsigned *)Vec_PtrEntry( vSimInfo, r );
            if ( Abc_InfoHasBit(pInfo, iBit) )
                Abc_InfoSetBit( pCex->pData, r );
        }
        for ( f = 0; f < nFrames; f++ )
            for ( iPi = 0; iPi < nPis; iPi++ )
            {
                pInfo = (unsigned *)Vec_PtrEntry( vSimInfo,
                    nRegs + f * nPis + iPi );
                if ( Abc_InfoHasBit(pInfo, iBit) )
                    Abc_InfoSetBit( pCex->pData,
                        nRegs + f * nPis + iPi );
            }
        Cec_TranPatDbAppend( pDb, pCex );
    }
    ABC_FREE( pUsed );
}

static void Cec_TranPatDbSeal( Cec_TranPatDb_t * pDb )
{
    int i, nCexes = Vec_PtrSize(pDb->vCexes);
    Vec_IntClear( pDb->vBatchEnds );
    for ( i = 64; i < nCexes; i += 64 )
        Vec_IntPush( pDb->vBatchEnds, i );
    if ( nCexes )
        Vec_IntPush( pDb->vBatchEnds, nCexes );
}

static void Cec_TranPatDbRemapRegs( Cec_TranPatDb_t * pDb,
    int nRegsNew, Vec_Int_t * vNewToOld )
{
    Abc_Cex_t * pOld, * pNew;
    int i, r, f, iPi, iOld;
    assert( vNewToOld == NULL || Vec_IntSize(vNewToOld) == nRegsNew );
    Vec_PtrForEachEntry( Abc_Cex_t *, pDb->vCexes, pOld, i )
    {
        pNew = Abc_CexAlloc( nRegsNew, pOld->nPis, pOld->iFrame + 1 );
        pNew->iPo = pOld->iPo;
        pNew->iFrame = pOld->iFrame;
        for ( r = 0; r < nRegsNew; r++ )
        {
            iOld = vNewToOld ? Vec_IntEntry(vNewToOld, r) : r;
            assert( iOld >= 0 && iOld < pOld->nRegs );
            if ( Abc_InfoHasBit(pOld->pData, iOld) )
                Abc_InfoSetBit( pNew->pData, r );
        }
        for ( f = 0; f <= pOld->iFrame; f++ )
            for ( iPi = 0; iPi < pOld->nPis; iPi++ )
                if ( Abc_InfoHasBit(pOld->pData,
                        pOld->nRegs + f * pOld->nPis + iPi) )
                    Abc_InfoSetBit( pNew->pData,
                        nRegsNew + f * pOld->nPis + iPi );
        Abc_CexFree( pOld );
        Vec_PtrWriteEntry( pDb->vCexes, i, pNew );
    }
    pDb->nRegs = nRegsNew;
}

#include "cecTranStrictCex.h"

static inline word Cec_TranSetLane( word Value, int iLane, int fValue )
{
    word Mask = ((word)1) << iLane;
    return fValue ? (Value | Mask) : (Value & ~Mask);
}

static void Cec_TranPatDbInjectInit( Cec_TranPatDb_t * pDb, Cec_TranSim_t * p )
{
    Abc_Cex_t * pCex;
    int b, c, r, w, iLane, iBeg = 0, iEnd;
    Vec_IntForEachEntry( pDb->vBatchEnds, iEnd, b )
    {
        w = b;
        for ( c = iBeg; c < iEnd; c++ )
        {
            pCex = (Abc_Cex_t *)Vec_PtrEntry( pDb->vCexes, c );
            if ( pCex->nRegs != Gia_ManRegNum(p->pGia) )
                continue;
            iLane = c - iBeg;
            for ( r = 0; r < pCex->nRegs; r++ )
                p->pState[r * p->nWords + w] = Cec_TranSetLane(
                    p->pState[r * p->nWords + w], iLane,
                    Abc_InfoHasBit(pCex->pData, r) );
        }
        iBeg = iEnd;
    }
}

static word Cec_TranPatDbInjectPi( Cec_TranPatDb_t * pDb, int f, int iPi, int w, word Value )
{
    Abc_Cex_t * pCex;
    int b = w, c, iLane, iBeg, iEnd;
    if ( b < 0 || b >= Vec_IntSize(pDb->vBatchEnds) )
        return Value;
    iBeg = b ? Vec_IntEntry(pDb->vBatchEnds, b - 1) : 0;
    iEnd = Vec_IntEntry(pDb->vBatchEnds, b);
    for ( c = iBeg; c < iEnd; c++ )
    {
        pCex = (Abc_Cex_t *)Vec_PtrEntry( pDb->vCexes, c );
        if ( f > pCex->iFrame )
            continue;
        iLane = c - iBeg;
        Value = Cec_TranSetLane( Value, iLane,
            Abc_InfoHasBit(pCex->pData, pCex->nRegs + f * pCex->nPis + iPi) );
    }
    return Value;
}

static inline word * Cec_TranSimObj( Cec_TranSim_t * p, int iObj )
{
    return p->pSims + (size_t)iObj * p->nSlots;
}

static inline word Cec_TranSimLit( Cec_TranSim_t * p, int iLit, int iSlot )
{
    return Cec_TranSimObj(p, Abc_Lit2Var(iLit))[iSlot] ^
        (Abc_LitIsCompl(iLit) ? ~(word)0 : 0);
}

static Cec_TranSim_t * Cec_TranSimStart( Gia_Man_t * pGia, Cec_ParTran_t * pPars,
    Cec_TranPatDb_t * pDb )
{
    Cec_TranSim_t * p;
    Gia_Obj_t * pObj, * pObjRi, * pObjRo;
    int f, w, i, iSlot, iFan0, iFan1;
    word v0, v1;
    p = ABC_CALLOC( Cec_TranSim_t, 1 );
    p->pGia = pGia;
    p->nBudgetWords = pPars->nSimWords;
    // CEX replace random lanes inside Q instead of being appended after Q.
    // Only an overflowing corpus makes the source wider than Build; that
    // wider source is simulated once and root-local batches are gathered from
    // it below.
    p->nWords = Abc_MaxInt( p->nBudgetWords,
        Vec_IntSize(pDb->vBatchEnds) );
    p->nFrames = pPars->nSimFrames;
    // The source simulation is deliberately capped by -W.  A long witness is
    // not allowed to inflate Build's horizon; every retained CEX contributes
    // its complete prefix inside this fixed window.
    p->nSlots = p->nWords * p->nFrames;
    p->pSims = ABC_CALLOC( word, (size_t)Gia_ManObjNum(pGia) * p->nSlots );
    p->pState = ABC_CALLOC( word, (size_t)Gia_ManRegNum(pGia) * p->nWords );
    Cec_TranPatDbInjectInit( pDb, p );
    Abc_RandomW( 1 );
    // Words are simulated outermost.  Each CEX batch occupies the matching
    // word and overwrites only its live bit lanes; unused lanes remain random
    // reset-reachable traces.
    for ( w = 0; w < p->nWords; w++ )
    {
        for ( f = 0; f < p->nFrames; f++ )
        {
            iSlot = f * p->nWords + w;
            Gia_ManForEachPi( pGia, pObj, i )
                Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot] =
                    Cec_TranPatDbInjectPi( pDb, f, i, w,
                        Abc_RandomW(0) );
            Gia_ManForEachRo( pGia, pObj, i )
                Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot] = p->pState[i * p->nWords + w];
            Gia_ManForEachAnd( pGia, pObj, i )
            {
                iFan0 = Gia_ObjFaninId0p( pGia, pObj );
                iFan1 = Gia_ObjFaninId1p( pGia, pObj );
                v0 = Cec_TranSimObj(p, iFan0)[iSlot] ^ (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0);
                v1 = Cec_TranSimObj(p, iFan1)[iSlot] ^ (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0);
                Cec_TranSimObj(p, i)[iSlot] = Gia_ObjIsXor(pObj) ? (v0 ^ v1) : (v0 & v1);
            }
            Gia_ManForEachCo( pGia, pObj, i )
                Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot] =
                    Cec_TranSimLit( p, Gia_ObjFaninLit0p(pGia, pObj), iSlot );
            Gia_ManForEachRiRo( pGia, pObjRi, pObjRo, i )
                p->pState[i * p->nWords + w] =
                    Cec_TranSimObj(p, Gia_ObjId(pGia, pObjRi))[iSlot];
        }
    }
    return p;
}

static void Cec_TranSimStop( Cec_TranSim_t * p )
{
    if ( p == NULL )
        return;
    ABC_FREE( p->pSims );
    ABC_FREE( p->pState );
    ABC_FREE( p->pCiCounts );
    ABC_FREE( p->pObsKeys );
    ABC_FREE( p->pObsLabels );
    ABC_FREE( p );
}

#include "cecTranOdcCare.h"

// Allocate a root-local Q-by-W signature only when the CEX corpus overflows
// the Q trace words.  Each selected trace keeps its bit lane through all W
// frames; this is not a bag of unrelated terminal-frame samples.
static Cec_TranSim_t * Cec_TranSimStartRootBatch( Gia_Man_t * pGia,
    int nWords, int nFrames )
{
    Cec_TranSim_t * p = ABC_CALLOC( Cec_TranSim_t, 1 );
    p->pGia = pGia;
    p->nBudgetWords = p->nWords = nWords;
    p->nFrames = nFrames;
    p->nSlots = nWords * nFrames;
    p->pSims = ABC_CALLOC( word,
        (size_t)Gia_ManObjNum(pGia) * p->nSlots );
    return p;
}

static inline int Cec_TranTeachSampleValue( Cec_TranSim_t * pSim,
    int iObj, int iSample )
{
    return (int)((Cec_TranSimObj(pSim, iObj)[iSample >> 6] >>
        (iSample & 63)) & 1);
}

static inline void Cec_TranTeachCoverAdd( word * pCover, int * piHyp,
    int Value, int Target )
{
    int iHyp = (*piHyp)++;
    if ( Value != Target )
        pCover[iHyp >> 6] |= ((word)1) << (iHyp & 63);
}

static unsigned Cec_TranTeachMix( unsigned x )
{
    x ^= x >> 16;
    x *= 0x7feb352du;
    x ^= x >> 15;
    x *= 0x846ca68bu;
    return x ^ (x >> 16);
}

// When more CEX traces exist than Q words can hold, greedily put the most
// root-relevant traces first.  Relevance is measured over every frame against
// cheap wrong explanations of the root.  Proxy saturation never wastes
// capacity: the remaining lanes are filled by a deterministic root-specific
// spread over all unselected CEX.  Thus exactly min(64*Q, nCexes) complete
// traces are retained.
static int Cec_TranTeachSelectCex( Cec_TranSim_t * pSource,
    Cec_TranPatDb_t * pDb, int iTarget, Vec_Int_t * vPool,
    int nSelectMax, int * pSelected, int * pnHypotheses, int * pnCovered )
{
    enum { CEC_TRAN_TEACH_DIV_MAX = 8 };
    int nDivs = Abc_MinInt( CEC_TRAN_TEACH_DIV_MAX, Vec_IntSize(vPool) );
    int nPairs = nDivs * (nDivs - 1) / 2;
    int nHyps = 2 + 2 * nDivs + 6 * nPairs;
    int nHypWords = (nHyps + 63) / 64;
    int nCexes = Vec_PtrSize(pDb->vCexes);
    word * pCover = ABC_CALLOC( word, (size_t)nCexes * nHypWords );
    word * pDone = ABC_CALLOC( word, nHypWords );
    word * pAll = ABC_CALLOC( word, nHypWords );
    char * pChosen = ABC_CALLOC( char, nCexes );
    int c, f, i, k, d0, d1, iHyp, Target, Value, Best, BestScore;
    int nSelected = 0, nCovered = 0, nDistinguishable = 0;
    nSelectMax = Abc_MinInt( nSelectMax, nCexes );
    for ( c = 0; c < nCexes; c++ )
    {
        Abc_Cex_t * pCex = (Abc_Cex_t *)Vec_PtrEntry(pDb->vCexes, c);
        word * pRow = pCover + (size_t)c * nHypWords;
        int nCexFrames = Abc_MinInt( pSource->nFrames,
            pCex->iFrame + 1 );
        for ( f = 0; f < nCexFrames; f++ )
        {
            int DivValues[CEC_TRAN_TEACH_DIV_MAX];
            int iSample = 64 * (f * pSource->nWords + (c >> 6)) +
                (c & 63);
            Target = Cec_TranTeachSampleValue( pSource, iTarget, iSample );
            for ( i = 0; i < nDivs; i++ )
                DivValues[i] = Cec_TranTeachSampleValue( pSource,
                    Vec_IntEntry(vPool, i), iSample );
            iHyp = 0;
            Cec_TranTeachCoverAdd( pRow, &iHyp, 0, Target );
            Cec_TranTeachCoverAdd( pRow, &iHyp, 1, Target );
            for ( i = 0; i < nDivs; i++ )
            {
                Cec_TranTeachCoverAdd( pRow, &iHyp, DivValues[i], Target );
                Cec_TranTeachCoverAdd( pRow, &iHyp, !DivValues[i], Target );
            }
            for ( d0 = 0; d0 < nDivs; d0++ )
                for ( d1 = d0 + 1; d1 < nDivs; d1++ )
                {
                    Value = DivValues[d0] & DivValues[d1];
                    Cec_TranTeachCoverAdd( pRow, &iHyp, Value, Target );
                    Cec_TranTeachCoverAdd( pRow, &iHyp, !Value, Target );
                    Value = DivValues[d0] | DivValues[d1];
                    Cec_TranTeachCoverAdd( pRow, &iHyp, Value, Target );
                    Cec_TranTeachCoverAdd( pRow, &iHyp, !Value, Target );
                    Value = DivValues[d0] ^ DivValues[d1];
                    Cec_TranTeachCoverAdd( pRow, &iHyp, Value, Target );
                    Cec_TranTeachCoverAdd( pRow, &iHyp, !Value, Target );
                }
            assert( iHyp == nHyps );
        }
        for ( k = 0; k < nHypWords; k++ )
            pAll[k] |= pRow[k];
    }
    for ( i = 0; i < nSelectMax; i++ )
    {
        Best = -1;
        BestScore = 0;
        for ( c = 0; c < nCexes; c++ )
        {
            word * pRow = pCover + (size_t)c * nHypWords;
            int Score = 0;
            if ( pChosen[c] )
                continue;
            for ( k = 0; k < nHypWords; k++ )
                Score += Abc_TtCountOnes( pRow[k] & ~pDone[k] );
            if ( Score > BestScore )
                BestScore = Score, Best = c;
        }
        if ( Best < 0 )
            break;
        pSelected[nSelected++] = Best;
        pChosen[Best] = 1;
        for ( k = 0; k < nHypWords; k++ )
            pDone[k] |= pCover[(size_t)Best * nHypWords + k];
    }
    // Once the cheap proxy is saturated, retain information rather than
    // throwing CEX away.  Rotate the residual corpus by root so small Q values
    // do not force every root to receive the same arbitrary prefix.
    if ( nSelected < nSelectMax )
    {
        int nTried = 0;
        int iStart = nCexes ?
            (int)(Cec_TranTeachMix((unsigned)iTarget) % nCexes) : 0;
        for ( c = iStart; nTried < nCexes && nSelected < nSelectMax;
              c = c + 1 == nCexes ? 0 : c + 1, nTried++ )
            if ( !pChosen[c] )
                pSelected[nSelected++] = c, pChosen[c] = 1;
    }
    for ( k = 0; k < nHypWords; k++ )
        nCovered += Abc_TtCountOnes( pDone[k] ),
        nDistinguishable += Abc_TtCountOnes( pAll[k] );
    *pnHypotheses = nDistinguishable;
    *pnCovered = nCovered;
    ABC_FREE( pCover );
    ABC_FREE( pDone );
    ABC_FREE( pAll );
    ABC_FREE( pChosen );
    return nSelected;
}

typedef struct Cec_TranTeachCache_t_ Cec_TranTeachCache_t;
struct Cec_TranTeachCache_t_
{
    int              nSamples;
    int              nObjs;
    int *            pObjs;
    word *           pSims;
    word *           pCare;       // source care on the identical selected lanes
    Cec_TranSim_t *   pSource;     // immutable snapshot owner; outlives this cache
    int              nSourceWords;
    int              nBuildWords;
    int              nFrames;
};

static void Cec_TranTeachCacheStop( Cec_TranTeachCache_t * pCache )
{
    if ( pCache == NULL )
        return;
    ABC_FREE( pCache->pObjs );
    ABC_FREE( pCache->pSims );
    ABC_FREE( pCache->pCare );
    ABC_FREE( pCache );
}

// Gather complete CEX trace lanes from the once-computed overflowing source
// into a root-local Q-by-W signature.  No graph simulation is performed here.
// The packed result is cached, so later proof waves only copy words.
static void Cec_TranTeachBuildSignature( Cec_TranSim_t * pSource,
    Cec_TranSim_t * pBuild, Cec_TranPatDb_t * pDb, int iTarget,
    Vec_Int_t * vPool, Cec_TranTeachCache_t ** ppCache,
    Cec_TranProf_t * pProf, word const * pCareSource )
{
    Cec_TranTeachCache_t * pCache = *ppCache;
    int * pCexIds;
    int nHypotheses = 0, nCovered = 0;
    int nSelected, nTraceMax = 64 * pBuild->nWords;
    int i, f, d, iObj;
    abctime clk = Abc_Clock();
    assert( pBuild->nFrames == pSource->nFrames );
    if ( pCache == NULL )
    {
        pCache = *ppCache = ABC_CALLOC( Cec_TranTeachCache_t, 1 );
        pCache->nSamples = pBuild->nSlots;
        pCache->pSource = pSource;
        pCache->nSourceWords = pSource->nWords;
        pCache->nBuildWords = pBuild->nWords;
        pCache->nFrames = pBuild->nFrames;
        pCache->nObjs = 1 + Vec_IntSize(vPool);
        pCache->pObjs = ABC_ALLOC( int, pCache->nObjs );
        pCache->pSims = ABC_CALLOC( word,
            (size_t)pCache->nObjs * pBuild->nSlots );
        pCexIds = ABC_ALLOC( int, nTraceMax );
        nSelected = Cec_TranTeachSelectCex( pSource, pDb, iTarget,
            vPool, nTraceMax, pCexIds, &nHypotheses, &nCovered );
        assert( nSelected == Abc_MinInt(nTraceMax,
            Vec_PtrSize(pDb->vCexes)) );
        pProf->nRootTeachSelections++;
        pProf->nRootTeachWithCex += nSelected > 0;
        pProf->nRootTeachCexSelected += nSelected;
        pProf->nRootTeachHypotheses += nHypotheses;
        pProf->nRootTeachHypCovered += nCovered;
        pCache->pObjs[0] = iTarget;
        Vec_IntForEachEntry( vPool, iObj, i )
            pCache->pObjs[i + 1] = iObj;
        for ( i = 0; i < pCache->nObjs; i++ )
        {
            iObj = pCache->pObjs[i];
            for ( d = 0; d < nSelected; d++ )
                for ( f = 0; f < pBuild->nFrames; f++ )
                    if ( Cec_TranTeachSampleValue(pSource, iObj,
                            64 * (f * pSource->nWords +
                                (pCexIds[d] >> 6)) +
                            (pCexIds[d] & 63)) )
                        pCache->pSims[(size_t)i * pBuild->nSlots +
                            f * pBuild->nWords + (d >> 6)] |=
                            ((word)1) << (d & 63);
        }
        // Build only stores target/divisor columns; its fanout side inputs
        // are absent or stale.  Project the original source-care mask before
        // discarding these exact selected CEX IDs, preserving every frame.
        // The packed mask has the same immutable target/pool/source lifetime
        // as the cached columns.  Strict teaching leaves it unallocated.
        if ( pCareSource )
        {
            pCache->pCare = ABC_CALLOC( word, pBuild->nSlots );
            for ( d = 0; d < nSelected; d++ )
                for ( f = 0; f < pBuild->nFrames; f++ )
                    if ( (pCareSource[f * pSource->nWords + (pCexIds[d] >> 6)] >>
                            (pCexIds[d] & 63)) & 1 )
                        pCache->pCare[f * pBuild->nWords + (d >> 6)] |=
                            ((word)1) << (d & 63);
        }
        ABC_FREE( pCexIds );
    }
    assert( pCache->pSource == pSource );
    assert( pCache->nSourceWords == pSource->nWords );
    assert( pCache->nBuildWords == pBuild->nWords );
    assert( pCache->nFrames == pBuild->nFrames );
    assert( (pCache->pCare != NULL) == (pCareSource != NULL) );
    assert( pCache->nSamples == pBuild->nSlots );
    assert( pCache->nObjs == 1 + Vec_IntSize(vPool) );
    assert( pCache->pObjs[0] == iTarget );
    for ( i = 0; i < pCache->nObjs; i++ )
    {
        iObj = i ? Vec_IntEntry(vPool, i - 1) : iTarget;
        assert( pCache->pObjs[i] == iObj );
        memcpy( Cec_TranSimObj(pBuild, iObj),
            pCache->pSims + (size_t)i * pBuild->nSlots,
            sizeof(word) * pBuild->nSlots );
    }
    memset( Cec_TranSimObj(pBuild, 0), 0,
        sizeof(word) * pBuild->nSlots );
    pProf->nRootTeachCalls++;
    pProf->timeRootTeach += Abc_Clock() - clk;
}

// Independent PI/RO simulation used only by the all-state combination lane.
// Reachable signatures intentionally start every trace from reset and cannot
// observe a mismatch confined to an unreachable register state.  Here every
// CI, including every RO, is independent.  CBS SAT models are appended as
// individual lanes and immediately screen later candidates in the same batch.
typedef struct Cec_TranFreeSim_t_ Cec_TranFreeSim_t;
struct Cec_TranFreeSim_t_
{
    Gia_Man_t * pGia;
    int         nBaseWords;
    int         nCexMax;
    int         nCexes;
    int         nWords;
    word *      pSims;          // [object ID][allocated word]
};

static inline word * Cec_TranFreeSimObj( Cec_TranFreeSim_t * p, int iObj )
{
    return p->pSims + (size_t)iObj * p->nWords;
}

static inline word Cec_TranFreeSimLit( Cec_TranFreeSim_t * p, int iLit, int w )
{
    return Cec_TranFreeSimObj(p, Abc_Lit2Var(iLit))[w] ^
        (Abc_LitIsCompl(iLit) ? ~(word)0 : 0);
}

static inline word Cec_TranFreeRandom( word * pState )
{
    word x = *pState;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    return *pState = x;
}

static Cec_TranFreeSim_t * Cec_TranFreeSimStart( Gia_Man_t * pGia,
    int nBaseWords, int nCexMax )
{
    Cec_TranFreeSim_t * p = ABC_CALLOC( Cec_TranFreeSim_t, 1 );
    Gia_Obj_t * pObj;
    word Rand = ABC_CONST(0x9e3779b97f4a7c15), v0, v1;
    int i, w, iFan0, iFan1;
    p->pGia = pGia;
    p->nBaseWords = nBaseWords;
    p->nCexMax = nCexMax;
    p->nWords = nBaseWords + (nCexMax + 63) / 64;
    p->nWords = Abc_MaxInt( p->nWords, 1 );
    p->pSims = ABC_CALLOC( word, (size_t)Gia_ManObjNum(pGia) * p->nWords );
    for ( w = 0; w < nBaseWords; w++ )
    {
        Gia_ManForEachCi( pGia, pObj, i )
            Cec_TranFreeSimObj(p, Gia_ObjId(pGia, pObj))[w] =
                Cec_TranFreeRandom( &Rand );
        Gia_ManForEachAnd( pGia, pObj, i )
        {
            iFan0 = Gia_ObjFaninId0p( pGia, pObj );
            iFan1 = Gia_ObjFaninId1p( pGia, pObj );
            v0 = Cec_TranFreeSimObj(p, iFan0)[w] ^
                (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0);
            v1 = Cec_TranFreeSimObj(p, iFan1)[w] ^
                (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0);
            Cec_TranFreeSimObj(p, i)[w] = Gia_ObjIsXor(pObj) ?
                (v0 ^ v1) : (v0 & v1);
        }
    }
    return p;
}

static void Cec_TranFreeSimStop( Cec_TranFreeSim_t * p )
{
    if ( p == NULL )
        return;
    ABC_FREE( p->pSims );
    ABC_FREE( p );
}

// Return 1 for an initial-random mismatch and 2 for a mismatch first exposed
// by an appended CBS model.  Unused lanes in the last CEX word are masked.
static int Cec_TranFreeSimMismatch( Cec_TranFreeSim_t * p, int iLit0, int iLit1 )
{
    word Diff, Mask;
    int w, nValid;
    if ( p == NULL )
        return 0;
    for ( w = 0; w < p->nBaseWords; w++ )
        if ( Cec_TranFreeSimLit(p, iLit0, w) !=
             Cec_TranFreeSimLit(p, iLit1, w) )
            return 1;
    for ( w = 0; w < (p->nCexes + 63) / 64; w++ )
    {
        nValid = Abc_MinInt( 64, p->nCexes - 64 * w );
        Mask = nValid == 64 ? ~(word)0 : ((((word)1) << nValid) - 1);
        Diff = (Cec_TranFreeSimLit(p, iLit0, p->nBaseWords + w) ^
                Cec_TranFreeSimLit(p, iLit1, p->nBaseWords + w)) & Mask;
        if ( Diff )
            return 2;
    }
    return 0;
}

// Append one CBS model as a free-state lane.  CBS reports only assigned CIs;
// unreported CIs are don't-cares and are completed with zero.  Scalar
// resimulation validates that this completion still separates the candidate
// before the lane becomes visible to later signature checks.
static int Cec_TranFreeSimAddModel( Cec_TranFreeSim_t * p, Vec_Int_t * vModel,
    int iLit0, int iLit1 )
{
    Gia_Man_t * pGia;
    Gia_Obj_t * pObj;
    word Mask, v0, v1;
    int i, iModel, iCi, iObj, iFan0, iFan1, w;
    if ( p == NULL || p->nCexes >= p->nCexMax )
        return 0;
    pGia = p->pGia;
    w = p->nBaseWords + p->nCexes / 64;
    Mask = ((word)1) << (p->nCexes & 63);
    Gia_ManForEachObj( pGia, pObj, i )
        Cec_TranFreeSimObj(p, i)[w] &= ~Mask;
    Vec_IntForEachEntry( vModel, iModel, i )
    {
        iCi = Abc_Lit2Var( iModel );
        if ( iCi < 0 || iCi >= Gia_ManCiNum(pGia) || Abc_LitIsCompl(iModel) )
            continue;
        iObj = Gia_ObjId( pGia, Gia_ManCi(pGia, iCi) );
        Cec_TranFreeSimObj(p, iObj)[w] |= Mask;
    }
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        iFan0 = Gia_ObjFaninId0p( pGia, pObj );
        iFan1 = Gia_ObjFaninId1p( pGia, pObj );
        v0 = Cec_TranFreeSimObj(p, iFan0)[w] ^
            (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0);
        v1 = Cec_TranFreeSimObj(p, iFan1)[w] ^
            (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0);
        if ( (Gia_ObjIsXor(pObj) ? (v0 ^ v1) : (v0 & v1)) & Mask )
            Cec_TranFreeSimObj(p, i)[w] |= Mask;
    }
    if ( !((Cec_TranFreeSimLit(p, iLit0, w) ^
            Cec_TranFreeSimLit(p, iLit1, w)) & Mask) )
        return 0;
    p->nCexes++;
    return 1;
}

#include "cecTranOdcCareTest.h"
