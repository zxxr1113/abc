/**CFile****************************************************************

  FileName    [cecCorrIncrSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Persistent failed-endpoint TFO incremental simulation for &scorr.]

  Description [Keeps dense storage for every (frame, object) key.  SAT endpoint
  values seed a frame-aware TFO walk.  Values needed by this TFO and its
  affected classes are recomputed on demand from the current packed CEX inputs;
  values from earlier batches are never consumed as side inputs.  Wide cones
  fall back to the standard full sweep.]

  Author      [Xiran Zhao]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Jun 2026.]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline int Cec_SeedSimKey( Cec_SeedSim_t * p, int frame, int objId )
{
    return frame * p->nObjs + objId;
}

static inline unsigned * Cec_SeedSimVal( Cec_SeedSim_t * p, int frame, int objId )
{
    size_t Key = (size_t)Cec_SeedSimKey( p, frame, objId );
    return p->pVal + Key * p->nWords;
}

static inline int Cec_SeedSimMark( Cec_SeedSim_t * p, int frame, int objId )
{
    int Key = Cec_SeedSimKey( p, frame, objId );
    if ( p->pMark[Key] == p->nMarkVersion )
        return 0;
    p->pMark[Key] = p->nMarkVersion;
    Vec_IntPush( p->vDirtyKeys, Key );
    return 1;
}

static inline void Cec_SeedSimCopyWords( unsigned * pDst, unsigned * pSrc, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        pDst[w] = pSrc[w];
}

static int Cec_SeedSimEvalWord( Cec_SeedSim_t * p, int Frame, int ObjId, int iWord, unsigned Mask, int nLimit )
{
    Gia_Man_t * pAig = p->pAig;
    Gia_Obj_t * pObj = Gia_ManObj( pAig, ObjId );
    int Key = Cec_SeedSimKey( p, Frame, ObjId );
    unsigned * pRes = Cec_SeedSimVal( p, Frame, ObjId );
    unsigned * pDone = p->pEvalMask + (size_t)Key * p->nWords;
    unsigned Missing, Normal, SeedMask = 0, SeedValue = 0, Value = 0;
    int iSeed = p->pSeedMark[Key] - 1;
    if ( Mask == 0 )
        return 1;
    if ( p->pEvalMark[Key] != p->nEvalVersion )
    {
        int Phase = pRes[0] & 1;
        int w;
        if ( ++p->nEvalKeys > nLimit )
            return 0;
        p->pEvalMark[Key] = p->nEvalVersion;
        for ( w = 0; w < p->nWords; w++ )
        {
            pRes[w] = Phase ? ~(unsigned)0 : 0;
            pDone[w] = 0;
        }
    }
    Missing = Mask & ~pDone[iWord];
    if ( Missing == 0 )
        return 1;
    if ( iSeed >= 0 )
    {
        SeedMask  = ((unsigned *)Vec_IntArray(p->vSeedMasks)) [(size_t)iSeed * p->nWords + iWord];
        SeedValue = ((unsigned *)Vec_IntArray(p->vSeedValues))[(size_t)iSeed * p->nWords + iWord];
    }
    Normal = Missing & ~SeedMask;
    if ( Normal )
    {
        if ( ObjId == 0 )
            Value = 0;
        else if ( Gia_ObjIsPi(pAig, pObj) )
        {
            int iPi = Gia_ObjCioId( pObj );
            unsigned * pInput = (unsigned *)Vec_PtrEntry( p->vBatchInfo,
                p->nRegs + Frame * p->nPis + iPi );
            Value = pInput[iWord];
        }
        else if ( Gia_ObjIsRo(pAig, pObj) )
        {
            if ( Frame == 0 )
            {
                int iReg = Gia_ObjCioId(pObj) - p->nPis;
                unsigned * pInput = (unsigned *)Vec_PtrEntry( p->vBatchInfo, iReg );
                Value = pInput[iWord];
            }
            else
            {
                Gia_Obj_t * pRi = Gia_ObjRoToRi( pAig, pObj );
                int RiId = Gia_ObjId( pAig, pRi );
                int DrvId = Gia_ObjFaninId0( pRi, RiId );
                if ( !Cec_SeedSimEvalWord(p, Frame - 1, DrvId, iWord, Normal, nLimit) )
                    return 0;
                Value = Cec_SeedSimVal(p, Frame - 1, DrvId)[iWord];
                if ( Gia_ObjFaninC0(pRi) )
                    Value = ~Value;
            }
        }
        else if ( Gia_ObjIsAnd(pObj) )
        {
            int Fan0 = Gia_ObjFaninId0( pObj, ObjId );
            int Fan1 = Gia_ObjFaninId1( pObj, ObjId );
            unsigned Val0, Val1;
            if ( !Cec_SeedSimEvalWord(p, Frame, Fan0, iWord, Normal, nLimit) ||
                 !Cec_SeedSimEvalWord(p, Frame, Fan1, iWord, Normal, nLimit) )
                return 0;
            Val0 = Cec_SeedSimVal(p, Frame, Fan0)[iWord];
            Val1 = Cec_SeedSimVal(p, Frame, Fan1)[iWord];
            if ( Gia_ObjFaninC0(pObj) )
                Val0 = ~Val0;
            if ( Gia_ObjFaninC1(pObj) )
                Val1 = ~Val1;
            Value = Val0 & Val1;
        }
        else
            return 0;
        pRes[iWord] = (pRes[iWord] & ~Normal) | (Value & Normal);
    }
    SeedMask &= Missing;
    pRes[iWord] = (pRes[iWord] & ~SeedMask) | (SeedValue & SeedMask);
    pDone[iWord] |= Missing;
    return 1;
}

static int Cec_SeedSimEvalActive( Cec_SeedSim_t * p, int Frame, int ObjId, int nLimit )
{
    int w;
    for ( w = 0; w < p->nWords; w++ )
        if ( p->pActiveMask[w] &&
             !Cec_SeedSimEvalWord(p, Frame, ObjId, w, p->pActiveMask[w], nLimit) )
            return 0;
    return 1;
}

Cec_SeedSim_t * Cec_SeedSimAlloc( Gia_Man_t * pAig, int nFrames, int iSeedFrame, int nWords )
{
    Cec_SeedSim_t * p = ABC_CALLOC( Cec_SeedSim_t, 1 );
    size_t nKeys = (size_t)nFrames * Gia_ManObjNum(pAig);
    int w;
    assert( iSeedFrame >= 0 && iSeedFrame < nFrames );
    p->pAig    = pAig;
    p->nFrames = nFrames;
    p->iSeedFrame = iSeedFrame;
    p->nObjs   = Gia_ManObjNum( pAig );
    p->nPis    = Gia_ManPiNum( pAig );
    p->nRegs   = Gia_ManRegNum( pAig );
    p->nWords  = nWords;
    p->pVal         = ABC_CALLOC( unsigned, nKeys * nWords );
    p->pEvalMask    = ABC_CALLOC( unsigned, nKeys * nWords );
    p->pActiveMask  = ABC_CALLOC( unsigned, nWords );
    p->pMark        = ABC_CALLOC( int, nKeys );
    p->pSeedMark    = ABC_CALLOC( int, nKeys );
    p->pEvalMark    = ABC_CALLOC( int, nKeys );
    p->pRootMark    = ABC_CALLOC( int, p->nObjs );
    p->vDirtyKeys   = Vec_IntAlloc( 4096 );
    p->vQueue       = Vec_IntAlloc( 4096 );
    p->vSeedKeys    = Vec_IntAlloc( 64 );
    p->vSeedMasks   = Vec_IntAlloc( 64 * nWords );
    p->vSeedValues  = Vec_IntAlloc( 64 * nWords );
    p->vDirtyRoots  = Vec_IntAlloc( 1024 );
    p->vConstRefined = Vec_IntAlloc( 64 );
    p->vClassOld    = Vec_IntAlloc( 64 );
    p->vClassNew    = Vec_IntAlloc( 64 );
    p->pPhase0      = ABC_ALLOC( unsigned, nWords );
    p->pPhase1      = ABC_ALLOC( unsigned, nWords );
    for ( w = 0; w < nWords; w++ )
    {
        p->pPhase0[w] = 0;
        p->pPhase1[w] = ~(unsigned)0;
    }
    if ( pAig->vFanout == NULL )
    {
        Gia_ManStaticFanoutStart( pAig );
        p->fOwnsFanout = 1;
    }
    return p;
}

void Cec_SeedSimFree( Cec_SeedSim_t * p )
{
    if ( p == NULL )
        return;
    if ( p->fOwnsFanout )
        Gia_ManStaticFanoutStop( p->pAig );
    Vec_IntFreeP( &p->vDirtyKeys );
    Vec_IntFreeP( &p->vQueue );
    Vec_IntFreeP( &p->vSeedKeys );
    Vec_IntFreeP( &p->vSeedMasks );
    Vec_IntFreeP( &p->vSeedValues );
    Vec_IntFreeP( &p->vDirtyRoots );
    Vec_IntFreeP( &p->vConstRefined );
    Vec_IntFreeP( &p->vClassOld );
    Vec_IntFreeP( &p->vClassNew );
    Vec_PtrFreeP( &p->vSimInfo );
    ABC_FREE( p->pVal );
    ABC_FREE( p->pEvalMask );
    ABC_FREE( p->pActiveMask );
    ABC_FREE( p->pMark );
    ABC_FREE( p->pSeedMark );
    ABC_FREE( p->pEvalMark );
    ABC_FREE( p->pRootMark );
    ABC_FREE( p->pPhase0 );
    ABC_FREE( p->pPhase1 );
    ABC_FREE( p );
}

static void Cec_SeedSimReset( Cec_SeedSim_t * p )
{
    int i, Key;
    Vec_IntForEachEntry( p->vSeedKeys, Key, i )
        p->pSeedMark[Key] = 0;
    Vec_IntClear( p->vDirtyKeys );
    Vec_IntClear( p->vQueue );
    Vec_IntClear( p->vSeedKeys );
    Vec_IntClear( p->vSeedMasks );
    Vec_IntClear( p->vSeedValues );
    memset( p->pActiveMask, 0, sizeof(unsigned) * p->nWords );
    p->vBatchInfo = NULL;
    p->nEvalKeys = 0;
    p->nMarkVersion++;
    p->nEvalVersion++;
    if ( p->nMarkVersion == 0 )
    {
        memset( p->pMark, 0, sizeof(int) * (size_t)p->nFrames * p->nObjs );
        p->nMarkVersion = 1;
    }
    if ( p->nEvalVersion == 0 )
    {
        memset( p->pEvalMark, 0, sizeof(int) * (size_t)p->nFrames * p->nObjs );
        p->nEvalVersion = 1;
    }
}

static inline void Cec_SeedSimSetBit( unsigned * pInfo, int iBit, int Value )
{
    if ( Abc_InfoHasBit( pInfo, iBit ) != Value )
        Abc_InfoXorBit( pInfo, iBit );
}

static int Cec_SeedSimAddSourceBit( Cec_SeedSim_t * p, int ObjId, int iBit, int Value )
{
    int Key, iSeed, w;
    unsigned * pMask, * pValue;
    if ( ObjId == 0 )
        return Value == 0;
    if ( ObjId < 0 || ObjId >= p->nObjs || Value < 0 )
        return 0;
    Key = Cec_SeedSimKey( p, p->iSeedFrame, ObjId );
    iSeed = p->pSeedMark[Key] - 1;
    if ( iSeed < 0 )
    {
        iSeed = Vec_IntSize( p->vSeedKeys );
        Vec_IntPush( p->vSeedKeys, Key );
        for ( w = 0; w < p->nWords; w++ )
        {
            Vec_IntPush( p->vSeedMasks, 0 );
            Vec_IntPush( p->vSeedValues, 0 );
        }
        p->pSeedMark[Key] = iSeed + 1;
    }
    pMask  = (unsigned *)Vec_IntArray(p->vSeedMasks)  + (size_t)iSeed * p->nWords;
    pValue = (unsigned *)Vec_IntArray(p->vSeedValues) + (size_t)iSeed * p->nWords;
    if ( Abc_InfoHasBit(pMask, iBit) )
        return Abc_InfoHasBit(pValue, iBit) == Value;
    Abc_InfoSetBit( pMask, iBit );
    Cec_SeedSimSetBit( pValue, iBit, Value );
    Abc_InfoSetBit( p->pActiveMask, iBit );
    if ( Cec_SeedSimMark( p, p->iSeedFrame, ObjId ) )
        Vec_IntPush( p->vQueue, Key );
    return 1;
}

static int Cec_SeedSimCollectEndpointSources( Cec_SeedSim_t * p, Vec_Int_t * vOutputs, Vec_Int_t * vOutVals, Vec_Int_t * vOutBits )
{
    int i, Out, iBit;
    if ( vOutputs == NULL || vOutVals == NULL || vOutBits == NULL )
        return 0;
    if ( Vec_IntSize(vOutputs) > Vec_IntSize(vOutVals) )
        return 0;
    Vec_IntForEachEntryDouble( vOutBits, Out, iBit, i )
    {
        int Obj0, Obj1, Val0, Val1;
        if ( Out < 0 || 2*Out + 1 >= Vec_IntSize(vOutputs) ||
             2*Out + 1 >= Vec_IntSize(vOutVals) )
            return 0;
        Obj0 = Vec_IntEntry( vOutputs, 2*Out );
        Obj1 = Vec_IntEntry( vOutputs, 2*Out + 1 );
        Val0 = Vec_IntEntry( vOutVals, 2*Out );
        Val1 = Vec_IntEntry( vOutVals, 2*Out + 1 );
        if ( Val0 < 0 || Val1 < 0 )
            return 0;
        if ( !Cec_SeedSimAddSourceBit( p, Obj0, iBit, Val0 ) )
            return 0;
        if ( !Cec_SeedSimAddSourceBit( p, Obj1, iBit, Val1 ) )
            return 0;
    }
    return 1;
}

static int Cec_SeedSimComputeTfo( Cec_SeedSim_t * p, int nLimit )
{
    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
        return 0;
    while ( Vec_IntSize(p->vQueue) > 0 )
    {
        int Key = Vec_IntPop( p->vQueue );
        int Frame = Key / p->nObjs;
        int ObjId = Key % p->nObjs;
        int FanId, i;
        Gia_ObjForEachFanoutStaticId( p->pAig, ObjId, FanId, i )
        {
            Gia_Obj_t * pFan = Gia_ManObj( p->pAig, FanId );
            if ( Gia_ObjIsAnd(pFan) )
            {
                if ( Cec_SeedSimMark( p, Frame, FanId ) )
                {
                    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
                        return 0;
                    Vec_IntPush( p->vQueue, Cec_SeedSimKey(p, Frame, FanId) );
                }
            }
            else if ( Gia_ObjIsRi(p->pAig, pFan) && Frame + 1 < p->nFrames )
            {
                int RoId = Gia_ObjRiToRoId( p->pAig, FanId );
                if ( Cec_SeedSimMark( p, Frame + 1, RoId ) )
                {
                    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
                        return 0;
                    Vec_IntPush( p->vQueue, Cec_SeedSimKey(p, Frame + 1, RoId) );
                }
            }
        }
    }
    return 1;
}

static void Cec_SeedSimStartRootSet( Cec_SeedSim_t * p )
{
    p->nRootVersion++;
    if ( p->nRootVersion == 0 )
    {
        memset( p->pRootMark, 0, sizeof(int) * p->nObjs );
        p->nRootVersion = 1;
    }
    Vec_IntClear( p->vDirtyRoots );
}

static void Cec_SeedSimAddDirtyRoot( Cec_SeedSim_t * p, int ObjId )
{
    Gia_Man_t * pAig = p->pAig;
    int iRoot;
    if ( !Gia_ObjIsClass(pAig, ObjId) )
        return;
    iRoot = Gia_ObjIsHead(pAig, ObjId) ? ObjId : Gia_ObjRepr(pAig, ObjId);
    if ( p->pRootMark[iRoot] == p->nRootVersion )
        return;
    p->pRootMark[iRoot] = p->nRootVersion;
    Vec_IntPush( p->vDirtyRoots, iRoot );
}

static int Cec_SeedSimPrepareFrame( Cec_SeedSim_t * p, int Frame, int iLo, int iHi, int nLimit )
{
    Gia_Man_t * pAig = p->pAig;
    int i, Ent;
    Cec_SeedSimStartRootSet( p );
    for ( i = iLo; i < iHi; i++ )
    {
        int ObjId = Vec_IntEntry(p->vDirtyKeys, i) % p->nObjs;
        if ( !Cec_SeedSimEvalActive(p, Frame, ObjId, nLimit) )
            return 0;
        Cec_SeedSimAddDirtyRoot( p, ObjId );
    }
    Vec_IntForEachEntry( p->vDirtyRoots, Ent, i )
    {
        int Member;
        if ( !Cec_SeedSimEvalActive(p, Frame, Ent, nLimit) )
            return 0;
        Gia_ClassForEachObj1( pAig, Ent, Member )
        {
            if ( !Cec_SeedSimEvalActive(p, Frame, Member, nLimit) )
                return 0;
        }
    }
    return 1;
}

static void Cec_SeedSimRefineClass( Cec_SeedSim_t * p, int Frame, int iRoot )
{
    unsigned * pSim0;
    int Ent;
    Vec_IntClear( p->vClassOld );
    Vec_IntClear( p->vClassNew );
    Vec_IntPush( p->vClassOld, iRoot );
    pSim0 = Cec_SeedSimVal( p, Frame, iRoot );
    Gia_ClassForEachObj1( p->pAig, iRoot, Ent )
    {
        unsigned * pSim1 = Cec_SeedSimVal( p, Frame, Ent );
        if ( Cec_ManSimCompareEqual( pSim0, pSim1, p->nWords ) )
            Vec_IntPush( p->vClassOld, Ent );
        else
            Vec_IntPush( p->vClassNew, Ent );
    }
    if ( Vec_IntSize(p->vClassNew) == 0 )
        return;
    Cec_ManSimClassCreate( p->pAig, p->vClassOld );
    Cec_ManSimClassCreate( p->pAig, p->vClassNew );
    if ( Vec_IntSize(p->vClassNew) > 1 )
        Cec_SeedSimRefineClass( p, Frame, Vec_IntEntry(p->vClassNew, 0) );
}

static void Cec_SeedSimProcessRefinedConstants( Cec_SeedSim_t * p, Cec_ManSim_t * pSim, int Frame )
{
    Gia_Man_t * pAig = p->pAig;
    int * pTable;
    int i, k, Key, iPrev, nTableSize;
    if ( Vec_IntSize(p->vConstRefined) == 0 )
        return;
    if ( pSim->pPars->fConstCorr )
    {
        Vec_IntForEachEntry( p->vConstRefined, i, k )
            Gia_ObjSetRepr( pAig, i, GIA_VOID );
        return;
    }
    nTableSize = Abc_PrimeCudd( 100 + Vec_IntSize(p->vConstRefined) / 3 );
    pTable = ABC_CALLOC( int, nTableSize );
    Vec_IntForEachEntry( p->vConstRefined, i, k )
    {
        assert( Gia_ObjRepr(pAig, i) == 0 );
        assert( Gia_ObjNext(pAig, i) == 0 );
        Key = Cec_ManSimHashKey( Cec_SeedSimVal(p, Frame, i), p->nWords, nTableSize );
        iPrev = pTable[Key];
        if ( iPrev == 0 )
            Gia_ObjSetRepr( pAig, i, GIA_VOID );
        else
        {
            assert( iPrev < i );
            Gia_ObjSetNext( pAig, iPrev, i );
            Gia_ObjSetRepr( pAig, i, Gia_ObjRepr(pAig, iPrev) );
            if ( Gia_ObjRepr(pAig, i) == GIA_VOID )
                Gia_ObjSetRepr( pAig, i, iPrev );
        }
        pTable[Key] = i;
    }
    Vec_IntForEachEntry( p->vConstRefined, i, k )
        if ( Gia_ObjIsHead(pAig, i) )
            Cec_SeedSimRefineClass( p, Frame, i );
    ABC_FREE( pTable );
}

static void Cec_SeedSimRefineFrame( Cec_SeedSim_t * p, Cec_ManSim_t * pSim, int Frame, int iLo, int iHi )
{
    Gia_Man_t * pAig = p->pAig;
    int i, Ent;
    Cec_SeedSimStartRootSet( p );
    Vec_IntClear( p->vConstRefined );
    for ( i = iLo; i < iHi; i++ )
    {
        int ObjId = Vec_IntEntry(p->vDirtyKeys, i) % p->nObjs;
        if ( Gia_ObjIsConst(pAig, ObjId) )
        {
            unsigned * pVal = Cec_SeedSimVal( p, Frame, ObjId );
            unsigned * pPhase = Gia_ObjPhase(Gia_ManObj(pAig, ObjId)) ? p->pPhase1 : p->pPhase0;
            if ( !Cec_ManSimCompareEqual( pVal, pPhase, p->nWords ) )
                Vec_IntPush( p->vConstRefined, ObjId );
            continue;
        }
        Cec_SeedSimAddDirtyRoot( p, ObjId );
    }
    Vec_IntForEachEntry( p->vDirtyRoots, Ent, i )
        if ( Gia_ObjIsHead(pAig, Ent) )
            Cec_SeedSimRefineClass( p, Frame, Ent );
    Cec_SeedSimProcessRefinedConstants( p, pSim, Frame );
}

int Cec_SeedSimTryBatch( Cec_SeedSim_t * p, Cec_ManSim_t * pSim, Vec_Ptr_t * vSimInfo, Vec_Int_t * vOutputs, Vec_Int_t * vOutVals, Vec_Int_t * vOutBits, int nFrames )
{
    ABC_INT64_T nKeys = (ABC_INT64_T)p->nFrames * p->nObjs;
    int nLimit = (int)(nKeys * CEC_SEEDSIM_FRAC_NUM / CEC_SEEDSIM_FRAC_DEN);
    int nDirty, iLo;
    assert( nFrames == p->nFrames );
    assert( Vec_PtrSize(vSimInfo) == p->nRegs + p->nPis * p->nFrames );
    assert( Vec_PtrReadWordsSimInfo(vSimInfo) == p->nWords );
    if ( !p->fInitialized )
    {
        p->nBatchFull++;
        return 0;
    }
    Cec_SeedSimReset( p );
    p->vBatchInfo = vSimInfo;
    if ( !Cec_SeedSimCollectEndpointSources( p, vOutputs, vOutVals, vOutBits ) )
    {
        p->vBatchInfo = NULL;
        p->nBatchFull++;
        return 0;
    }
    if ( !Cec_SeedSimComputeTfo( p, nLimit ) )
    {
        nDirty = Vec_IntSize( p->vDirtyKeys );
        if ( nDirty > p->nMaxDirty )
            p->nMaxDirty = nDirty;
        p->vBatchInfo = NULL;
        p->nBatchFull++;
        return 0;
    }
    nDirty = Vec_IntSize( p->vDirtyKeys );
    if ( nDirty > p->nMaxDirty )
        p->nMaxDirty = nDirty;
    if ( nDirty == 0 )
    {
        p->vBatchInfo = NULL;
        p->nBatchLocal++;
        return 1;
    }
    Vec_IntSort( p->vDirtyKeys, 0 );
    iLo = 0;
    while ( iLo < Vec_IntSize(p->vDirtyKeys) )
    {
        int Frame = Vec_IntEntry(p->vDirtyKeys, iLo) / p->nObjs;
        int iHi = iLo;
        while ( iHi < Vec_IntSize(p->vDirtyKeys) &&
                Vec_IntEntry(p->vDirtyKeys, iHi) / p->nObjs == Frame )
            iHi++;
        if ( !Cec_SeedSimPrepareFrame(p, Frame, iLo, iHi, nLimit) )
        {
            if ( p->nEvalKeys > p->nMaxDirty )
                p->nMaxDirty = p->nEvalKeys;
            p->vBatchInfo = NULL;
            p->nBatchFull++;
            return 0;
        }
        Cec_SeedSimRefineFrame( p, pSim, Frame, iLo, iHi );
        iLo = iHi;
    }
    if ( p->nEvalKeys > p->nMaxDirty )
        p->nMaxDirty = p->nEvalKeys;
    p->vBatchInfo = NULL;
    p->nBatchLocal++;
    return 1;
}

void Cec_SeedSimSaveFrameInputs( Cec_SeedSim_t * p, Vec_Ptr_t * vInfoCis, int Frame )
{
    Gia_Obj_t * pObj;
    int i, w;
    unsigned * pConst;
    assert( Frame >= 0 && Frame < p->nFrames );
    assert( Vec_PtrSize(vInfoCis) == p->nPis + p->nRegs );
    assert( Vec_PtrReadWordsSimInfo(vInfoCis) == p->nWords );
    pConst = Cec_SeedSimVal( p, Frame, 0 );
    for ( w = 0; w < p->nWords; w++ )
        pConst[w] = 0;
    Gia_ManForEachCi( p->pAig, pObj, i )
    {
        unsigned * pDst = Cec_SeedSimVal( p, Frame, Gia_ObjId(p->pAig, pObj) );
        unsigned * pSrc = (unsigned *)Vec_PtrEntry( vInfoCis, i );
        Cec_SeedSimCopyWords( pDst, pSrc, p->nWords );
        pDst[0] &= ~(unsigned)1;
    }
}

void Cec_SeedSimSaveFrameOutputs( Cec_SeedSim_t * p, Vec_Ptr_t * vInfoCos, int Frame )
{
    Gia_Obj_t * pObj;
    int i;
    assert( Frame >= 0 && Frame < p->nFrames );
    assert( Vec_PtrSize(vInfoCos) == Gia_ManCoNum(p->pAig) );
    assert( Vec_PtrReadWordsSimInfo(vInfoCos) == p->nWords );
    Gia_ManForEachCo( p->pAig, pObj, i )
        Cec_SeedSimCopyWords( Cec_SeedSimVal(p, Frame, Gia_ObjId(p->pAig, pObj)),
                             (unsigned *)Vec_PtrEntry(vInfoCos, i), p->nWords );
}

void Cec_SeedSimFinishFull( Cec_SeedSim_t * p )
{
    p->fInitialized = 1;
}

void Cec_SeedSimBeginCall( Cec_SeedSim_t * p )
{
    p->nBatchLocal = p->nBatchFull = p->nMaxDirty = 0;
}

int Cec_SeedSimNumLocal( Cec_SeedSim_t * p ) { return p->nBatchLocal; }
int Cec_SeedSimNumFull ( Cec_SeedSim_t * p ) { return p->nBatchFull; }
int Cec_SeedSimNumDirty( Cec_SeedSim_t * p ) { return p->nMaxDirty; }
int Cec_SeedSimNumKeys ( Cec_SeedSim_t * p ) { return p->nFrames * p->nObjs; }

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
