/**CFile****************************************************************

  FileName    [cecCorrIncrSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [CEX-diagnosis and split-TFO incremental simulation for &scorr.]

  Description [Traces each failed SRM output through the speculative equivalence
  assumptions used to build it.  Host-AIG values are evaluated on demand from
  the current packed CEX inputs.  Assumptions that are false under a CEX split
  their host classes; only these real splits seed a frame-aware TFO search for
  additional refinements.  Unexplained CEX lanes and wide cones fall back to
  the standard full sweep.]

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
    assert( frame >= 0 && frame < p->nFrames );
    assert( objId >= 0 && objId < p->nObjs );
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

static int Cec_SeedSimEvalActive( Cec_SeedSim_t * p, int Frame, int ObjId, int nLimit )
{
    Gia_Man_t * pAig = p->pAig;
    Gia_Obj_t * pObj = Gia_ManObj( pAig, ObjId );
    int Key = Cec_SeedSimKey( p, Frame, ObjId );
    unsigned * pRes = Cec_SeedSimVal( p, Frame, ObjId );
    int Phase, w;
    if ( p->pEvalMark[Key] == p->nEvalVersion )
        return 1;
    if ( ++p->nEvalKeys > nLimit )
        return 0;
    p->pEvalMark[Key] = p->nEvalVersion;
    Phase = pRes[0] & 1;
    for ( w = 0; w < p->nWords; w++ )
        pRes[w] = Phase ? ~(unsigned)0 : 0;
    if ( ObjId == 0 )
        return 1;
    if ( Gia_ObjIsPi(pAig, pObj) )
    {
        int iPi = Gia_ObjCioId( pObj );
        unsigned * pInput = (unsigned *)Vec_PtrEntry( p->vBatchInfo,
            p->nRegs + Frame * p->nPis + iPi );
        for ( w = 0; w < p->nWords; w++ )
            pRes[w] = (pRes[w] & ~p->pActiveMask[w]) |
                      (pInput[w] & p->pActiveMask[w]);
        return 1;
    }
    if ( Gia_ObjIsRo(pAig, pObj) )
    {
        if ( Frame == 0 )
        {
            int iReg = Gia_ObjCioId(pObj) - p->nPis;
            unsigned * pInput = (unsigned *)Vec_PtrEntry( p->vBatchInfo, iReg );
            for ( w = 0; w < p->nWords; w++ )
                pRes[w] = (pRes[w] & ~p->pActiveMask[w]) |
                          (pInput[w] & p->pActiveMask[w]);
        }
        else
        {
            Gia_Obj_t * pRi = Gia_ObjRoToRi( pAig, pObj );
            int RiId = Gia_ObjId( pAig, pRi );
            int DrvId = Gia_ObjFaninId0( pRi, RiId );
            unsigned * pDrv;
            if ( !Cec_SeedSimEvalActive(p, Frame - 1, DrvId, nLimit) )
                return 0;
            pDrv = Cec_SeedSimVal( p, Frame - 1, DrvId );
            for ( w = 0; w < p->nWords; w++ )
            {
                unsigned Value = Gia_ObjFaninC0(pRi) ? ~pDrv[w] : pDrv[w];
                pRes[w] = (pRes[w] & ~p->pActiveMask[w]) |
                          (Value & p->pActiveMask[w]);
            }
        }
        return 1;
    }
    if ( Gia_ObjIsAnd(pObj) )
    {
        int Fan0 = Gia_ObjFaninId0( pObj, ObjId );
        int Fan1 = Gia_ObjFaninId1( pObj, ObjId );
        unsigned * pVal0, * pVal1;
        if ( !Cec_SeedSimEvalActive(p, Frame, Fan0, nLimit) ||
             !Cec_SeedSimEvalActive(p, Frame, Fan1, nLimit) )
            return 0;
        pVal0 = Cec_SeedSimVal( p, Frame, Fan0 );
        pVal1 = Cec_SeedSimVal( p, Frame, Fan1 );
        for ( w = 0; w < p->nWords; w++ )
        {
            unsigned Val0 = Gia_ObjFaninC0(pObj) ? ~pVal0[w] : pVal0[w];
            unsigned Val1 = Gia_ObjFaninC1(pObj) ? ~pVal1[w] : pVal1[w];
            unsigned Value = Val0 & Val1;
            pRes[w] = (pRes[w] & ~p->pActiveMask[w]) |
                      (Value & p->pActiveMask[w]);
        }
        return 1;
    }
    return 0;
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
    p->pActiveMask  = ABC_CALLOC( unsigned, nWords );
    p->pCexMask     = ABC_CALLOC( unsigned, nWords );
    p->pFoundMask   = ABC_CALLOC( unsigned, nWords );
    p->pDiffMask    = ABC_CALLOC( unsigned, nWords );
    p->pTempMask    = ABC_CALLOC( unsigned, nWords );
    p->pMark        = ABC_CALLOC( int, nKeys );
    p->pSpecMark    = ABC_CALLOC( int, nKeys );
    p->pDiagMark    = ABC_CALLOC( int, nKeys );
    p->pSplitMark   = ABC_CALLOC( int, nKeys );
    p->pProcessMark = ABC_CALLOC( int, nKeys );
    p->pEvalMark    = ABC_CALLOC( int, nKeys );
    p->pRootMark    = ABC_CALLOC( int, p->nObjs );
    p->vDiagPairs   = Vec_IntAlloc( 192 );
    p->vSpecKeys    = Vec_IntAlloc( 1024 );
    p->vSpecMasks   = Vec_IntAlloc( 1024 * nWords );
    p->vDiagKeys    = Vec_IntAlloc( 1024 );
    p->vDiagRoots   = Vec_IntAlloc( 1024 );
    p->vDiagMasks   = Vec_IntAlloc( 1024 * nWords );
    p->vSplitKeys   = Vec_IntAlloc( 1024 );
    p->vDirtyKeys   = Vec_IntAlloc( 4096 );
    p->vWaveKeys    = Vec_IntAlloc( 4096 );
    p->vQueue       = Vec_IntAlloc( 4096 );
    p->vDirtyRoots  = Vec_IntAlloc( 1024 );
    p->vConstRefined = Vec_IntAlloc( 64 );
    p->vClassAll    = Vec_IntAlloc( 64 );
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
    Vec_IntFreeP( &p->vDiagPairs );
    Vec_IntFreeP( &p->vSpecKeys );
    Vec_IntFreeP( &p->vSpecMasks );
    Vec_IntFreeP( &p->vDiagKeys );
    Vec_IntFreeP( &p->vDiagRoots );
    Vec_IntFreeP( &p->vDiagMasks );
    Vec_IntFreeP( &p->vSplitKeys );
    Vec_IntFreeP( &p->vDirtyKeys );
    Vec_IntFreeP( &p->vWaveKeys );
    Vec_IntFreeP( &p->vQueue );
    Vec_IntFreeP( &p->vDirtyRoots );
    Vec_IntFreeP( &p->vConstRefined );
    Vec_IntFreeP( &p->vClassAll );
    Vec_IntFreeP( &p->vClassOld );
    Vec_IntFreeP( &p->vClassNew );
    Vec_PtrFreeP( &p->vSimInfo );
    ABC_FREE( p->pVal );
    ABC_FREE( p->pActiveMask );
    ABC_FREE( p->pCexMask );
    ABC_FREE( p->pFoundMask );
    ABC_FREE( p->pDiffMask );
    ABC_FREE( p->pTempMask );
    ABC_FREE( p->pMark );
    ABC_FREE( p->pSpecMark );
    ABC_FREE( p->pDiagMark );
    ABC_FREE( p->pSplitMark );
    ABC_FREE( p->pProcessMark );
    ABC_FREE( p->pEvalMark );
    ABC_FREE( p->pRootMark );
    ABC_FREE( p->pPhase0 );
    ABC_FREE( p->pPhase1 );
    ABC_FREE( p );
}

static void Cec_SeedSimReset( Cec_SeedSim_t * p )
{
    size_t nKeys = (size_t)p->nFrames * p->nObjs;
    int i, Key;
    Vec_IntForEachEntry( p->vSpecKeys, Key, i )
        p->pSpecMark[Key] = 0;
    Vec_IntForEachEntry( p->vDiagKeys, Key, i )
        p->pDiagMark[Key] = 0;
    Vec_IntClear( p->vDiagPairs );
    Vec_IntClear( p->vSpecKeys );
    Vec_IntClear( p->vSpecMasks );
    Vec_IntClear( p->vDiagKeys );
    Vec_IntClear( p->vDiagRoots );
    Vec_IntClear( p->vDiagMasks );
    Vec_IntClear( p->vSplitKeys );
    Vec_IntClear( p->vDirtyKeys );
    Vec_IntClear( p->vWaveKeys );
    Vec_IntClear( p->vQueue );
    for ( i = 0; i < p->nWords; i++ )
        p->pActiveMask[i] = ~(unsigned)0;
    p->pActiveMask[0] &= ~(unsigned)1;
    memset( p->pCexMask, 0, sizeof(unsigned) * p->nWords );
    memset( p->pFoundMask, 0, sizeof(unsigned) * p->nWords );
    p->vBatchInfo = NULL;
    p->nSpecKeys = 0;
    p->nEvalKeys = 0;
    p->nMarkVersion++;
    p->nSplitVersion++;
    p->nProcessVersion++;
    p->nEvalVersion++;
    if ( p->nMarkVersion == 0 )
    {
        memset( p->pMark, 0, sizeof(int) * nKeys );
        p->nMarkVersion = 1;
    }
    if ( p->nSplitVersion == 0 )
    {
        memset( p->pSplitMark, 0, sizeof(int) * nKeys );
        p->nSplitVersion = 1;
    }
    if ( p->nProcessVersion == 0 )
    {
        memset( p->pProcessMark, 0, sizeof(int) * nKeys );
        p->nProcessVersion = 1;
    }
    if ( p->nEvalVersion == 0 )
    {
        memset( p->pEvalMark, 0, sizeof(int) * nKeys );
        p->nEvalVersion = 1;
    }
}

static int Cec_SeedSimAddDiagKey( Cec_SeedSim_t * p, int Frame, int ObjId )
{
    int Key, iDiag, Repr, w;
    if ( ObjId <= 0 || ObjId >= p->nObjs )
        return ObjId == 0;
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    iDiag = p->pDiagMark[Key] - 1;
    if ( iDiag < 0 )
    {
        Repr = Gia_ObjRepr( p->pAig, ObjId );
        iDiag = Vec_IntSize( p->vDiagKeys );
        p->pDiagMark[Key] = iDiag + 1;
        Vec_IntPush( p->vDiagKeys, Key );
        Vec_IntPush( p->vDiagRoots, Repr == 0 ? 0 :
            (Gia_ObjIsHead(p->pAig, ObjId) ? ObjId : Repr) );
        for ( w = 0; w < p->nWords; w++ )
            Vec_IntPush( p->vDiagMasks, 0 );
    }
    return 1;
}

static int Cec_SeedSimAddDiagBit( Cec_SeedSim_t * p, int Frame, int ObjId, int iBit )
{
    int Key, iDiag;
    unsigned * pMask;
    if ( !Cec_SeedSimAddDiagKey(p, Frame, ObjId) )
        return 0;
    if ( ObjId == 0 )
        return 1;
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    iDiag = p->pDiagMark[Key] - 1;
    assert( iDiag >= 0 );
    pMask = (unsigned *)Vec_IntArray(p->vDiagMasks) + (size_t)iDiag * p->nWords;
    Abc_InfoSetBit( pMask, iBit );
    return 1;
}

static int Cec_SeedSimCollectSpecBit( Cec_SeedSim_t * p, int Frame, int ObjId, int iBit, int nLimit );

static int Cec_SeedSimCollectRealBit( Cec_SeedSim_t * p, int Frame, int ObjId, int iBit, int nLimit )
{
    Gia_Obj_t * pObj;
    if ( ObjId < 0 || ObjId >= p->nObjs || Frame < 0 || Frame >= p->nFrames )
        return 0;
    if ( ObjId == 0 )
        return 1;
    pObj = Gia_ManObj( p->pAig, ObjId );
    if ( Gia_ObjIsAnd(pObj) )
    {
        return Cec_SeedSimCollectSpecBit( p, Frame, Gia_ObjFaninId0(pObj, ObjId), iBit, nLimit ) &&
               Cec_SeedSimCollectSpecBit( p, Frame, Gia_ObjFaninId1(pObj, ObjId), iBit, nLimit );
    }
    if ( Gia_ObjIsRo(p->pAig, pObj) && Frame > 0 )
    {
        Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
        int RiId = Gia_ObjId( p->pAig, pRi );
        return Cec_SeedSimCollectSpecBit( p, Frame - 1,
            Gia_ObjFaninId0(pRi, RiId), iBit, nLimit );
    }
    return 1;
}

static int Cec_SeedSimCollectSpecBit( Cec_SeedSim_t * p, int Frame, int ObjId, int iBit, int nLimit )
{
    int Key, Repr, iSpec, iWord = iBit >> 5, w;
    unsigned Bit = (unsigned)1 << (iBit & 31);
    unsigned * pMask;
    if ( ObjId < 0 || ObjId >= p->nObjs || Frame < 0 || Frame >= p->nFrames )
        return 0;
    if ( ObjId == 0 )
        return 1;
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    iSpec = p->pSpecMark[Key] - 1;
    if ( iSpec < 0 )
    {
        if ( ++p->nSpecKeys > nLimit )
            return 0;
        iSpec = Vec_IntSize( p->vSpecKeys );
        p->pSpecMark[Key] = iSpec + 1;
        Vec_IntPush( p->vSpecKeys, Key );
        for ( w = 0; w < p->nWords; w++ )
            Vec_IntPush( p->vSpecMasks, 0 );
    }
    pMask = (unsigned *)Vec_IntArray(p->vSpecMasks) + (size_t)iSpec * p->nWords;
    if ( pMask[iWord] & Bit )
        return 1;
    pMask[iWord] |= Bit;
    Repr = Gia_ObjRepr( p->pAig, ObjId );
    if ( Repr != GIA_VOID )
    {
        if ( !Cec_SeedSimAddDiagBit(p, Frame, ObjId, iBit) )
            return 0;
        return Repr == 0 ||
               Cec_SeedSimCollectSpecBit( p, Frame, Repr, iBit, nLimit );
    }
    return Cec_SeedSimCollectRealBit( p, Frame, ObjId, iBit, nLimit );
}

static int Cec_SeedSimCollectDiagnosis( Cec_SeedSim_t * p, Vec_Int_t * vOutputs, Vec_Int_t * vOutBits, int nLimit )
{
    int i, Out, iBit;
    if ( vOutputs == NULL || vOutBits == NULL )
        return 0;
    Vec_IntForEachEntryDouble( vOutBits, Out, iBit, i )
    {
        int Obj0, Obj1;
        if ( Out < 0 || 2*Out + 1 >= Vec_IntSize(vOutputs) )
            return 0;
        Obj0 = Vec_IntEntry( vOutputs, 2*Out );
        Obj1 = Vec_IntEntry( vOutputs, 2*Out + 1 );
        Abc_InfoSetBit( p->pCexMask, iBit );
        Vec_IntPush( p->vDiagPairs, Obj0 );
        Vec_IntPush( p->vDiagPairs, Obj1 );
        Vec_IntPush( p->vDiagPairs, iBit );
        if ( !Cec_SeedSimAddDiagKey(p, p->iSeedFrame, Obj0) ||
             !Cec_SeedSimAddDiagKey(p, p->iSeedFrame, Obj1) )
            return 0;
        if ( !Cec_SeedSimCollectRealBit(p, p->iSeedFrame, Obj0, iBit, nLimit) ||
             !Cec_SeedSimCollectRealBit(p, p->iSeedFrame, Obj1, iBit, nLimit) )
            return 0;
    }
    return Vec_IntSize(vOutBits) > 0;
}

static int Cec_SeedSimCollectShapeSpec( Cec_SeedSim_t * p, int Frame, int ObjId, int nLimit );

static int Cec_SeedSimCollectShapeReal( Cec_SeedSim_t * p, int Frame, int ObjId, int nLimit )
{
    Gia_Obj_t * pObj;
    int Key;
    if ( ObjId < 0 || ObjId >= p->nObjs || Frame < 0 || Frame >= p->nFrames )
        return 0;
    if ( ObjId == 0 )
        return 1;
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    if ( p->pProcessMark[Key] == p->nProcessVersion )
        return 1;
    p->pProcessMark[Key] = p->nProcessVersion;
    Vec_IntPush( p->vDirtyKeys, Key );
    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
        return 0;
    pObj = Gia_ManObj( p->pAig, ObjId );
    if ( Gia_ObjIsAnd(pObj) )
        return Cec_SeedSimCollectShapeSpec( p, Frame, Gia_ObjFaninId0(pObj, ObjId), nLimit ) &&
               Cec_SeedSimCollectShapeSpec( p, Frame, Gia_ObjFaninId1(pObj, ObjId), nLimit );
    if ( Gia_ObjIsRo(p->pAig, pObj) && Frame > 0 )
    {
        Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
        int RiId = Gia_ObjId( p->pAig, pRi );
        return Cec_SeedSimCollectShapeSpec( p, Frame - 1,
            Gia_ObjFaninId0(pRi, RiId), nLimit );
    }
    return 1;
}

static int Cec_SeedSimCollectShapeSpec( Cec_SeedSim_t * p, int Frame, int ObjId, int nLimit )
{
    Gia_Obj_t * pObj;
    int Repr;
    if ( ObjId < 0 || ObjId >= p->nObjs || Frame < 0 || Frame >= p->nFrames )
        return 0;
    if ( ObjId == 0 || !Cec_SeedSimMark(p, Frame, ObjId) )
        return 1;
    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
        return 0;
    Repr = Gia_ObjRepr( p->pAig, ObjId );
    if ( Repr != GIA_VOID )
        return Repr == 0 || Cec_SeedSimCollectShapeSpec( p, Frame, Repr, nLimit );
    pObj = Gia_ManObj( p->pAig, ObjId );
    if ( Gia_ObjIsAnd(pObj) )
        return Cec_SeedSimCollectShapeSpec( p, Frame, Gia_ObjFaninId0(pObj, ObjId), nLimit ) &&
               Cec_SeedSimCollectShapeSpec( p, Frame, Gia_ObjFaninId1(pObj, ObjId), nLimit );
    if ( Gia_ObjIsRo(p->pAig, pObj) && Frame > 0 )
    {
        Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
        int RiId = Gia_ObjId( p->pAig, pRi );
        return Cec_SeedSimCollectShapeSpec( p, Frame - 1,
            Gia_ObjFaninId0(pRi, RiId), nLimit );
    }
    return 1;
}

static int Cec_SeedSimDiagnosisShapeSmall( Cec_SeedSim_t * p,
    Vec_Int_t * vOutputs, Vec_Int_t * vOutBits, int nLimit )
{
    int i, Out, iBit;
    Vec_IntForEachEntryDouble( vOutBits, Out, iBit, i )
    {
        int Obj0, Obj1;
        (void)iBit;
        if ( Out < 0 || 2*Out + 1 >= Vec_IntSize(vOutputs) )
            return 0;
        Obj0 = Vec_IntEntry( vOutputs, 2*Out );
        Obj1 = Vec_IntEntry( vOutputs, 2*Out + 1 );
        if ( !Cec_SeedSimCollectShapeReal(p, p->iSeedFrame, Obj0, nLimit) ||
             !Cec_SeedSimCollectShapeReal(p, p->iSeedFrame, Obj1, nLimit) )
            return 0;
    }
    return 1;
}

static void Cec_SeedSimRestartTfoMarks( Cec_SeedSim_t * p )
{
    size_t nKeys = (size_t)p->nFrames * p->nObjs;
    Vec_IntClear( p->vDirtyKeys );
    Vec_IntClear( p->vQueue );
    p->nMarkVersion++;
    p->nProcessVersion++;
    if ( p->nMarkVersion == 0 )
    {
        memset( p->pMark, 0, sizeof(int) * nKeys );
        p->nMarkVersion = 1;
    }
    if ( p->nProcessVersion == 0 )
    {
        memset( p->pProcessMark, 0, sizeof(int) * nKeys );
        p->nProcessVersion = 1;
    }
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
    Vec_IntClear( p->vConstRefined );
}

static void Cec_SeedSimAddRoot( Cec_SeedSim_t * p, int ObjId )
{
    Gia_Man_t * pAig = p->pAig;
    int iRoot;
    if ( Gia_ObjIsConst(pAig, ObjId) )
    {
        iRoot = ObjId;
        if ( p->pRootMark[iRoot] != p->nRootVersion )
        {
            p->pRootMark[iRoot] = p->nRootVersion;
            Vec_IntPush( p->vConstRefined, iRoot );
        }
    }
    else if ( Gia_ObjIsClass(pAig, ObjId) )
    {
        iRoot = Gia_ObjIsHead(pAig, ObjId) ? ObjId : Gia_ObjRepr(pAig, ObjId);
        if ( p->pRootMark[iRoot] != p->nRootVersion )
        {
            p->pRootMark[iRoot] = p->nRootVersion;
            Vec_IntPush( p->vDirtyRoots, iRoot );
        }
    }
    else
        return;
}

static int Cec_SeedSimCollectEvalShape( Cec_SeedSim_t * p,
    int Frame, int ObjId, int nLimit )
{
    Gia_Obj_t * pObj;
    int Key;
    if ( ObjId < 0 || ObjId >= p->nObjs || Frame < 0 || Frame >= p->nFrames )
        return 0;
    Key = Cec_SeedSimKey( p, Frame, ObjId );
    if ( p->pProcessMark[Key] == p->nProcessVersion )
        return 1;
    p->pProcessMark[Key] = p->nProcessVersion;
    Vec_IntPush( p->vDirtyKeys, Key );
    if ( Vec_IntSize(p->vDirtyKeys) > nLimit )
        return 0;
    if ( ObjId == 0 )
        return 1;
    pObj = Gia_ManObj( p->pAig, ObjId );
    if ( Gia_ObjIsAnd(pObj) )
        return Cec_SeedSimCollectEvalShape( p, Frame,
                   Gia_ObjFaninId0(pObj, ObjId), nLimit ) &&
               Cec_SeedSimCollectEvalShape( p, Frame,
                   Gia_ObjFaninId1(pObj, ObjId), nLimit );
    if ( Gia_ObjIsRo(p->pAig, pObj) && Frame > 0 )
    {
        Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
        int RiId = Gia_ObjId( p->pAig, pRi );
        return Cec_SeedSimCollectEvalShape( p, Frame - 1,
            Gia_ObjFaninId0(pRi, RiId), nLimit );
    }
    return 1;
}

static int Cec_SeedSimDiagnosisEvalShapeSmall( Cec_SeedSim_t * p,
    Vec_Int_t * vKeys, int nLimit )
{
    int iLo = 0;
    Vec_IntSort( vKeys, 0 );
    while ( iLo < Vec_IntSize(vKeys) )
    {
        int Frame = Vec_IntEntry(vKeys, iLo) / p->nObjs;
        int iHi = iLo, i, Key, ObjId, Ent;
        while ( iHi < Vec_IntSize(vKeys) &&
                Vec_IntEntry(vKeys, iHi) / p->nObjs == Frame )
            iHi++;
        Cec_SeedSimStartRootSet( p );
        for ( i = iLo; i < iHi; i++ )
        {
            Key = Vec_IntEntry( vKeys, i );
            ObjId = Key % p->nObjs;
            if ( Gia_ObjIsConst(p->pAig, ObjId) ||
                 Gia_ObjIsClass(p->pAig, ObjId) )
                Cec_SeedSimAddRoot( p, ObjId );
            else if ( !Cec_SeedSimCollectEvalShape(p, Frame, ObjId, nLimit) )
                return 0;
        }
        Vec_IntForEachEntry( p->vDirtyRoots, Ent, i )
        {
            int Member;
            if ( !Cec_SeedSimCollectEvalShape(p, Frame, Ent, nLimit) )
                return 0;
            Gia_ClassForEachObj1( p->pAig, Ent, Member )
                if ( !Cec_SeedSimCollectEvalShape(p, Frame, Member, nLimit) )
                    return 0;
        }
        Vec_IntForEachEntry( p->vConstRefined, Ent, i )
            if ( !Cec_SeedSimCollectEvalShape(p, Frame, Ent, nLimit) )
                return 0;
        iLo = iHi;
    }
    return 1;
}

static void Cec_SeedSimDiffMask( Cec_SeedSim_t * p, unsigned * pValue0,
    unsigned * pValue1, unsigned * pMask, unsigned * pDiff )
{
    int fCompl = (pValue0[0] & 1) != (pValue1[0] & 1);
    int w;
    for ( w = 0; w < p->nWords; w++ )
        pDiff[w] = (pValue0[w] ^ (fCompl ? ~pValue1[w] : pValue1[w])) & pMask[w];
}

static int Cec_SeedSimMaskIsZero( unsigned * pMask, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        if ( pMask[w] )
            return 0;
    return 1;
}

static int Cec_SeedSimCurrentRoot( Cec_SeedSim_t * p, int ObjId )
{
    if ( ObjId == 0 || Gia_ObjIsConst(p->pAig, ObjId) )
        return 0;
    if ( Gia_ObjIsHead(p->pAig, ObjId) )
        return ObjId;
    if ( Gia_ObjIsClass(p->pAig, ObjId) )
        return Gia_ObjRepr(p->pAig, ObjId);
    return ObjId;
}

static void Cec_SeedSimCheckFailedPairs( Cec_SeedSim_t * p, int Frame )
{
    int i;
    assert( Frame == p->iSeedFrame );
    for ( i = 0; i < Vec_IntSize(p->vDiagPairs); i += 3 )
    {
        int Obj0 = Vec_IntEntry( p->vDiagPairs, i );
        int Obj1 = Vec_IntEntry( p->vDiagPairs, i + 1 );
        int iBit = Vec_IntEntry( p->vDiagPairs, i + 2 );
        int iWord = iBit >> 5;
        unsigned Bit = (unsigned)1 << (iBit & 31);
        unsigned * pValue0, * pValue1;
        if ( Cec_SeedSimCurrentRoot(p, Obj0) != Cec_SeedSimCurrentRoot(p, Obj1) )
        {
            p->pFoundMask[iWord] |= Bit;
            continue;
        }
        pValue0 = Obj0 == 0 ? p->pPhase0 : Cec_SeedSimVal( p, Frame, Obj0 );
        pValue1 = Obj1 == 0 ? p->pPhase0 : Cec_SeedSimVal( p, Frame, Obj1 );
        Cec_SeedSimDiffMask( p, pValue0, pValue1, p->pActiveMask, p->pDiffMask );
        p->pFoundMask[iWord] |= p->pDiffMask[iWord] & Bit;
    }
}

static void Cec_SeedSimAddSplitKey( Cec_SeedSim_t * p, int Frame, int ObjId )
{
    int Key = Cec_SeedSimKey( p, Frame, ObjId );
    if ( p->pSplitMark[Key] == p->nSplitVersion )
        return;
    p->pSplitMark[Key] = p->nSplitVersion;
    Vec_IntPush( p->vSplitKeys, Key );
}

static int Cec_SeedSimPrepareFrame( Cec_SeedSim_t * p, Vec_Int_t * vKeys,
    int Frame, int iLo, int iHi, int nLimit, int fDiagnosis )
{
    Gia_Man_t * pAig = p->pAig;
    int i, Key, Ent;
    Cec_SeedSimStartRootSet( p );
    for ( i = iLo; i < iHi; i++ )
    {
        int ObjId;
        Key = Vec_IntEntry( vKeys, i );
        ObjId = Key % p->nObjs;
        if ( fDiagnosis )
        {
            int iDiag = p->pDiagMark[Key] - 1;
            unsigned * pMask;
            int RootOld;
            assert( iDiag >= 0 );
            pMask = (unsigned *)Vec_IntArray(p->vDiagMasks) + (size_t)iDiag * p->nWords;
            RootOld = Vec_IntEntry( p->vDiagRoots, iDiag );
            int RootNew = Gia_ObjIsConst(pAig, ObjId) ? 0 :
                (Gia_ObjIsHead(pAig, ObjId) ? ObjId :
                 (Gia_ObjIsClass(pAig, ObjId) ? Gia_ObjRepr(pAig, ObjId) : GIA_VOID));
            // Failed endpoints are diagnosis keys as well.  An endpoint
            // outside an equivalence class has no member-to-root assumption.
            if ( RootOld == GIA_VOID )
            {
                if ( !Cec_SeedSimEvalActive(p, Frame, ObjId, nLimit) )
                    return 0;
                continue;
            }
            if ( RootNew != RootOld )
            {
                int w;
                for ( w = 0; w < p->nWords; w++ )
                    p->pFoundMask[w] |= pMask[w];
                continue;
            }
        }
        Cec_SeedSimAddRoot( p, ObjId );
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
    Vec_IntForEachEntry( p->vConstRefined, Ent, i )
        if ( !Cec_SeedSimEvalActive(p, Frame, Ent, nLimit) )
            return 0;
    if ( fDiagnosis )
    {
        for ( i = iLo; i < iHi; i++ )
        {
            unsigned * pMask, * pValue0, * pValue1;
            int ObjId, RootOld, RootNew, iDiag, w;
            Key = Vec_IntEntry( vKeys, i );
            ObjId = Key % p->nObjs;
            iDiag = p->pDiagMark[Key] - 1;
            assert( iDiag >= 0 );
            RootOld = Vec_IntEntry( p->vDiagRoots, iDiag );
            RootNew = Gia_ObjIsConst(pAig, ObjId) ? 0 :
                (Gia_ObjIsHead(pAig, ObjId) ? ObjId :
                 (Gia_ObjIsClass(pAig, ObjId) ? Gia_ObjRepr(pAig, ObjId) : GIA_VOID));
            pMask = (unsigned *)Vec_IntArray(p->vDiagMasks) + (size_t)iDiag * p->nWords;
            if ( RootOld == GIA_VOID )
                continue;
            if ( RootNew != RootOld )
            {
                for ( w = 0; w < p->nWords; w++ )
                    p->pFoundMask[w] |= pMask[w];
                continue;
            }
            if ( ObjId == RootOld )
                continue;
            pValue0 = Cec_SeedSimVal( p, Frame, ObjId );
            pValue1 = RootOld == 0 ?
                (Gia_ObjPhase(Gia_ManObj(pAig, ObjId)) ? p->pPhase1 : p->pPhase0) :
                Cec_SeedSimVal( p, Frame, RootOld );
            Cec_SeedSimDiffMask( p, pValue0, pValue1, pMask, p->pDiffMask );
            for ( w = 0; w < p->nWords; w++ )
                p->pFoundMask[w] |= p->pDiffMask[w];
        }
        if ( Frame == p->iSeedFrame )
            Cec_SeedSimCheckFailedPairs( p, Frame );
    }
    return 1;
}

static int Cec_SeedSimRefineClass_rec( Cec_SeedSim_t * p, int Frame, int iRoot )
{
    unsigned * pSim0;
    int Ent, Count = 0;
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
        return 0;
    Cec_ManSimClassCreate( p->pAig, p->vClassOld );
    Cec_ManSimClassCreate( p->pAig, p->vClassNew );
    if ( Vec_IntSize(p->vClassNew) > 1 )
        Count += Cec_SeedSimRefineClass_rec( p, Frame, Vec_IntEntry(p->vClassNew, 0) );
    return Count + 1;
}

static int Cec_SeedSimRefineClass( Cec_SeedSim_t * p, int Frame, int iRoot )
{
    unsigned * pRoot = Cec_SeedSimVal( p, Frame, iRoot );
    unsigned * pDiff = p->pDiffMask;
    unsigned * pTemp = p->pTempMask;
    int Ent, i, w, Count;
    memset( pDiff, 0, sizeof(unsigned) * p->nWords );
    Vec_IntClear( p->vClassAll );
    Gia_ClassForEachObj( p->pAig, iRoot, Ent )
    {
        Vec_IntPush( p->vClassAll, Ent );
        if ( Ent == iRoot )
            continue;
        Cec_SeedSimDiffMask( p, pRoot, Cec_SeedSimVal(p, Frame, Ent),
                            p->pActiveMask, pTemp );
        for ( w = 0; w < p->nWords; w++ )
            pDiff[w] |= pTemp[w];
    }
    if ( Cec_SeedSimMaskIsZero(pDiff, p->nWords) )
        return 0;
    Count = Cec_SeedSimRefineClass_rec( p, Frame, iRoot );
    assert( Count > 0 );
    Vec_IntForEachEntry( p->vClassAll, Ent, i )
        Cec_SeedSimAddSplitKey( p, Frame, Ent );
    return Count;
}

static void Cec_SeedSimProcessRefinedConstants( Cec_SeedSim_t * p,
    Cec_ManSim_t * pSim, int Frame )
{
    Gia_Man_t * pAig = p->pAig;
    int * pTable;
    int i, k, Key, iPrev, nTableSize;
    if ( Vec_IntSize(p->vConstRefined) == 0 )
        return;
    Vec_IntForEachEntry( p->vConstRefined, i, k )
    {
        unsigned * pValue = Cec_SeedSimVal( p, Frame, i );
        unsigned * pPhase = Gia_ObjPhase(Gia_ManObj(pAig, i)) ? p->pPhase1 : p->pPhase0;
        unsigned * pDiff = p->pDiffMask;
        Cec_SeedSimDiffMask( p, pValue, pPhase, p->pActiveMask, pDiff );
        if ( Cec_SeedSimMaskIsZero(pDiff, p->nWords) )
        {
            Vec_IntDrop( p->vConstRefined, k-- );
            continue;
        }
        Cec_SeedSimAddSplitKey( p, Frame, i );
    }
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
            Cec_SeedSimRefineClass_rec( p, Frame, i );
    ABC_FREE( pTable );
}

static void Cec_SeedSimRefineFrame( Cec_SeedSim_t * p, Cec_ManSim_t * pSim,
    int Frame )
{
    int i, Ent;
    Vec_IntForEachEntry( p->vDirtyRoots, Ent, i )
        if ( Gia_ObjIsHead(p->pAig, Ent) )
            Cec_SeedSimRefineClass( p, Frame, Ent );
    Cec_SeedSimProcessRefinedConstants( p, pSim, Frame );
}

static int Cec_SeedSimProcessKeys( Cec_SeedSim_t * p, Cec_ManSim_t * pSim,
    Vec_Int_t * vKeys, int nLimit, int fDiagnosis )
{
    int iLo = 0;
    Vec_IntSort( vKeys, 0 );
    while ( iLo < Vec_IntSize(vKeys) )
    {
        int Frame = Vec_IntEntry(vKeys, iLo) / p->nObjs;
        int iHi = iLo;
        while ( iHi < Vec_IntSize(vKeys) &&
                Vec_IntEntry(vKeys, iHi) / p->nObjs == Frame )
            iHi++;
        if ( !Cec_SeedSimPrepareFrame(p, vKeys, Frame, iLo, iHi, nLimit, fDiagnosis) )
            return 0;
        Cec_SeedSimRefineFrame( p, pSim, Frame );
        iLo = iHi;
    }
    return 1;
}

static int Cec_SeedSimDiagnosisCovered( Cec_SeedSim_t * p )
{
    int w;
    for ( w = 0; w < p->nWords; w++ )
        if ( p->pCexMask[w] & ~p->pFoundMask[w] )
            return 0;
    return 1;
}

static void Cec_SeedSimQueueNewSplits( Cec_SeedSim_t * p, int * piSplit )
{
    while ( *piSplit < Vec_IntSize(p->vSplitKeys) )
    {
        int Key = Vec_IntEntry( p->vSplitKeys, (*piSplit)++ );
        int Frame = Key / p->nObjs;
        int ObjId = Key % p->nObjs;
        if ( Cec_SeedSimMark(p, Frame, ObjId) )
            Vec_IntPush( p->vQueue, Key );
    }
}

static void Cec_SeedSimCollectWave( Cec_SeedSim_t * p )
{
    int i, Key;
    Vec_IntClear( p->vWaveKeys );
    Vec_IntForEachEntry( p->vDirtyKeys, Key, i )
    {
        if ( p->pProcessMark[Key] == p->nProcessVersion )
            continue;
        p->pProcessMark[Key] = p->nProcessVersion;
        Vec_IntPush( p->vWaveKeys, Key );
    }
}

int Cec_SeedSimTryBatch( Cec_SeedSim_t * p, Cec_ManSim_t * pSim,
    Vec_Ptr_t * vSimInfo, Vec_Int_t * vOutputs, Vec_Int_t * vOutBits, int nFrames )
{
    ABC_INT64_T nKeys = (ABC_INT64_T)p->nFrames * p->nObjs;
    int nLimit = (int)(nKeys * CEC_SEEDSIM_FRAC_NUM / CEC_SEEDSIM_FRAC_DEN);
    int nDiagLimit = (int)(nKeys * CEC_SEEDSIM_DIAG_FRAC_NUM / CEC_SEEDSIM_DIAG_FRAC_DEN);
    int iSplit = 0, nDirty;
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
    if ( !Cec_SeedSimDiagnosisShapeSmall(p, vOutputs, vOutBits, nDiagLimit) )
    {
        nDirty = Vec_IntSize( p->vDirtyKeys );
        if ( nDirty > p->nMaxDirty )
            p->nMaxDirty = nDirty;
        p->vBatchInfo = NULL;
        p->nBatchFull++;
        return 0;
    }
    Cec_SeedSimRestartTfoMarks( p );
    if ( !Cec_SeedSimCollectDiagnosis(p, vOutputs, vOutBits, nLimit) ||
         Vec_IntSize(p->vDiagKeys) > nLimit )
    {
        nDirty = Abc_MaxInt( p->nSpecKeys, p->nEvalKeys );
        if ( nDirty > p->nMaxDirty )
            p->nMaxDirty = nDirty;
        p->vBatchInfo = NULL;
        p->nBatchFull++;
        return 0;
    }
    if ( !Cec_SeedSimDiagnosisEvalShapeSmall(p, p->vDiagKeys, nDiagLimit) )
    {
        nDirty = Vec_IntSize( p->vDirtyKeys );
        if ( nDirty > p->nMaxDirty )
            p->nMaxDirty = nDirty;
        p->vBatchInfo = NULL;
        p->nBatchFull++;
        return 0;
    }
    Cec_SeedSimRestartTfoMarks( p );
    if ( !Cec_SeedSimProcessKeys(p, pSim, p->vDiagKeys, nLimit, 1) ||
         !Cec_SeedSimDiagnosisCovered(p) )
    {
        nDirty = Abc_MaxInt( p->nSpecKeys, p->nEvalKeys );
        if ( nDirty > p->nMaxDirty )
            p->nMaxDirty = nDirty;
        p->vBatchInfo = NULL;
        p->nBatchFull++;
        return 0;
    }
    while ( iSplit < Vec_IntSize(p->vSplitKeys) )
    {
        Cec_SeedSimQueueNewSplits( p, &iSplit );
        if ( !Cec_SeedSimComputeTfo(p, nLimit) )
        {
            nDirty = Vec_IntSize( p->vDirtyKeys );
            if ( nDirty > p->nMaxDirty )
                p->nMaxDirty = nDirty;
            p->vBatchInfo = NULL;
            p->nBatchFull++;
            return 0;
        }
        Cec_SeedSimCollectWave( p );
        if ( Vec_IntSize(p->vWaveKeys) &&
             !Cec_SeedSimProcessKeys(p, pSim, p->vWaveKeys, nLimit, 0) )
        {
            if ( p->nEvalKeys > p->nMaxDirty )
                p->nMaxDirty = p->nEvalKeys;
            p->vBatchInfo = NULL;
            p->nBatchFull++;
            return 0;
        }
    }
    nDirty = Abc_MaxInt( p->nSpecKeys, Vec_IntSize(p->vDirtyKeys) );
    nDirty = Abc_MaxInt( nDirty, p->nEvalKeys );
    if ( nDirty > p->nMaxDirty )
        p->nMaxDirty = nDirty;
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
