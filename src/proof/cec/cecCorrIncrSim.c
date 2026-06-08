/**CFile****************************************************************

  FileName    [cecCorrIncrSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Persistent failed-endpoint TFO incremental simulation for &scorr.]

  Description [Keeps simulation values for every (frame, object) key.  SAT
  supplies the values of each failed pair's endpoints.  These endpoints seed
  a frame-aware TFO walk; only this cone is re-evaluated, and side inputs are
  read from the persistent value array.  Wide cones fall back to the standard
  full sweep, after which the persistent array is refreshed.]

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

static inline void Cec_SeedSimEvalAnd( Cec_SeedSim_t * p, int frame, int objId )
{
    Gia_Obj_t * pObj = Gia_ManObj( p->pAig, objId );
    unsigned * pRes = Cec_SeedSimVal( p, frame, objId );
    unsigned * pR0 = Cec_SeedSimVal( p, frame, Gia_ObjFaninId0(pObj, objId) );
    unsigned * pR1 = Cec_SeedSimVal( p, frame, Gia_ObjFaninId1(pObj, objId) );
    int w;
    assert( Gia_ObjIsAnd(pObj) );
    if ( Gia_ObjFaninC0(pObj) )
    {
        if ( Gia_ObjFaninC1(pObj) )
            for ( w = 0; w < p->nWords; w++ ) pRes[w] = ~(pR0[w] | pR1[w]);
        else
            for ( w = 0; w < p->nWords; w++ ) pRes[w] = ~pR0[w] & pR1[w];
    }
    else
    {
        if ( Gia_ObjFaninC1(pObj) )
            for ( w = 0; w < p->nWords; w++ ) pRes[w] = pR0[w] & ~pR1[w];
        else
            for ( w = 0; w < p->nWords; w++ ) pRes[w] = pR0[w] & pR1[w];
    }
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
    p->pMark        = ABC_CALLOC( int, nKeys );
    p->pSeedMark    = ABC_CALLOC( int, nKeys );
    p->pRootMark    = ABC_CALLOC( int, p->nObjs );
    p->vSeeds       = Vec_IntAlloc( 1024 );
    p->vDirtyKeys   = Vec_IntAlloc( 4096 );
    p->vQueue       = Vec_IntAlloc( 4096 );
    p->vDirtyRoots  = Vec_IntAlloc( 1024 );
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
    Vec_IntFreeP( &p->vSeeds );
    Vec_IntFreeP( &p->vDirtyKeys );
    Vec_IntFreeP( &p->vQueue );
    Vec_IntFreeP( &p->vDirtyRoots );
    Vec_IntFreeP( &p->vClassOld );
    Vec_IntFreeP( &p->vClassNew );
    ABC_FREE( p->pVal );
    ABC_FREE( p->pMark );
    ABC_FREE( p->pSeedMark );
    ABC_FREE( p->pRootMark );
    ABC_FREE( p->pPhase0 );
    ABC_FREE( p->pPhase1 );
    ABC_FREE( p );
}

static void Cec_SeedSimReset( Cec_SeedSim_t * p )
{
    Vec_IntClear( p->vSeeds );
    Vec_IntClear( p->vDirtyKeys );
    Vec_IntClear( p->vQueue );
    p->nMarkVersion++;
    p->nSeedVersion++;
    if ( p->nMarkVersion == 0 )
    {
        memset( p->pMark, 0, sizeof(int) * (size_t)p->nFrames * p->nObjs );
        p->nMarkVersion = 1;
    }
    if ( p->nSeedVersion == 0 )
    {
        memset( p->pSeedMark, 0, sizeof(int) * (size_t)p->nFrames * p->nObjs );
        p->nSeedVersion = 1;
    }
}

static inline void Cec_SeedSimSetBit( unsigned * pInfo, int iBit, int Value )
{
    if ( Abc_InfoHasBit( pInfo, iBit ) != Value )
        Abc_InfoXorBit( pInfo, iBit );
}

static int Cec_SeedSimAddSourceBit( Cec_SeedSim_t * p, int ObjId, int iBit, int Value )
{
    int Key;
    unsigned * pInfo;
    if ( ObjId == 0 )
        return Value == 0;
    if ( ObjId < 0 || ObjId >= p->nObjs || Value < 0 )
        return 0;
    Key = Cec_SeedSimKey( p, p->iSeedFrame, ObjId );
    p->pSeedMark[Key] = p->nSeedVersion;
    pInfo = Cec_SeedSimVal( p, p->iSeedFrame, ObjId );
    Cec_SeedSimSetBit( pInfo, iBit, Value );
    if ( Cec_SeedSimMark( p, p->iSeedFrame, ObjId ) )
    {
        p->pSeedMark[Key] = p->nSeedVersion;
        Vec_IntPush( p->vSeeds, Key );
        Vec_IntPush( p->vQueue, Key );
    }
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

static int Cec_SeedSimComputeTfo( Cec_SeedSim_t * p )
{
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
                    Vec_IntPush( p->vQueue, Cec_SeedSimKey(p, Frame, FanId) );
            }
            else if ( Gia_ObjIsRi(p->pAig, pFan) && Frame + 1 < p->nFrames )
            {
                int RoId = Gia_ObjRiToRoId( p->pAig, FanId );
                if ( Cec_SeedSimMark( p, Frame + 1, RoId ) )
                    Vec_IntPush( p->vQueue, Cec_SeedSimKey(p, Frame + 1, RoId) );
            }
        }
    }
    return Vec_IntSize( p->vDirtyKeys );
}

static void Cec_SeedSimEvaluate( Cec_SeedSim_t * p )
{
    int i, Key;
    Vec_IntSort( p->vDirtyKeys, 0 );
    Vec_IntForEachEntry( p->vDirtyKeys, Key, i )
    {
        int Frame = Key / p->nObjs;
        int ObjId = Key % p->nObjs;
        Gia_Obj_t * pObj = Gia_ManObj( p->pAig, ObjId );
        if ( p->pSeedMark[Key] == p->nSeedVersion )
            continue;
        if ( Gia_ObjIsAnd(pObj) )
            Cec_SeedSimEvalAnd( p, Frame, ObjId );
        else if ( Gia_ObjIsRo(p->pAig, pObj) && Frame > 0 )
        {
            Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
            int RiId = Gia_ObjId( p->pAig, pRi );
            int DrvId = Gia_ObjFaninId0( pRi, RiId );
            unsigned * pRes = Cec_SeedSimVal( p, Frame, ObjId );
            unsigned * pDrv = Cec_SeedSimVal( p, Frame - 1, DrvId );
            int w;
            if ( Gia_ObjFaninC0(pRi) )
                for ( w = 0; w < p->nWords; w++ ) pRes[w] = ~pDrv[w];
            else
                Cec_SeedSimCopyWords( pRes, pDrv, p->nWords );
            pRes[0] &= ~(unsigned)1;
        }
    }
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

static void Cec_SeedSimRefineFrame( Cec_SeedSim_t * p, int Frame, int iLo, int iHi )
{
    Gia_Man_t * pAig = p->pAig;
    int i, Ent;
    p->nRootVersion++;
    if ( p->nRootVersion == 0 )
    {
        memset( p->pRootMark, 0, sizeof(int) * p->nObjs );
        p->nRootVersion = 1;
    }
    Vec_IntClear( p->vDirtyRoots );
    for ( i = iLo; i < iHi; i++ )
    {
        int ObjId = Vec_IntEntry(p->vDirtyKeys, i) % p->nObjs;
        if ( Gia_ObjIsConst(pAig, ObjId) )
        {
            unsigned * pVal = Cec_SeedSimVal( p, Frame, ObjId );
            unsigned * pPhase = Gia_ObjPhase(Gia_ManObj(pAig, ObjId)) ? p->pPhase1 : p->pPhase0;
            if ( !Cec_ManSimCompareEqual( pVal, pPhase, p->nWords ) )
                Gia_ObjSetRepr( pAig, ObjId, GIA_VOID );
            continue;
        }
        if ( Gia_ObjIsClass(pAig, ObjId) )
        {
            int iRoot = Gia_ObjIsHead(pAig, ObjId) ? ObjId : Gia_ObjRepr(pAig, ObjId);
            if ( p->pRootMark[iRoot] != p->nRootVersion )
            {
                p->pRootMark[iRoot] = p->nRootVersion;
                Vec_IntPush( p->vDirtyRoots, iRoot );
            }
        }
    }
    Vec_IntForEachEntry( p->vDirtyRoots, Ent, i )
        if ( Gia_ObjIsHead(pAig, Ent) )
            Cec_SeedSimRefineClass( p, Frame, Ent );
}

int Cec_SeedSimTryBatch( Cec_SeedSim_t * p, Cec_ManSim_t * pSim, Vec_Int_t * vOutputs, Vec_Int_t * vOutVals, Vec_Int_t * vOutBits, int nFrames )
{
    int nDirty, iLo;
    (void)pSim;
    assert( nFrames == p->nFrames );
    if ( !p->fInitialized )
    {
        p->nBatchFull++;
        return 0;
    }
    Cec_SeedSimReset( p );
    if ( !Cec_SeedSimCollectEndpointSources( p, vOutputs, vOutVals, vOutBits ) )
    {
        p->nBatchFull++;
        return 0;
    }
    nDirty = Cec_SeedSimComputeTfo( p );
    if ( nDirty > p->nMaxDirty )
        p->nMaxDirty = nDirty;
    if ( (ABC_INT64_T)nDirty * CEC_SEEDSIM_FRAC_DEN >
         (ABC_INT64_T)p->nFrames * p->nObjs * CEC_SEEDSIM_FRAC_NUM )
    {
        p->nBatchFull++;
        return 0;
    }
    p->nBatchLocal++;
    if ( nDirty == 0 )
        return 1;
    Cec_SeedSimEvaluate( p );
    iLo = 0;
    while ( iLo < Vec_IntSize(p->vDirtyKeys) )
    {
        int Frame = Vec_IntEntry(p->vDirtyKeys, iLo) / p->nObjs;
        int iHi = iLo;
        while ( iHi < Vec_IntSize(p->vDirtyKeys) &&
                Vec_IntEntry(p->vDirtyKeys, iHi) / p->nObjs == Frame )
            iHi++;
        Cec_SeedSimRefineFrame( p, Frame, iLo, iHi );
        iLo = iHi;
    }
    return 1;
}

void Cec_SeedSimUpdateFull( Cec_SeedSim_t * p, Vec_Ptr_t * vSimInfo, int nFrames )
{
    Gia_Obj_t * pObj;
    int Frame, i, w;
    assert( nFrames == p->nFrames );
    assert( Vec_PtrSize(vSimInfo) == p->nRegs + nFrames * p->nPis );
    assert( Vec_PtrReadWordsSimInfo(vSimInfo) == p->nWords );
    for ( Frame = 0; Frame < nFrames; Frame++ )
    {
        unsigned * pConst = Cec_SeedSimVal( p, Frame, 0 );
        for ( w = 0; w < p->nWords; w++ )
            pConst[w] = 0;
        Gia_ManForEachRo( p->pAig, pObj, i )
        {
            int ObjId = Gia_ObjId( p->pAig, pObj );
            unsigned * pDst = Cec_SeedSimVal( p, Frame, ObjId );
            if ( Frame == 0 )
            {
                unsigned * pSrc = (unsigned *)Vec_PtrEntry( vSimInfo, i );
                Cec_SeedSimCopyWords( pDst, pSrc, p->nWords );
            }
            else
            {
                Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pAig, pObj );
                int RiId = Gia_ObjId( p->pAig, pRi );
                int DrvId = Gia_ObjFaninId0( pRi, RiId );
                unsigned * pSrc = Cec_SeedSimVal( p, Frame - 1, DrvId );
                if ( Gia_ObjFaninC0(pRi) )
                    for ( w = 0; w < p->nWords; w++ ) pDst[w] = ~pSrc[w];
                else
                    Cec_SeedSimCopyWords( pDst, pSrc, p->nWords );
            }
            pDst[0] &= ~(unsigned)1;
        }
        Gia_ManForEachPi( p->pAig, pObj, i )
        {
            int ObjId = Gia_ObjId( p->pAig, pObj );
            unsigned * pDst = Cec_SeedSimVal( p, Frame, ObjId );
            unsigned * pSrc = (unsigned *)Vec_PtrEntry( vSimInfo, p->nRegs + Frame * p->nPis + i );
            Cec_SeedSimCopyWords( pDst, pSrc, p->nWords );
            pDst[0] &= ~(unsigned)1;
        }
        Gia_ManForEachAnd( p->pAig, pObj, i )
            Cec_SeedSimEvalAnd( p, Frame, i );
        Gia_ManForEachCo( p->pAig, pObj, i )
        {
            int ObjId = Gia_ObjId( p->pAig, pObj );
            int DrvId = Gia_ObjFaninId0( pObj, ObjId );
            unsigned * pDst = Cec_SeedSimVal( p, Frame, ObjId );
            unsigned * pSrc = Cec_SeedSimVal( p, Frame, DrvId );
            if ( Gia_ObjFaninC0(pObj) )
                for ( w = 0; w < p->nWords; w++ ) pDst[w] = ~pSrc[w];
            else
                Cec_SeedSimCopyWords( pDst, pSrc, p->nWords );
        }
    }
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
