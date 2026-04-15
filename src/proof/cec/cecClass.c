/**CFile****************************************************************

  FileName    [cecClass.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Equivalence class refinement.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecClass.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline unsigned * Cec_ObjSim( Cec_ManSim_t * p, int Id )            { return p->pMems + p->pSimInfo[Id] + 1;   }
static inline void       Cec_ObjSetSim( Cec_ManSim_t * p, int Id, int n )  { p->pSimInfo[Id] = n;                     }

static inline float      Cec_MemUsage( Cec_ManSim_t * p )                  { return 1.0*p->nMemsMax*(p->pPars->nWords+1)/(1<<20);   }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Compares simulation info of one node with constant 0.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSimCompareConst( unsigned * p, int nWords )
{
    int w;
    if ( p[0] & 1 )
    {
        for ( w = 0; w < nWords; w++ )
            if ( p[w] != ~0 )
                return 0;
        return 1;
    }
    else
    {
        for ( w = 0; w < nWords; w++ )
            if ( p[w] != 0 )
                return 0;
        return 1;
    }
}

/**Function*************************************************************

  Synopsis    [Compares simulation info of two nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSimCompareEqual( unsigned * p0, unsigned * p1, int nWords )
{
    int w;
    if ( (p0[0] & 1) == (p1[0] & 1) )
    {
        for ( w = 0; w < nWords; w++ )
            if ( p0[w] != p1[w] )
                return 0;
        return 1;
    }
    else
    {
        for ( w = 0; w < nWords; w++ )
            if ( p0[w] != ~p1[w] )
                return 0;
        return 1;
    }
}

/**Function*************************************************************

  Synopsis    [Returns the number of the first non-equal bit.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSimCompareConstFirstBit( unsigned * p, int nWords )
{
    int w;
    if ( p[0] & 1 )
    {
        for ( w = 0; w < nWords; w++ )
            if ( p[w] != ~0 )
                return 32*w + Gia_WordFindFirstBit( ~p[w] );
        return -1;
    }
    else
    {
        for ( w = 0; w < nWords; w++ )
            if ( p[w] != 0 )
                return 32*w + Gia_WordFindFirstBit( p[w] );
        return -1;
    }
}

/**Function*************************************************************

  Synopsis    [Compares simulation info of two nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSimCompareEqualFirstBit( unsigned * p0, unsigned * p1, int nWords )
{
    int w;
    if ( (p0[0] & 1) == (p1[0] & 1) )
    {
        for ( w = 0; w < nWords; w++ )
            if ( p0[w] != p1[w] )
                return 32*w + Gia_WordFindFirstBit( p0[w] ^ p1[w] );
        return -1;
    }
    else
    {
        for ( w = 0; w < nWords; w++ )
            if ( p0[w] != ~p1[w] )
                return 32*w + Gia_WordFindFirstBit( p0[w] ^ ~p1[w] );
        return -1;
    }
}

/**Function*************************************************************

  Synopsis    [Returns the number of the first non-equal bit.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSimCompareConstScore( unsigned * p, int nWords, int * pScores )
{
    int w, b;
    if ( p[0] & 1 )
    {
        for ( w = 0; w < nWords; w++ )
            if ( p[w] != ~0 )
                for ( b = 0; b < 32; b++ )
                    if ( ((~p[w]) >> b ) & 1 )
                        pScores[32*w + b]++;
    }
    else
    {
        for ( w = 0; w < nWords; w++ )
            if ( p[w] != 0 )
                for ( b = 0; b < 32; b++ )
                    if ( ((p[w]) >> b ) & 1 )
                        pScores[32*w + b]++;
    }
}

/**Function*************************************************************

  Synopsis    [Compares simulation info of two nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSimCompareEqualScore( unsigned * p0, unsigned * p1, int nWords, int * pScores )
{
    int w, b;
    if ( (p0[0] & 1) == (p1[0] & 1) )
    {
        for ( w = 0; w < nWords; w++ )
            if ( p0[w] != p1[w] )
                for ( b = 0; b < 32; b++ )
                    if ( ((p0[w] ^ p1[w]) >> b ) & 1 )
                        pScores[32*w + b]++;
    }
    else
    {
        for ( w = 0; w < nWords; w++ )
            if ( p0[w] != ~p1[w] )
                for ( b = 0; b < 32; b++ )
                    if ( ((p0[w] ^ ~p1[w]) >> b ) & 1 )
                        pScores[32*w + b]++;
    }
}

/**Function*************************************************************

  Synopsis    [Creates equivalence class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSimClassCreate( Gia_Man_t * p, Vec_Int_t * vClass )
{
    int Repr = GIA_VOID, EntPrev = -1, Ent, i;
    assert( Vec_IntSize(vClass) > 0 );
    Vec_IntForEachEntry( vClass, Ent, i )
    {
        if ( i == 0 )
        {
            Repr = Ent;
            Gia_ObjSetRepr( p, Ent, GIA_VOID );
            EntPrev = Ent;
        }
        else
        {
            assert( Repr < Ent );
            Gia_ObjSetRepr( p, Ent, Repr );
            Gia_ObjSetNext( p, EntPrev, Ent );
            EntPrev = Ent;
        }
    }
    Gia_ObjSetNext( p, EntPrev, 0 );
}

/**Function*************************************************************

  Synopsis    [Refines one equivalence class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int s_Count = 0;

int Cec_ManSimClassRefineOne_rec( Cec_ManSim_t * p, int i )
{
    unsigned * pSim0, * pSim1;
    int Ent;
    s_Count++;
    Vec_IntClear( p->vClassOld );
    Vec_IntClear( p->vClassNew );
    Vec_IntPush( p->vClassOld, i );
    pSim0 = Cec_ObjSim(p, i);
    Gia_ClassForEachObj1( p->pAig, i, Ent )
    {
        pSim1 = Cec_ObjSim(p, Ent);
        if ( Cec_ManSimCompareEqual( pSim0, pSim1, p->nWords ) )
            Vec_IntPush( p->vClassOld, Ent );
        else
        {
            Vec_IntPush( p->vClassNew, Ent );
            if ( p->pBestState )
                Cec_ManSimCompareEqualScore( pSim0, pSim1, p->nWords, p->pScores );
        }
    }
    if ( Vec_IntSize( p->vClassNew ) == 0 )
        return 0;
    Cec_ManSimClassCreate( p->pAig, p->vClassOld );
    Cec_ManSimClassCreate( p->pAig, p->vClassNew );
    if ( Vec_IntSize(p->vClassNew) > 1 )
        return 1 + Cec_ManSimClassRefineOne_rec( p, Vec_IntEntry(p->vClassNew,0) );
    return 1;
}
int Cec_ManSimClassRefineOne_( Cec_ManSim_t * p, int i )
{
    int Res;
    s_Count = 0;
    Res = Cec_ManSimClassRefineOne_rec( p, i );
    if ( s_Count > 10 )
    printf( "%d ", s_Count );
    return Res;
}
int Cec_ManSimClassRefineOne( Cec_ManSim_t * p, int i )
{
    return Cec_ManSimClassRefineOne_rec( p, i );
}

/**Function*************************************************************

  Synopsis    [Refines one equivalence class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSimClassRemoveOne( Cec_ManSim_t * p, int i )
{
    int iRepr, Ent;
    if ( Gia_ObjIsConst(p->pAig, i) )
    {
        Gia_ObjSetRepr( p->pAig, i, GIA_VOID );
        return 1;
    }
    if ( !Gia_ObjIsClass(p->pAig, i) )
        return 0;
    assert( Gia_ObjIsClass(p->pAig, i) );
    iRepr = Gia_ObjRepr( p->pAig, i );
    if ( iRepr == GIA_VOID )
        iRepr = i;
    // collect nodes
    Vec_IntClear( p->vClassOld );
    Vec_IntClear( p->vClassNew );
    Gia_ClassForEachObj( p->pAig, iRepr, Ent )
    {
        if ( Ent == i )
            Vec_IntPush( p->vClassNew, Ent );
        else
            Vec_IntPush( p->vClassOld, Ent );
    }
    assert( Vec_IntSize( p->vClassNew ) == 1 );
    Cec_ManSimClassCreate( p->pAig, p->vClassOld );
    Cec_ManSimClassCreate( p->pAig, p->vClassNew );
    assert( !Gia_ObjIsClass(p->pAig, i) );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes hash key of the simuation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSimHashKey( unsigned * pSim, int nWords, int nTableSize )
{
    static int s_Primes[16] = { 
        1291, 1699, 1999, 2357, 2953, 3313, 3907, 4177, 
        4831, 5147, 5647, 6343, 6899, 7103, 7873, 8147 };
    unsigned uHash = 0;
    int i;
    if ( pSim[0] & 1 )
        for ( i = 0; i < nWords; i++ )
            uHash ^= ~pSim[i] * s_Primes[i & 0xf];
    else
        for ( i = 0; i < nWords; i++ )
            uHash ^= pSim[i] * s_Primes[i & 0xf];
    return (int)(uHash % nTableSize);

}

/**Function*************************************************************

  Synopsis    [Resets pointers to the simulation memory.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSimMemRelink( Cec_ManSim_t * p )
{
    unsigned * pPlace, Ent;
    pPlace = (unsigned *)&p->MemFree;
    for ( Ent = p->nMems * (p->nWords + 1); 
          Ent + p->nWords + 1 < (unsigned)p->nWordsAlloc; 
          Ent += p->nWords + 1 )
    {
        *pPlace = Ent;
        pPlace = p->pMems + Ent;
    }
    *pPlace = 0;
    p->nWordsOld = p->nWords;
}

/**Function*************************************************************

  Synopsis    [References simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Cec_ManSimSimRef( Cec_ManSim_t * p, int i )
{
    unsigned * pSim;
    assert( p->pSimInfo[i] == 0 );
    if ( p->MemFree == 0 )
    {
        if ( p->nWordsAlloc == 0 )
        {
            assert( p->pMems == NULL );
            p->nWordsAlloc = (1<<17); // -> 1Mb
            p->nMems = 1;
        }
        p->nWordsAlloc *= 2;
        p->pMems = ABC_REALLOC( unsigned, p->pMems, p->nWordsAlloc );
        Cec_ManSimMemRelink( p );
    }
    p->pSimInfo[i] = p->MemFree;
    pSim = p->pMems + p->MemFree;
    p->MemFree = pSim[0];
    pSim[0] = Gia_ObjValue( Gia_ManObj(p->pAig, i) );
    p->nMems++;
    if ( p->nMemsMax < p->nMems )
        p->nMemsMax = p->nMems;
    return pSim;
}

/**Function*************************************************************

  Synopsis    [Dereferences simulaton info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Cec_ManSimSimDeref( Cec_ManSim_t * p, int i )
{
    unsigned * pSim;
    assert( p->pSimInfo[i] > 0 );
    pSim = p->pMems + p->pSimInfo[i];
    if ( --pSim[0] == 0 )
    {
        pSim[0] = p->MemFree;
        p->MemFree = p->pSimInfo[i];
        p->pSimInfo[i] = 0;
        p->nMems--;
    }
    return pSim;
}

/**Function*************************************************************

  Synopsis    [Refines nodes belonging to candidate constant class.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSimProcessRefined( Cec_ManSim_t * p, Vec_Int_t * vRefined )
{
    unsigned * pSim;
    int * pTable, nTableSize, i, k, Key;
    if ( Vec_IntSize(vRefined) == 0 )
        return;
    nTableSize = Abc_PrimeCudd( 100 + Vec_IntSize(vRefined) / 3 );
    pTable = ABC_CALLOC( int, nTableSize );
    Vec_IntForEachEntry( vRefined, i, k )
    {
        pSim = Cec_ObjSim( p, i );
        assert( !Cec_ManSimCompareConst( pSim, p->nWords ) );
        Key = Cec_ManSimHashKey( pSim, p->nWords, nTableSize );
        if ( pTable[Key] == 0 )
        {
            assert( Gia_ObjRepr(p->pAig, i) == 0 );
            assert( Gia_ObjNext(p->pAig, i) == 0 );
            Gia_ObjSetRepr( p->pAig, i, GIA_VOID );
        }
        else
        {
            Gia_ObjSetNext( p->pAig, pTable[Key], i );
            Gia_ObjSetRepr( p->pAig, i, Gia_ObjRepr(p->pAig, pTable[Key]) );
            if ( Gia_ObjRepr(p->pAig, i) == GIA_VOID )
                Gia_ObjSetRepr( p->pAig, i, pTable[Key] );
            assert( Gia_ObjRepr(p->pAig, i) > 0 );
        }
        pTable[Key] = i;
    }
    Vec_IntForEachEntry( vRefined, i, k )
    {
        if ( Gia_ObjIsHead( p->pAig, i ) )
            Cec_ManSimClassRefineOne( p, i );
    }
    Vec_IntForEachEntry( vRefined, i, k )
        Cec_ManSimSimDeref( p, i );
    ABC_FREE( pTable );
}


/**Function*************************************************************

  Synopsis    [Saves the input pattern with the given number.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSimSavePattern( Cec_ManSim_t * p, int iPat )
{
    unsigned * pInfo;
    int i;
    assert( p->pCexComb == NULL );
    assert( iPat >= 0 && iPat < 32 * p->nWords );
    p->pCexComb = (Abc_Cex_t *)ABC_CALLOC( char, 
        sizeof(Abc_Cex_t) + sizeof(unsigned) * Abc_BitWordNum(Gia_ManCiNum(p->pAig)) );
    p->pCexComb->iPo = p->iOut;
    p->pCexComb->nPis = Gia_ManCiNum(p->pAig);
    p->pCexComb->nBits = Gia_ManCiNum(p->pAig);
    for ( i = 0; i < Gia_ManCiNum(p->pAig); i++ )
    {
        pInfo = (unsigned *)Vec_PtrEntry( p->vCiSimInfo, i );
        if ( Abc_InfoHasBit( pInfo, iPat ) )
            Abc_InfoSetBit( p->pCexComb->pData, i );
    }
}

/**Function*************************************************************

  Synopsis    [Find the best pattern using the scores.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSimFindBestPattern( Cec_ManSim_t * p )
{ 
    unsigned * pInfo;
    int i, ScoreBest = 0, iPatBest = 1; // set the first pattern
    // find the best pattern
    for ( i = 0; i < 32 * p->nWords; i++ )
        if ( ScoreBest < p->pScores[i] )
        {
            ScoreBest = p->pScores[i];
            iPatBest = i;
        }
    // compare this with the available patterns - and save
    if ( p->pBestState->iPo <= ScoreBest )
    {
        assert( p->pBestState->nRegs == Gia_ManRegNum(p->pAig) );
        for ( i = 0; i < Gia_ManRegNum(p->pAig); i++ )
        {
            pInfo = (unsigned *)Vec_PtrEntry( p->vCiSimInfo, Gia_ManPiNum(p->pAig) + i );
            if ( Abc_InfoHasBit(p->pBestState->pData, i) != Abc_InfoHasBit(pInfo, iPatBest) )
                Abc_InfoXorBit( p->pBestState->pData, i );
        }
        p->pBestState->iPo = ScoreBest;
    }
}

/**Function*************************************************************

  Synopsis    [Returns 1 if computation should stop.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSimAnalyzeOutputs( Cec_ManSim_t * p )
{
    unsigned * pInfo, * pInfo2;
    int i;
    if ( !p->pPars->fCheckMiter )
        return 0;
    assert( p->vCoSimInfo != NULL );
    // compare outputs with 0
    if ( p->pPars->fDualOut )
    {
        assert( (Gia_ManPoNum(p->pAig) & 1) == 0 );
        for ( i = 0; i < Gia_ManPoNum(p->pAig); i++ )
        {
            pInfo  = (unsigned *)Vec_PtrEntry( p->vCoSimInfo, i );
            pInfo2 = (unsigned *)Vec_PtrEntry( p->vCoSimInfo, ++i );
            if ( !Cec_ManSimCompareEqual( pInfo, pInfo2, p->nWords ) )
            {
                if ( p->iOut == -1 )
                {
                    p->iOut = i/2;
                    Cec_ManSimSavePattern( p, Cec_ManSimCompareEqualFirstBit(pInfo, pInfo2, p->nWords) );
                }
                if ( p->pCexes == NULL )
                    p->pCexes = ABC_CALLOC( void *, Gia_ManPoNum(p->pAig)/2 );
                if ( p->pCexes[i/2] == NULL )
                {
                    p->nOuts++;
                    p->pCexes[i/2] = (void *)1;
                }
            }
        }
    }
    else
    {
        for ( i = 0; i < Gia_ManPoNum(p->pAig); i++ )
        {
            pInfo = (unsigned *)Vec_PtrEntry( p->vCoSimInfo, i );
            if ( !Cec_ManSimCompareConst( pInfo, p->nWords ) )
            {
                if ( p->iOut == -1 )
                {
                    p->iOut = i;
                    Cec_ManSimSavePattern( p, Cec_ManSimCompareConstFirstBit(pInfo, p->nWords) );
                }
                if ( p->pCexes == NULL )
                    p->pCexes = ABC_CALLOC( void *, Gia_ManPoNum(p->pAig) );
                if ( p->pCexes[i] == NULL )
                {
                    p->nOuts++;
                    p->pCexes[i] = (void *)1;
                }
            }
        }
    }
    return p->pCexes != NULL;
}

/**Function*************************************************************

  Synopsis    [Simulates one round.]

  Description [Returns the number of PO entry if failed; 0 otherwise.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSimSimulateRound( Cec_ManSim_t * p, Vec_Ptr_t * vInfoCis, Vec_Ptr_t * vInfoCos )
{
    Gia_Obj_t * pObj;
    unsigned * pRes0, * pRes1, * pRes;
    int i, k, w, Ent, iCiId = 0, iCoId = 0;
    // prepare internal storage
    if ( p->nWordsOld != p->nWords )
        Cec_ManSimMemRelink( p );
    p->nMemsMax = 0;
    // allocate score counters
    ABC_FREE( p->pScores );
    if ( p->pBestState )
        p->pScores = ABC_CALLOC( int, 32 * p->nWords );
    // simulate nodes
    Vec_IntClear( p->vRefinedC );
    if ( Gia_ObjValue(Gia_ManConst0(p->pAig)) )
    {
        pRes = Cec_ManSimSimRef( p, 0 );
        for ( w = 1; w <= p->nWords; w++ )
            pRes[w] = 0;
    }
    Gia_ManForEachObj1( p->pAig, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) ) 
        {
            if ( Gia_ObjValue(pObj) == 0 )
            {
                iCiId++;
                continue;
            }
            pRes = Cec_ManSimSimRef( p, i );
            if ( vInfoCis ) 
            {
                pRes0 = (unsigned *)Vec_PtrEntry( vInfoCis, iCiId++ );
                for ( w = 1; w <= p->nWords; w++ )
                    pRes[w] = pRes0[w-1];
            }
            else
            {
                for ( w = 1; w <= p->nWords; w++ )
                    pRes[w] = Gia_ManRandom( 0 );
            }
            // make sure the first pattern is always zero
            pRes[1] ^= (pRes[1] & 1);
            goto references;
        }
        if ( Gia_ObjIsCo(pObj) ) // co always has non-zero 1st fanin and zero 2nd fanin
        {
            pRes0 = Cec_ManSimSimDeref( p, Gia_ObjFaninId0(pObj,i) );
            if ( vInfoCos )
            {
                pRes = (unsigned *)Vec_PtrEntry( vInfoCos, iCoId++ );
                if ( Gia_ObjFaninC0(pObj) )
                    for ( w = 1; w <= p->nWords; w++ )
                        pRes[w-1] = ~pRes0[w];
                else 
                    for ( w = 1; w <= p->nWords; w++ )
                        pRes[w-1] = pRes0[w];
            }
            continue;
        }
        assert( Gia_ObjValue(pObj) );
        pRes  = Cec_ManSimSimRef( p, i );
        pRes0 = Cec_ManSimSimDeref( p, Gia_ObjFaninId0(pObj,i) );
        pRes1 = Cec_ManSimSimDeref( p, Gia_ObjFaninId1(pObj,i) );

//        Abc_Print( 1, "%d,%d  ", Gia_ObjValue( Gia_ObjFanin0(pObj) ), Gia_ObjValue( Gia_ObjFanin1(pObj) ) );

        if ( Gia_ObjFaninC0(pObj) )
        {
            if ( Gia_ObjFaninC1(pObj) )
                for ( w = 1; w <= p->nWords; w++ )
                    pRes[w] = ~(pRes0[w] | pRes1[w]);
            else
                for ( w = 1; w <= p->nWords; w++ )
                    pRes[w] = ~pRes0[w] & pRes1[w];
        }
        else
        {
            if ( Gia_ObjFaninC1(pObj) )
                for ( w = 1; w <= p->nWords; w++ )
                    pRes[w] = pRes0[w] & ~pRes1[w];
            else
                for ( w = 1; w <= p->nWords; w++ )
                    pRes[w] = pRes0[w] & pRes1[w];
        }

references:
        // if this node is candidate constant, collect it
        if ( Gia_ObjIsConst(p->pAig, i) && !Cec_ManSimCompareConst(pRes + 1, p->nWords) )
        {
            pRes[0]++;
            Vec_IntPush( p->vRefinedC, i );
            if ( p->pBestState )
                Cec_ManSimCompareConstScore( pRes + 1, p->nWords, p->pScores );
        }
        // if the node belongs to a class, save it
        if ( Gia_ObjIsClass(p->pAig, i) )
            pRes[0]++;
        // if this is the last node of the class, process it
        if ( Gia_ObjIsTail(p->pAig, i) )
        {
            Vec_IntClear( p->vClassTemp );
            Gia_ClassForEachObj( p->pAig, Gia_ObjRepr(p->pAig, i), Ent )
                Vec_IntPush( p->vClassTemp, Ent );
            // refine this class
            Cec_ManSimClassRefineOne( p, Gia_ObjRepr(p->pAig, i) );
            Vec_IntForEachEntry( p->vClassTemp, Ent, k )
                Cec_ManSimSimDeref( p, Ent );
        }
    }

    if ( p->pPars->fConstCorr )
    {
        Vec_IntForEachEntry( p->vRefinedC, i, k )
        {
            Gia_ObjSetRepr( p->pAig, i, GIA_VOID );
            Cec_ManSimSimDeref( p, i );
        }
        Vec_IntClear( p->vRefinedC );
    }

    if ( Vec_IntSize(p->vRefinedC) > 0 )
        Cec_ManSimProcessRefined( p, p->vRefinedC );
    assert( vInfoCis == NULL || iCiId == Gia_ManCiNum(p->pAig) );
    assert( vInfoCos == NULL || iCoId == Gia_ManCoNum(p->pAig) );
    assert( p->nMems == 1 );
    if ( p->nMems != 1 )
        Abc_Print( 1, "Cec_ManSimSimulateRound(): Memory management error!\n" );
    if ( p->pPars->fVeryVerbose )
        Gia_ManEquivPrintClasses( p->pAig, 0, Cec_MemUsage(p) );
    if ( p->pBestState )
        Cec_ManSimFindBestPattern( p );
/*
    if ( p->nMems > 1 ) {
        for ( i = 1; i < p->nObjs; i++ )
        if ( p->pSims[i] ) {
            int x = 0;
        }
    }
*/
    return Cec_ManSimAnalyzeOutputs( p );
}



/**Function*************************************************************

  Synopsis    [Creates simulation info for this round.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSimCreateInfo( Cec_ManSim_t * p, Vec_Ptr_t * vInfoCis, Vec_Ptr_t * vInfoCos )
{
    unsigned * pRes0, * pRes1;
    int i, w;
    if ( p->pPars->fSeqSimulate && Gia_ManRegNum(p->pAig) > 0 )
    {
        assert( vInfoCis && vInfoCos );
        for ( i = 0; i < Gia_ManPiNum(p->pAig); i++ )
        {
            pRes0 = (unsigned *)Vec_PtrEntry( vInfoCis, i );
            for ( w = 0; w < p->nWords; w++ )
                pRes0[w] = Gia_ManRandom( 0 );
        }
        for ( i = 0; i < Gia_ManRegNum(p->pAig); i++ )
        {
            pRes0 = (unsigned *)Vec_PtrEntry( vInfoCis, Gia_ManPiNum(p->pAig) + i );
            pRes1 = (unsigned *)Vec_PtrEntry( vInfoCos, Gia_ManPoNum(p->pAig) + i );
            for ( w = 0; w < p->nWords; w++ )
                pRes0[w] = pRes1[w];
        }
    }
    else 
    {
        for ( i = 0; i < Gia_ManCiNum(p->pAig); i++ )
        {
            pRes0 = (unsigned *)Vec_PtrEntry( vInfoCis, i );
            for ( w = 0; w < p->nWords; w++ )
                pRes0[w] = Gia_ManRandom( 0 );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the bug is found.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSimClassesPrepare( Cec_ManSim_t * p, int LevelMax )
{
    Gia_Obj_t * pObj;
    int i;
    assert( p->pAig->pReprs == NULL );
    // allocate representation
    p->pAig->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(p->pAig) );
    p->pAig->pNexts = ABC_CALLOC( int, Gia_ManObjNum(p->pAig) );
    // create references
    Gia_ManCreateValueRefs( p->pAig );
    // set starting representative of internal nodes to be constant 0
    if ( p->pPars->fLatchCorr )
        Gia_ManForEachObj( p->pAig, pObj, i )
            Gia_ObjSetRepr( p->pAig, i, GIA_VOID );
    else if ( LevelMax == -1 )
        Gia_ManForEachObj( p->pAig, pObj, i )
            Gia_ObjSetRepr( p->pAig, i, Gia_ObjIsAnd(pObj) ? 0 : GIA_VOID );
    else
    {
        Gia_ManLevelNum( p->pAig );
        Gia_ManForEachObj( p->pAig, pObj, i )
            Gia_ObjSetRepr( p->pAig, i, (Gia_ObjIsAnd(pObj) && Gia_ObjLevel(p->pAig,pObj) <= LevelMax) ? 0 : GIA_VOID );
        Vec_IntFreeP( &p->pAig->vLevels );
    }
    // if sequential simulation, set starting representative of ROs to be constant 0
    if ( p->pPars->fSeqSimulate )
        Gia_ManForEachRo( p->pAig, pObj, i )
            if ( pObj->Value )
                Gia_ObjSetRepr( p->pAig, Gia_ObjId(p->pAig, pObj), 0 );
    // perform simulation
    if ( p->pAig->nSimWords )
    {
        p->nWords = 2*p->pAig->nSimWords;
        assert( Vec_WrdSize(p->pAig->vSimsPi) == Gia_ManCiNum(p->pAig) * p->pAig->nSimWords ); 
        //Cec_ManSimCreateInfo( p, p->vCiSimInfo, p->vCoSimInfo );
        for ( i = 0; i < Gia_ManCiNum(p->pAig); i++ )
            memmove( Vec_PtrEntry(p->vCiSimInfo, i), Vec_WrdEntryP(p->pAig->vSimsPi, i*p->pAig->nSimWords), sizeof(word)*p->pAig->nSimWords );
        if ( Cec_ManSimSimulateRound( p, p->vCiSimInfo, p->vCoSimInfo ) )
            return 1;
        if ( p->pPars->fVerbose )
            Gia_ManEquivPrintClasses( p->pAig, 0, Cec_MemUsage(p) );
    }
    else
    {
        p->nWords = 1;
        do {
            if ( p->pPars->fVerbose )
                Gia_ManEquivPrintClasses( p->pAig, 0, Cec_MemUsage(p) );
            for ( i = 0; i < 4; i++ )
            {
                Cec_ManSimCreateInfo( p, p->vCiSimInfo, p->vCoSimInfo );
                if ( Cec_ManSimSimulateRound( p, p->vCiSimInfo, p->vCoSimInfo ) )
                    return 1;
            }
            p->nWords = 2 * p->nWords + 1;
        }
        while ( p->nWords <= p->pPars->nWords );
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the bug is found.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSimClassesRefine( Cec_ManSim_t * p )
{
    int i;
    Gia_ManCreateValueRefs( p->pAig );
    p->nWords = p->pPars->nWords;
    for ( i = 0; i < p->pPars->nRounds; i++ )
    {
        if ( (i % (p->pPars->nRounds / 5)) == 0 && p->pPars->fVerbose )
            Gia_ManEquivPrintClasses( p->pAig, 0, Cec_MemUsage(p) );
        Cec_ManSimCreateInfo( p, p->vCiSimInfo, p->vCoSimInfo );
        if ( Cec_ManSimSimulateRound( p, p->vCiSimInfo, p->vCoSimInfo ) )
            return 1;
    }
    if ( p->pPars->fVerbose )
        Gia_ManEquivPrintClasses( p->pAig, 0, Cec_MemUsage(p) );
    return 0;
}
////////////////////////////////////////////////////////////////////////
///       CBS-GUIDED SIMULATION (RIC3 rt_dfs_simulate via Circuit-SAT) ///
////////////////////////////////////////////////////////////////////////

/* Number of RI registers probed per DFS state.
   For each RI[j] we try two targets: RI[j]=1 then RI[j]=0.
   Total targets per call = 2 * CBS_DFS_MAX_RI. */
#define CBS_DFS_MAX_RI 8

/**Function*************************************************************

  Synopsis    [Lightweight polynomial hash of a next-state vector.]

  Description [Used for duplicate-next-state suppression in the DFS.
               Collisions are possible but acceptable – they merely cause
               the DFS to skip an occasional valid state, not to loop.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Cec_CbsStateHash( int * pState, int nReg )
{
    unsigned h = 2166136261u;   /* FNV-1a basis */
    int i;
    for ( i = 0; i < nReg; i++ )
        h = (h ^ (unsigned)pState[i]) * 16777619u;
    return h;
}

/**Function*************************************************************

  Synopsis    [CBS-based DFS exploration of reachable states.]

  Description [Given the current latch state pCurState[0..nReg-1],
               this function probes each RI-fanin node as a CBS "target"
               (forcing RI[j] output = 1 for j = 0..min(nReg,MAX_TARGETS)-1).
               For every SAT result the function:
                 1. Deduplicates against vSeen (a hash set of visited
                    next-states), preventing the DFS from re-entering an
                    already-explored state without needing blocking clauses.
                 2. Packs PI values (from CBS model) and current RO values
                    (= pCurState) as one simulation bit-pattern into
                    vCiSimInfo at slot *pBit.
                 3. Recurses into the discovered next state.

               Diversity across patterns comes from rotating the target
               RI register (j) so that CBS must justify a different circuit
               output on each call.

               *pBit is the next free bit slot; incremented per new pattern.
               nBits = 32*nWords is the capacity limit.]

  SideEffects [Modifies vCiSimInfo (bit-patterns); appends to vSeen.]

  SeeAlso     []

***********************************************************************/
static void Cec_ManCbsSimDfs( Cbs_Man_t * pCbs, Gia_Man_t * pAig,
    Gia_Obj_t ** ppRoObjs, Vec_Ptr_t * vCiSimInfo,
    int * pCurState, int * pBit, int nBits, Vec_Int_t * vSeen,
    int * pSimVals )
{
    Vec_Int_t  * vModel     = Cbs_ReadModel( pCbs );
    int          nPi        = Gia_ManPiNum( pAig );
    int          nReg       = Gia_ManRegNum( pAig );
    int          nObjNum    = Gia_ManObjNum( pAig );
    int          nRiTry     = Abc_MinInt( nReg, CBS_DFS_MAX_RI );
    int        * pNextState = ABC_ALLOC( int, nReg );
    int          i, j, k, dir, lit, status, cio_id, val;
    unsigned     h;
    Gia_Obj_t  * pObj, * pRiObj, * pTarget, * pTargetR;

    if ( *pBit >= nBits )
    {
        ABC_FREE( pNextState );
        return;
    }

    /* Probe CBS_DFS_MAX_RI registers in two directions each:
         dir=0: target makes RI[j] output = 1
         dir=1: target makes RI[j] output = 0  (Gia_Not of the dir=0 target)
       Trying both directions ensures we find patterns even when the circuit
       cannot produce RI[j]=1 from the current state (e.g. reset-state fixed
       points where all RI outputs are 0). */
    for ( j = 0; j < nRiTry; j++ )
    {
        for ( dir = 0; dir < 2; dir++ )
        {
            int entry, idx, found;

            if ( *pBit >= nBits )
                goto dfs_done;

            pRiObj   = Gia_ManRi( pAig, j );
            /* dir=0: child0 forces RI[j]=1; dir=1: Not(child0) forces RI[j]=0 */
            pTarget  = dir ? Gia_Not( Gia_ObjChild0(pRiObj) )
                           : Gia_ObjChild0( pRiObj );
            pTargetR = Gia_Regular( pTarget );

            /* Skip trivial targets: constants and free CIs give CBS nothing to
               justify and return trivial SAT with no useful PI assignments. */
            if ( Gia_ObjIsConst0( pTargetR ) || Gia_ObjIsCi( pTargetR ) )
                continue;

            /* Call CBS with RO = pCurState and the chosen target.
               We pass NULL for pRiFaninVals: next state is computed by
               forward simulation below, not extracted from CBS internals. */
            status = Cbs_ManSolveWithState( pCbs, pTarget,
                                            ppRoObjs, pCurState, nReg,
                                            NULL );
            if ( status != 0 )
                continue;   /* UNSAT or timeout: try next target */

            /* ------------------------------------------------------------------
               Forward simulation: compute the true next state from PI values
               (provided by CBS) and the current RO state.

               CBS backward justification only assigns nodes in the cone of the
               target RI; all other RI fanins remain unassigned.  Defaulting
               unassigned RI fanins to an arbitrary value would drive DFS into
               unreachable states and produce simulation vectors that split
               genuine equivalence classes.  Forward simulation avoids this by
               evaluating the circuit's combinational function exactly.

               Steps:
                 1. Zero the sim-value array (const0 = 0 is already correct).
                 2. Seed PIs from the CBS model; seed ROs from pCurState.
                 3. Propagate through AND/buffer nodes in topological order.
                 4. Read next-state values from RI fanins.
               ------------------------------------------------------------------ */
            memset( pSimVals, 0, (size_t)nObjNum * sizeof(int) );

            /* Step 2a: set PI values from CBS model.
               vModel entries: Abc_Var2Lit(Gia_ObjCioId(pCi), !value)
               → var = CioId, value = !(lit & 1).
               CioId 0..nPi-1 = PIs; CioId nPi..nPi+nReg-1 = ROs (skip). */
            Vec_IntForEachEntry( vModel, lit, i )
            {
                cio_id = Abc_Lit2Var( lit );
                val    = !Abc_LitIsCompl( lit );
                if ( cio_id < nPi )
                    pSimVals[ Gia_ObjId( pAig, Gia_ManCi(pAig, cio_id) ) ] = val;
            }

            /* Step 2b: set RO values from current state. */
            for ( k = 0; k < nReg; k++ )
                pSimVals[ Gia_ObjId( pAig, ppRoObjs[k] ) ] = pCurState[k];

            /* Step 3: propagate through AND/buffer nodes (topological order). */
            Gia_ManForEachAnd( pAig, pObj, i )
            {
                int v0 = pSimVals[ Gia_ObjFaninId0(pObj, i) ] ^ Gia_ObjFaninC0(pObj);
                int v1 = pSimVals[ Gia_ObjFaninId1(pObj, i) ] ^ Gia_ObjFaninC1(pObj);
                pSimVals[i] = v0 & v1;
            }

            /* Step 4: extract next-state values from RI fanins. */
            Gia_ManForEachRi( pAig, pRiObj, k )
                pNextState[k] = pSimVals[ Gia_ObjFaninId0p(pAig, pRiObj) ]
                                ^ Gia_ObjFaninC0( pRiObj );

            /* Deduplicate: skip if we have already recursed into this next state.
               A 32-bit FNV hash makes false duplicates negligibly rare. */
            h = Cec_CbsStateHash( pNextState, nReg );
            found = 0;
            Vec_IntForEachEntry( vSeen, entry, idx )
                if ( (unsigned)entry == h ) { found = 1; break; }
            if ( found )
                continue;
            Vec_IntPush( vSeen, (int)h );

            /* --- Pack PI values from the CBS model into vCiSimInfo at *pBit. --- */
            Vec_IntForEachEntry( vModel, lit, i )
            {
                cio_id = Abc_Lit2Var( lit );
                val    = !Abc_LitIsCompl( lit );
                if ( cio_id < nPi && val )
                    Abc_InfoSetBit( (unsigned *)Vec_PtrEntry(vCiSimInfo, cio_id),
                                    *pBit );
            }

            /* --- Pack current RO values (= pCurState) into vCiSimInfo[nPi+k]. --- */
            for ( k = 0; k < nReg; k++ )
                if ( pCurState[k] )
                    Abc_InfoSetBit( (unsigned *)Vec_PtrEntry(vCiSimInfo, nPi + k),
                                    *pBit );

            (*pBit)++;

            /* DFS: explore the discovered next state recursively. */
            Cec_ManCbsSimDfs( pCbs, pAig, ppRoObjs, vCiSimInfo,
                              pNextState, pBit, nBits, vSeen, pSimVals );
        } /* end dir loop */
    } /* end j loop */

dfs_done:
    ABC_FREE( pNextState );
}

/**Function*************************************************************

  Synopsis    [CBS-guided sequential simulation for equivalence class refinement.]

  Description [Replaces the old CNF/Tseitin approach with a Circuit-Based
               Solver (CBS) that operates directly on the GIA.  This
               eliminates the Tseitin-encoding overhead that made the
               previous sat_solver version slower than random simulation
               on large AIGs.

               The function initialises CBS on the current GIA, then runs
               a DFS (Cec_ManCbsSimDfs) that probes reachable successor
               states from the all-zero reset state.  Each discovered
               (PI, RO) pattern is packed into p->vCiSimInfo and forwarded
               to Cec_ManSimSimulateRound for equivalence-class refinement.

               Called after Cec_ManSimClassesPrepare + Cec_ManSimClassesRefine
               in Cec_ManLSCorrespondenceClasses (cecCorr.c).]

  SideEffects [Temporarily sets fMark0/fMark1/Value on GIA nodes (cleaned
               up by CBS internals before return).]

  SeeAlso     []

***********************************************************************/
int Cec_ManSimClassesSatGuided( Cec_ManSim_t * p )
{
    Gia_Man_t  * pAig      = p->pAig;
    int          nReg      = Gia_ManRegNum( pAig );
    int          nCi       = Gia_ManCiNum( pAig );
    int          nWords    = p->pPars->nWords;
    int          nBits     = 32 * nWords;
    Cbs_Man_t  * pCbs;
    Gia_Obj_t ** ppRoObjs;
    Vec_Int_t  * vSeen;
    Gia_Obj_t  * pObj;
    int        * pInitState;
    int        * pSimVals;
    int          i, bit, RetValue = 0;
    int          fCreatedRefs = 0;

    if ( nReg == 0 )
        return 0;

    /* Cbs_ManSolve_rec uses Gia_ObjRefNum for the decision heuristic, so
       pRefs must be populated.  Create it here if the caller has not done
       so already; track whether we own it so we can free it at the end. */
    if ( pAig->pRefs == NULL )
    {
        Gia_ManCreateRefs( pAig );
        fCreatedRefs = 1;
    }

    /* Prepare GIA for CBS: clear marks, fill Value (trail IDs), set phase. */
    Gia_ManCleanMark0( pAig );
    Gia_ManCleanMark1( pAig );
    Gia_ManFillValue( pAig );
    Gia_ManSetPhase( pAig );

    pCbs = Cbs_ManAlloc( pAig );
    /* Scale conflict/justification budgets with circuit size so CBS has a
       realistic chance of finding SAT assignments in large sequential designs.
       nBTLimit caps backtracks per call; nJustLimit caps the simultaneous
       justification frontier (governs timeouts on wide cones). */
    Cbs_ManSetConflictNum( pCbs, 5 );
    Cbs_ManSetJustLimit( pCbs, Abc_MaxInt( 100, Gia_ManAndNum(pAig) / 10 ) );

    /* Build an indexed array of RO GIA objects for fast assumption setup. */
    ppRoObjs = ABC_ALLOC( Gia_Obj_t *, nReg );
    Gia_ManForEachRo( pAig, pObj, i )
        ppRoObjs[i] = pObj;

    /* All-zero reset state (matches &scorr convention). */
    pInitState = ABC_CALLOC( int, nReg );
    /* Scratch space for forward simulation: one int per GIA object. */
    pSimVals   = ABC_ALLOC( int, Gia_ManObjNum(pAig) );

    /* Zero vCiSimInfo – CBS patterns will be written bit-by-bit.
       Bit 0 is forced all-zeros by Cec_ManSimSimulateRound itself,
       so we start filling from bit 1. */
    for ( i = 0; i < nCi; i++ )
        memset( Vec_PtrEntry(p->vCiSimInfo, i), 0,
                (size_t)nWords * sizeof(unsigned) );

    vSeen = Vec_IntAlloc( 64 );
    bit   = 1;
    Cec_ManCbsSimDfs( pCbs, pAig, ppRoObjs, p->vCiSimInfo,
                      pInitState, &bit, nBits, vSeen, pSimVals );
    Vec_IntFree( vSeen );

    if ( p->pPars->fVerbose )
        Abc_Print( 1, "CBS-guided sim: generated %d patterns (capacity %d).\n",
                   bit - 1, nBits - 1 );

    if ( bit > 1 )
    {
        Gia_ManCreateValueRefs( pAig );
        if ( Cec_ManSimSimulateRound( p, p->vCiSimInfo, p->vCoSimInfo ) )
            RetValue = 1;
        if ( p->pPars->fVerbose )
            Gia_ManEquivPrintClasses( pAig, 0, Cec_MemUsage(p) );
    }

    ABC_FREE( pSimVals );
    ABC_FREE( pInitState );
    ABC_FREE( ppRoObjs );
    Cbs_ManStop( pCbs );

    /* Restore clean marks for any code that runs after us. */
    Gia_ManCleanMark0( pAig );
    Gia_ManCleanMark1( pAig );

    /* Release pRefs only if we allocated it; leave it if the caller owns it. */
    if ( fCreatedRefs )
        ABC_FREE( pAig->pRefs );

    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

