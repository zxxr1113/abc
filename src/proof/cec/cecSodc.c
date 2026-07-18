/**CFile****************************************************************

  FileName    [cecSodc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable sequential synthesis under observability don't-cares.]

  Synopsis    [Research prototype of SODC redundancy removal/resubstitution.]

  Description [This implementation follows the proof discipline described in
  Marakkalage et al., TCAD 2025: candidate rewrites are committed one at a
  time, and each rewrite is checked under reset reachability by base-case and
  k-inductive signal correspondence.  Unlike the industrial implementation,
  this prototype uses a whole-design sequential miter instead of local SAT
  windows.  This makes it deliberately conservative and comparatively slow,
  but gives us a small, auditable baseline inside ABC.]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

void Cec_ManSodcSetDefaultParams( Cec_ParSodc_t * p )
{
    memset( p, 0, sizeof(Cec_ParSodc_t) );
    p->nFrames     = 1;
    p->nConfLimit  = 1000;
    p->nStepsMax   = -1;
    p->nCandMax    = 1000;
    p->nDivsMax    = 8;
    p->nChangesMax = 100;
    p->fUseScorr   = 1;
}

// Translate an old-GIA literal after its variable has been copied.
static inline int Cec_SodcCopyLit( Gia_Man_t * p, int iLit )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, Abc_Lit2Var(iLit) );
    assert( ~pObj->Value );
    return Abc_LitNotCond( pObj->Value, Abc_LitIsCompl(iLit) );
}

// Duplicate the GIA while replacing one fanin occurrence of one AND node.
// The divisor must precede the target in topological order.
static Gia_Man_t * Cec_SodcDupFanin( Gia_Man_t * p, int iTarget, int iFanin, int iDivLit )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, iLit0, iLit1;
    assert( iFanin == 0 || iFanin == 1 );
    assert( Abc_Lit2Var(iDivLit) < iTarget );
    assert( Gia_ObjIsAnd(Gia_ManObj(p, iTarget)) );
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Gia_ObjFanin0Copy( pObj );
        iLit1 = Gia_ObjFanin1Copy( pObj );
        if ( i == iTarget )
        {
            if ( iFanin == 0 )
                iLit0 = Cec_SodcCopyLit( p, iDivLit );
            else
                iLit1 = Cec_SodcCopyLit( p, iDivLit );
        }
        pObj->Value = Gia_ManHashAnd( pNew, iLit0, iLit1 );
    }
    Gia_ManForEachCo( p, pObj, i )
        pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    pNew = Gia_ManDupNormalize( pTemp = pNew, 0 );
    Gia_ManStop( pTemp );
    pNew = Gia_ManSeqCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

static int Cec_SodcAllPosAreZero( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachPo( p, pObj, i )
        if ( Gia_ObjFaninId0p(p, pObj) != 0 || Gia_ObjFaninC0(pObj) )
            return 0;
    return 1;
}

// A proof succeeds only when scorr reduces every sequential-miter output to 0.
// SAT timeouts/unknown candidates therefore cannot be committed.
static int Cec_SodcProveCandidate( Gia_Man_t * p, Gia_Man_t * pCand, Cec_ParSodc_t * pPars )
{
    Cec_ParCor_t Cor;
    Gia_Man_t * pMiter, * pReduced;
    int fProved;
    pMiter = Gia_ManMiter( p, pCand, 0, 0, 1, 0, 0 );
    if ( pMiter == NULL )
        return 0;
    Cec_ManCorSetDefaultParams( &Cor );
    Cor.nFrames   = pPars->nFrames;
    Cor.nBTLimit  = pPars->nConfLimit;
    Cor.nStepsMax = pPars->nStepsMax;
    Cor.fVerbose  = 0;
    pReduced = Cec_ManLSCorrespondence( pMiter, &Cor );
    fProved = Cec_SodcAllPosAreZero( pReduced );
    Gia_ManStop( pReduced );
    Gia_ManStop( pMiter );
    return fProved;
}

static Gia_Man_t * Cec_SodcRunScorr( Gia_Man_t * p, Cec_ParSodc_t * pPars )
{
    Cec_ParCor_t Cor;
    Cec_ManCorSetDefaultParams( &Cor );
    Cor.nFrames   = pPars->nFrames;
    Cor.nBTLimit  = pPars->nConfLimit;
    Cor.nStepsMax = pPars->nStepsMax;
    Cor.fVerbose  = pPars->fVerbose;
    return Cec_ManLSCorrespondence( p, &Cor );
}

Gia_Man_t * Cec_ManSodcSynthesis( Gia_Man_t * pGia, Cec_ParSodc_t * pPars )
{
    Gia_Man_t * p, * pCand, * pTemp;
    Gia_Obj_t * pObj;
    int i, f, d, iDiv, iDivLit, iFanLit;
    int nTried = 0, nProved = 0, nChanges = 0, fChanged;
    abctime clk = Abc_Clock();
    assert( Gia_ManRegNum(pGia) > 0 );
    p = Gia_ManDup( pGia );
    if ( pPars->fUseScorr )
    {
        pTemp = Cec_SodcRunScorr( p, pPars );
        Gia_ManStop( p );
        p = pTemp;
    }
    do
    {
        fChanged = 0;
        Gia_ManForEachAnd( p, pObj, i )
        {
            for ( f = 0; f < 2 && !fChanged; f++ )
            {
                iFanLit = f ? Gia_ObjFaninLit1(pObj, i) : Gia_ObjFaninLit0(pObj, i);
                // Constants first: 0 removes the node; 1 bypasses this fanin.
                for ( d = -2; d < 2 * pPars->nDivsMax && !fChanged; d++ )
                {
                    if ( nTried >= pPars->nCandMax || nChanges >= pPars->nChangesMax )
                        break;
                    if ( d == -2 )
                        iDivLit = 0;
                    else if ( d == -1 )
                        iDivLit = 1;
                    else
                    {
                        iDiv = i - 1 - d / 2;
                        if ( iDiv < 1 )
                            break;
                        iDivLit = Abc_Var2Lit( iDiv, d & 1 );
                    }
                    if ( iDivLit == iFanLit )
                        continue;
                    pCand = Cec_SodcDupFanin( p, i, f, iDivLit );
                    if ( Gia_ManRegNum(pCand) == 0 )
                    {
                        Gia_ManStop( pCand );
                        continue;
                    }
                    // The TCAD objective is area.  Do not spend a proof on a
                    // candidate that does not immediately reduce AIG nodes.
                    if ( Gia_ManAndNum(pCand) + Gia_ManRegNum(pCand) >=
                         Gia_ManAndNum(p)     + Gia_ManRegNum(p) )
                    {
                        Gia_ManStop( pCand );
                        continue;
                    }
                    nTried++;
                    if ( pPars->fVerbose )
                        Abc_Print( 1, "SODC try %d: obj %d fanin %d -> lit %d, AND %d -> %d.\n",
                            nTried, i, f, iDivLit, Gia_ManAndNum(p), Gia_ManAndNum(pCand) );
                    if ( Cec_SodcProveCandidate( p, pCand, pPars ) )
                    {
                        if ( pPars->fVerbose )
                            Abc_Print( 1, "SODC accepted: obj %d fanin %d -> lit %d.\n", i, f, iDivLit );
                        Gia_ManStop( p );
                        p = pCand;
                        nProved++;
                        nChanges++;
                        fChanged = 1;
                    }
                    else
                        Gia_ManStop( pCand );
                }
            }
            if ( fChanged || nTried >= pPars->nCandMax || nChanges >= pPars->nChangesMax )
                break;
        }
    }
    while ( fChanged && nTried < pPars->nCandMax && nChanges < pPars->nChangesMax );
    if ( pPars->fUseScorr )
    {
        pTemp = Cec_SodcRunScorr( p, pPars );
        Gia_ManStop( p );
        p = pTemp;
    }
    Abc_Print( 1, "SODC prototype: tried = %d, accepted = %d, AND = %d -> %d, time = %.2f sec.\n",
        nTried, nProved, Gia_ManAndNum(pGia), Gia_ManAndNum(p),
        1.0 * (Abc_Clock() - clk) / CLOCKS_PER_SEC );
    return p;
}

ABC_NAMESPACE_IMPL_END
