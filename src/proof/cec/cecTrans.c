/**CFile****************************************************************

  FileName    [cecTrans.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential transduction using SODC proof obligations.]

  Synopsis    [Candidate-and-prove sequential redundancy addition.]

  Description [This command is intentionally independent of &sodc.  It uses
  the BMC/induction machinery behind signal correspondence only as a bounded
  sequential proof oracle.  Its search space is speculative transduction:
  find a costly victim fanin, replace it with an existing or constructed
  divisor, clean up the speculative network, and commit only a proved,
  positive-gain transaction.]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

void Cec_ManTranSetDefaultParams( Cec_ParTran_t * p )
{
    memset( p, 0, sizeof(Cec_ParTran_t) );
    p->nFrames     = 1;
    p->nBTLimit    = 1000;
    p->nStepsMax   = -1;
    p->nCandMax    = 1000;
    p->nDivsMax    = 16;
    p->nConstrMax  = 16;
    p->nChangesMax = 100;
    p->nGainMin    = 1;
    p->fUseConstr  = 1;
}

// Convert an old-network literal into its literal in the network currently
// being duplicated.  All candidate divisors precede the target, so their
// copies are available when the target is rebuilt.
static inline int Cec_TranCopyLit( Gia_Man_t * p, int iLit )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, Abc_Lit2Var(iLit) );
    assert( ~pObj->Value );
    return Abc_LitNotCond( pObj->Value, Abc_LitIsCompl(iLit) );
}

// Build one speculative transaction.  div1 == -1 means that the victim is
// replaced by an existing literal div0.  Otherwise the replacement is the
// constructed one-AND divisor (div0 & div1).  Cleanup gives the exact local
// structural gain, rather than an unreliable MFFC estimate.
static Gia_Man_t * Cec_TranDupFanin( Gia_Man_t * p, int iTarget, int iFanin,
    int iDiv0, int iDiv1 )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, iLit0, iLit1, iRep;
    assert( iFanin == 0 || iFanin == 1 );
    assert( Abc_Lit2Var(iDiv0) < iTarget );
    assert( iDiv1 == -1 || Abc_Lit2Var(iDiv1) < iTarget );
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + 4 );
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
            iRep = Cec_TranCopyLit( p, iDiv0 );
            if ( iDiv1 != -1 )
                iRep = Gia_ManHashAnd( pNew, iRep, Cec_TranCopyLit(p, iDiv1) );
            if ( iFanin == 0 )
                iLit0 = iRep;
            else
                iLit1 = iRep;
        }
        pObj->Value = Gia_ManHashAnd( pNew, iLit0, iLit1 );
    }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
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

static int Cec_TranGain( Gia_Man_t * p, Gia_Man_t * pCand )
{
    return Gia_ManAndNum(p) + Gia_ManRegNum(p)
         - Gia_ManAndNum(pCand) - Gia_ManRegNum(pCand);
}

static int Cec_TranTryDry( Gia_Man_t * p, Cec_ParTran_t * pPars,
    int iTarget, int iFanin, int iDiv0, int iDiv1, int * pnPos )
{
    Gia_Man_t * pCand;
    int Gain;
    pCand = Cec_TranDupFanin( p, iTarget, iFanin, iDiv0, iDiv1 );
    Gain = Cec_TranGain( p, pCand );
    if ( Gain >= pPars->nGainMin && Gia_ManRegNum(pCand) > 0 )
    {
        (*pnPos)++;
        if ( pPars->fVerbose )
            Abc_Print( 1, "  candidate: n%d.f%d <- %d%s%d  gain=%d\n", iTarget,
                iFanin, iDiv0, iDiv1 == -1 ? "" : " & ",
                iDiv1 == -1 ? 0 : iDiv1, Gain );
    }
    Gia_ManStop( pCand );
    return Gain;
}

Gia_Man_t * Cec_ManSequentialTransduction( Gia_Man_t * pGia, Cec_ParTran_t * pPars )
{
    Gia_Obj_t * pObj;
    int i, f, d, e, iDiv0, iDiv1, nConstructedOne;
    int nExisting = 0, nConstructed = 0, nPositive = 0, nTried = 0;
    assert( Gia_ManRegNum(pGia) > 0 );
    Abc_Print( 1, "Sequential transduction: AND = %d, Reg = %d, frames = %d, conf = %d.\n",
        Gia_ManAndNum(pGia), Gia_ManRegNum(pGia), pPars->nFrames, pPars->nBTLimit );
    // Structural filtering is free: a topologically earlier object cannot be
    // in the target's TFO, so it cannot create a combinational cycle.  The
    // exact sequential/SODC test is deliberately deferred to the next stage.
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        for ( f = 0; f < 2; f++ )
        {
            nConstructedOne = 0;
            for ( d = 1; d <= pPars->nDivsMax && i - d > 0 && nTried < pPars->nCandMax; d++ )
            {
                iDiv0 = Abc_Var2Lit( i - d, d & 1 );
                if ( iDiv0 == (f ? Gia_ObjFaninLit1(pObj, i) : Gia_ObjFaninLit0(pObj, i)) )
                    continue;
                nExisting++;
                nTried++;
                Cec_TranTryDry( pGia, pPars, i, f, iDiv0, -1, &nPositive );
            }
            if ( !pPars->fUseConstr )
                continue;
            for ( d = 1; d <= pPars->nDivsMax && i - d > 1 && nConstructedOne < pPars->nConstrMax && nTried < pPars->nCandMax; d++ )
            {
                for ( e = d + 1; e <= pPars->nDivsMax && i - e > 0 && nConstructedOne < pPars->nConstrMax && nTried < pPars->nCandMax; e++ )
                {
                    iDiv0 = Abc_Var2Lit( i - d, 0 );
                    iDiv1 = Abc_Var2Lit( i - e, 0 );
                    nConstructed++;
                    nConstructedOne++;
                    nTried++;
                    Cec_TranTryDry( pGia, pPars, i, f, iDiv0, iDiv1, &nPositive );
                }
            }
        }
        if ( nTried >= pPars->nCandMax )
            break;
    }
    Abc_Print( 1, "Sequential transduction candidates: tried=%d existing=%d constructed=%d positive-gain=%d.\n",
        nTried, nExisting, nConstructed, nPositive );
    return Gia_ManDup( pGia );
}

ABC_NAMESPACE_IMPL_END
