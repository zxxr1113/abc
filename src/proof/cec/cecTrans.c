/**CFile****************************************************************

  FileName    [cecTrans.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential transduction using SODC proof obligations.]

  Synopsis    [Candidate-and-prove sequential redundancy addition.]

  Description [This command is intentionally independent of &sodc.  It uses
  the BMC/induction machinery behind signal correspondence only as a bounded
  sequential proof oracle.  Its search space is speculative transduction:
  find a costly victim fanin, derive an added divisor, prove that adding it
  is redundant, prove that it makes the victim removable, and commit only a
  proved positive-gain transaction.]

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
    p->nSimWords   = 4;
    p->nSimFrames  = 8;
    p->fUseConstr  = 1;
}

// A signature is a collection of independent reset-reachable random traces.
// Every word carries 64 traces in parallel; consecutive frame groups carry
// the successive states of each trace.  These signatures only guide search:
// all accepted edits are still discharged by the sequential proof oracle.
typedef struct Cec_TranSim_t_ Cec_TranSim_t;
struct Cec_TranSim_t_
{
    Gia_Man_t *     pGia;
    int             nWords;
    int             nFrames;
    int             nSlots;
    word *          pSims;          // [object ID][frame * nWords + word]
    word *          pState;         // current values of the ROs
};

static inline word * Cec_TranSimObj( Cec_TranSim_t * p, int iObj )
{
    return p->pSims + (size_t)iObj * p->nSlots;
}

static inline word Cec_TranSimLit( Cec_TranSim_t * p, int iLit, int iSlot )
{
    return Cec_TranSimObj(p, Abc_Lit2Var(iLit))[iSlot] ^
        (Abc_LitIsCompl(iLit) ? ~(word)0 : 0);
}

static Cec_TranSim_t * Cec_TranSimStart( Gia_Man_t * pGia, Cec_ParTran_t * pPars )
{
    Cec_TranSim_t * p;
    Gia_Obj_t * pObj, * pObjRi, * pObjRo;
    int f, w, i, iSlot, iFan0, iFan1;
    word v0, v1;
    p = ABC_CALLOC( Cec_TranSim_t, 1 );
    p->pGia = pGia;
    p->nWords = pPars->nSimWords;
    p->nFrames = pPars->nSimFrames;
    p->nSlots = p->nWords * p->nFrames;
    p->pSims = ABC_CALLOC( word, (size_t)Gia_ManObjNum(pGia) * p->nSlots );
    p->pState = ABC_CALLOC( word, (size_t)Gia_ManRegNum(pGia) * p->nWords );
    Abc_RandomW( 1 );
    for ( f = 0; f < p->nFrames; f++ )
    {
        for ( w = 0; w < p->nWords; w++ )
        {
            iSlot = f * p->nWords + w;
            Gia_ManForEachPi( pGia, pObj, i )
                Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot] = Abc_RandomW(0);
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
    ABC_FREE( p->pSims );
    ABC_FREE( p->pState );
    ABC_FREE( p );
}

// This is the conservative first implementation of the specification from
// the design document.  It deliberately takes C_i=1, so it recognizes
// requirements at the target itself and never treats sampled ODC as proof.
// Phase C will replace this with exact sequential-TFO care masks.
static int Cec_TranSigMatches( Cec_TranSim_t * p, int iTarget, int iFanin,
    int iDiv0, int iDiv1, int fDivCompl )
{
    Gia_Obj_t * pTarget = Gia_ManObj( p->pGia, iTarget );
    int iVictim = iFanin ? Gia_ObjFaninLit1p(p->pGia, pTarget) : Gia_ObjFaninLit0p(p->pGia, pTarget);
    int iOther  = iFanin ? Gia_ObjFaninLit0p(p->pGia, pTarget) : Gia_ObjFaninLit1p(p->pGia, pTarget);
    int s;
    word k, q, h;
    for ( s = 0; s < p->nSlots; s++ )
    {
        k = Cec_TranSimLit( p, iVictim, s );
        q = Cec_TranSimLit( p, iOther, s );
        h = Cec_TranSimLit( p, iDiv0, s );
        if ( iDiv1 != -1 )
            h &= Cec_TranSimLit( p, iDiv1, s );
        if ( fDivCompl )
            h = ~h;
        if ( (k & q & ~h) || (~k & q & h) )
            return 0;
    }
    return 1;
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

// Build one explicit stage of an add-then-remove transaction.  In add mode,
// target = old_target & h.  In removal mode, target = other_fanin & h, which
// is the result of removing the selected victim fanin after h was added.
// div1 == -1 selects an existing literal; otherwise h = div0 & div1.
static Gia_Man_t * Cec_TranDupEdit( Gia_Man_t * p, int iTarget, int iFanin,
    int iDiv0, int iDiv1, int fDivCompl, int fAdd )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, iLit0, iLit1, iOld, iOther, iRep;
    assert( iFanin == 0 || iFanin == 1 );
    assert( fDivCompl == 0 || fDivCompl == 1 );
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
            if ( fDivCompl )
                iRep = Abc_LitNot( iRep );
            if ( fAdd )
            {
                iOld = Gia_ManHashAnd( pNew, iLit0, iLit1 );
                pObj->Value = Gia_ManHashAnd( pNew, iOld, iRep );
            }
            else
            {
                iOther = iFanin == 0 ? iLit1 : iLit0;
                pObj->Value = Gia_ManHashAnd( pNew, iOther, iRep );
            }
            continue;
        }
        pObj->Value = Gia_ManHashAnd( pNew, iLit0, iLit1 );
    }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

// Cleanup is deliberately separated from the logical transaction.  Formal
// obligations are proved on the explicit add/remove structures; the cleaned
// copy is used only for exact cost and, after both proofs, for commit.
static Gia_Man_t * Cec_TranCleanup( Gia_Man_t * p )
{
    Gia_Man_t * pNew, * pTemp;
    pNew = Gia_ManCleanup( pTemp = Gia_ManDup(p) );
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

static int Cec_TranAllPosAreZero( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachPo( p, pObj, i )
        if ( Gia_ObjFaninId0p(p, pObj) != 0 || Gia_ObjFaninC0(pObj) )
            return 0;
    return 1;
}

static inline int Cec_TranVecLit( Vec_Int_t * vLits, int iLit )
{
    int iCopy = Vec_IntEntry( vLits, Abc_Lit2Var(iLit) );
    assert( iCopy >= 0 );
    return Abc_LitNotCond( iCopy, Abc_LitIsCompl(iLit) );
}

static inline int Cec_TranHashGate( Gia_Man_t * pNew, Gia_Obj_t * pObj, int iLit0, int iLit1 )
{
    return Gia_ObjIsXor(pObj) ? Gia_ManHashXor(pNew, iLit0, iLit1) :
        Gia_ManHashAnd(pNew, iLit0, iLit1);
}

// Mark the complete combinational TFO of the edited target, including the
// PO/RI boundaries.  A marked RI is emitted as a difference PO by the local
// miter; its corresponding RO is then related inductively by the common
// source-state machine built below.
static char * Cec_TranMarkTfo( Gia_Man_t * p, int iTarget )
{
    Gia_Obj_t * pObj;
    Vec_Int_t * vQueue = Vec_IntAlloc( 100 );
    char * pMark = ABC_CALLOC( char, Gia_ManObjNum(p) );
    int i, k, iFan;
    Gia_ManStaticFanoutStart( p );
    pMark[iTarget] = 1;
    Vec_IntPush( vQueue, iTarget );
    for ( i = 0; i < Vec_IntSize(vQueue); i++ )
    {
        int iObj = Vec_IntEntry( vQueue, i );
        for ( k = 0; k < Gia_ObjFanoutNumId(p, iObj); k++ )
        {
            iFan = Gia_ObjFanoutId( p, iObj, k );
            if ( pMark[iFan] )
                continue;
            pMark[iFan] = 1;
            pObj = Gia_ManObj( p, iFan );
            if ( !Gia_ObjIsCo(pObj) )
                Vec_IntPush( vQueue, iFan );
        }
    }
    Gia_ManStaticFanoutStop( p );
    Vec_IntFree( vQueue );
    return pMark;
}

// Construct a single-state sequential difference machine.  It shares the
// original transition relation, duplicates only the target's combinational
// TFO for the edited variant, and emits differences at all affected PO/RI
// boundaries.  Equality of the affected RIs, together with unchanged
// unmarked RIs, inductively establishes a common state trajectory.  Thus this
// is an exact COI reduction for these pure combinational edits, not a bounded
// window approximation.
static Gia_Man_t * Cec_TranBuildLocalMiter( Gia_Man_t * p, int iTarget, int iFanin,
    int iDiv0, int iDiv1, int fDivCompl, int fRemove )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vBase, * vEdit;
    char * pMark;
    int i, iLit0, iLit1, iOld, iOther, iRep, iEdit, nOuts = 0;
    assert( !Gia_ObjIsXor(Gia_ManObj(p, iTarget)) );
    pMark = Cec_TranMarkTfo( p, iTarget );
    vBase = Vec_IntStartFull( Gia_ManObjNum(p) );
    vEdit = Vec_IntStartFull( Gia_ManObjNum(p) );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + Gia_ManAndNum(p) / 4 + 100 );
    pNew->pName = Abc_UtilStrsav( "stran_local_miter" );
    Gia_ManHashAlloc( pNew );
    Vec_IntWriteEntry( vBase, 0, 0 );
    Vec_IntWriteEntry( vEdit, 0, 0 );
    Gia_ManForEachCi( p, pObj, i )
    {
        iEdit = Gia_ManAppendCi( pNew );
        Vec_IntWriteEntry( vBase, Gia_ObjId(p, pObj), iEdit );
        Vec_IntWriteEntry( vEdit, Gia_ObjId(p, pObj), iEdit );
    }
    Gia_ManForEachAnd( p, pObj, i )
    {
        iLit0 = Cec_TranVecLit( vBase, Gia_ObjFaninLit0p(p, pObj) );
        iLit1 = Cec_TranVecLit( vBase, Gia_ObjFaninLit1p(p, pObj) );
        iOld = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
        Vec_IntWriteEntry( vBase, i, iOld );
        if ( !pMark[i] )
        {
            Vec_IntWriteEntry( vEdit, i, iOld );
            continue;
        }
        if ( i == iTarget )
        {
            iRep = Cec_TranVecLit( vBase, iDiv0 );
            if ( iDiv1 != -1 )
                iRep = Gia_ManHashAnd( pNew, iRep, Cec_TranVecLit(vBase, iDiv1) );
            if ( fDivCompl )
                iRep = Abc_LitNot( iRep );
            if ( !fRemove )
                iEdit = Gia_ManHashAnd( pNew, iOld, iRep );
            else
            {
                iOther = iFanin ? iLit0 : iLit1;
                iEdit = Gia_ManHashAnd( pNew, iOther, iRep );
            }
        }
        else
        {
            iLit0 = Cec_TranVecLit( vEdit, Gia_ObjFaninLit0p(p, pObj) );
            iLit1 = Cec_TranVecLit( vEdit, Gia_ObjFaninLit1p(p, pObj) );
            iEdit = Cec_TranHashGate( pNew, pObj, iLit0, iLit1 );
        }
        Vec_IntWriteEntry( vEdit, i, iEdit );
    }
    // PO and affected-RI difference outputs must precede all RIs in a Gia.
    Gia_ManForEachPo( p, pObj, i )
    {
        int iDriver = Gia_ObjFaninId0p( p, pObj );
        if ( !pMark[iDriver] )
            continue;
        Gia_ManAppendCo( pNew, Gia_ManHashXor(pNew,
            Cec_TranVecLit(vBase, Gia_ObjFaninLit0p(p, pObj)),
            Cec_TranVecLit(vEdit, Gia_ObjFaninLit0p(p, pObj))) );
        nOuts++;
    }
    Gia_ManForEachRi( p, pObj, i )
    {
        int iDriver = Gia_ObjFaninId0p( p, pObj );
        if ( !pMark[iDriver] )
            continue;
        Gia_ManAppendCo( pNew, Gia_ManHashXor(pNew,
            Cec_TranVecLit(vBase, Gia_ObjFaninLit0p(p, pObj)),
            Cec_TranVecLit(vEdit, Gia_ObjFaninLit0p(p, pObj))) );
        nOuts++;
    }
    assert( nOuts > 0 );
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManAppendCo( pNew, Cec_TranVecLit(vBase, Gia_ObjFaninLit0p(p, pObj)) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Vec_IntFree( vBase );
    Vec_IntFree( vEdit );
    ABC_FREE( pMark );
    // Normalization installs the object-copy/value metadata expected by the
    // scorr simulation manager and also removes any structurally-zero local
    // difference output.
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    pNew = Gia_ManDupNormalize( pTemp = pNew, 0 );
    Gia_ManStop( pTemp );
    return pNew;
}

// This is intentionally the same sequential proof engine used by &scorr:
// bounded reset-reachable BMC followed by its inductive correspondence
// refinement.  The difference is the query: &stran proves a proposed
// transduction transaction, rather than asking scorr to merge an equivalence
// class in the original network.
static int Cec_TranProveWhole( Gia_Man_t * p, Gia_Man_t * pCand, Cec_ParTran_t * pPars )
{
    Cec_ParCor_t Cor;
    Gia_Man_t * pMiter, * pReduced;
    int fProved;
    pMiter = Gia_ManMiter( p, pCand, 0, 0, 1, 0, 0 );
    if ( pMiter == NULL )
        return 0;
    Cec_ManCorSetDefaultParams( &Cor );
    Cor.nFrames   = pPars->nFrames;
    Cor.nBTLimit  = pPars->nBTLimit;
    Cor.nStepsMax = pPars->nStepsMax;
    Cor.fVerbose  = 0;
    pReduced = Cec_ManLSCorrespondence( pMiter, &Cor );
    fProved = Cec_TranAllPosAreZero( pReduced );
    Gia_ManStop( pReduced );
    Gia_ManStop( pMiter );
    return fProved;
}

static int Cec_TranProveTransaction( Gia_Man_t * p, Gia_Man_t * pWhole0,
    Gia_Man_t * pWhole1, Cec_ParTran_t * pPars, int iTarget, int iFanin,
    int iDiv0, int iDiv1, int fDivCompl, int fRemove )
{
    Cec_ParCor_t Cor;
    Gia_Man_t * pMiter, * pReduced;
    int fProved;
    pMiter = Cec_TranBuildLocalMiter( p, iTarget, iFanin, iDiv0, iDiv1, fDivCompl, fRemove );
    Cec_ManCorSetDefaultParams( &Cor );
    Cor.nFrames   = pPars->nFrames;
    Cor.nBTLimit  = pPars->nBTLimit;
    Cor.nStepsMax = pPars->nStepsMax;
    Cor.fVerbose  = 0;
    pReduced = Cec_ManLSCorrespondence( pMiter, &Cor );
    fProved = Cec_TranAllPosAreZero( pReduced );
    Gia_ManStop( pReduced );
    Gia_ManStop( pMiter );
    if ( fProved && pPars->fShadow )
        fProved = Cec_TranProveWhole( pWhole0, pWhole1, pPars );
    return fProved;
}

// The candidate has already passed the exact structural-gain test.  This
// routine is the transactional boundary: no speculative wiring reaches p
// unless the sequential miter is discharged by scorr's proof infrastructure.
static int Cec_TranTryCommit( Gia_Man_t ** pp, Cec_ParTran_t * pPars,
    int iTarget, int iFanin, int iDiv0, int iDiv1, int fDivCompl, int * pnTried,
    int * pnPositive, int * pnAccepted )
{
    Gia_Man_t * p = *pp, * pAdd, * pFinal, * pCand;
    int Gain;
    pAdd   = Cec_TranDupEdit( p, iTarget, iFanin, iDiv0, iDiv1, fDivCompl, 1 );
    pFinal = Cec_TranDupEdit( p, iTarget, iFanin, iDiv0, iDiv1, fDivCompl, 0 );
    pCand  = Cec_TranCleanup( pFinal );
    Gain = Cec_TranGain( p, pCand );
    if ( Gain < pPars->nGainMin || Gia_ManRegNum(pCand) == 0 )
    {
        Gia_ManStop( pAdd );
        Gia_ManStop( pFinal );
        Gia_ManStop( pCand );
        return 0;
    }
    (*pnPositive)++;
    (*pnTried)++;
    if ( pPars->fVerbose )
    {
        if ( iDiv1 == -1 )
            Abc_Print( 1, "  proof %d: n%d.f%d <- lit%d  gain=%d\n",
                *pnTried, iTarget, iFanin, iDiv0, Gain );
        else if ( !fDivCompl )
            Abc_Print( 1, "  proof %d: n%d.f%d <- (lit%d & lit%d)  gain=%d\n",
                *pnTried, iTarget, iFanin, iDiv0, iDiv1, Gain );
        else
            Abc_Print( 1, "  proof %d: n%d.f%d <- !(lit%d & lit%d)  gain=%d\n",
                *pnTried, iTarget, iFanin, iDiv0, iDiv1, Gain );
    }
    // Strict transduction proof: first retain the newly added wire, then
    // prove removal.  The local miter shares p's state transition: after the
    // retention proof, p and pAdd have the same reachable states, so proving
    // add-vs-final differences on that state relation is exact.
    if ( !Cec_TranProveTransaction(p, p, pAdd, pPars, iTarget, iFanin, iDiv0, iDiv1, fDivCompl, 0) ||
         !Cec_TranProveTransaction(p, pAdd, pFinal, pPars, iTarget, iFanin, iDiv0, iDiv1, fDivCompl, 1) )
    {
        Gia_ManStop( pAdd );
        Gia_ManStop( pFinal );
        Gia_ManStop( pCand );
        return 0;
    }
    if ( pPars->fVerbose )
        Abc_Print( 1, "  accepted transaction: obj %d fanin %d, gain=%d.\n",
            iTarget, iFanin, Gain );
    Gia_ManStop( p );
    Gia_ManStop( pAdd );
    Gia_ManStop( pFinal );
    *pp = pCand;
    (*pnAccepted)++;
    return 1;
}

Gia_Man_t * Cec_ManSequentialTransduction( Gia_Man_t * pGia, Cec_ParTran_t * pPars )
{
    Gia_Man_t * p;
    Gia_Obj_t * pObj, * pDiv;
    Cec_TranSim_t * pSim;
    Vec_Int_t * vMatches, * vBases, * vConstr;
    int i, f, d, e, j, iDiv0, iDiv1, fDivCompl, iEntry;
    int nExisting = 0, nConstructed = 0, nPositive = 0, nTried = 0, nAccepted = 0;
    int nSigChecks = 0, nSigRejected = 0, nSigMatched = 0;
    int nVictim, nBaseLimit, nConstrLimit;
    int fChanged;
    abctime clk = Abc_Clock();
    assert( Gia_ManRegNum(pGia) > 0 );
    Abc_Print( 1, "Sequential transduction: AND = %d, Reg = %d, frames = %d, conf = %d.\n",
        Gia_ManAndNum(pGia), Gia_ManRegNum(pGia), pPars->nFrames, pPars->nBTLimit );
    p = Gia_ManDup( pGia );
    do
    {
        fChanged = 0;
        // Signatures are rebuilt after every committed transaction.  This is
        // intentionally conservative while structural edit caches do not yet
        // exist; no candidate is ever proved against a stale snapshot.
        pSim = Cec_TranSimStart( p, pPars );
        // Structural filtering is free: a topologically earlier object cannot
        // be in the target's TFO, so it cannot create a combinational cycle.
        Gia_ManForEachAnd( p, pObj, i )
        {
            if ( Gia_ObjIsXor(pObj) )
                continue;
            for ( f = 0; f < 2 && !fChanged; f++ )
            {
                nVictim = f ? Gia_ObjFaninLit1(pObj, i) : Gia_ObjFaninLit0(pObj, i);
                vMatches = Vec_IntAlloc( pPars->nDivsMax );
                // Test the full topologically-safe pool with bit-parallel
                // Must1/Must0 masks, but retain only the nearest matching
                // literals for expensive formal proof attempts.
                for ( d = i - 1; d > 0; d-- )
                {
                    pDiv = Gia_ManObj( p, d );
                    if ( !Gia_ObjIsCand(pDiv) )
                        continue;
                    for ( fDivCompl = 0; fDivCompl < 2; fDivCompl++ )
                    {
                        iDiv0 = Abc_Var2Lit( d, fDivCompl );
                        if ( iDiv0 == nVictim )
                            continue;
                        nExisting++;
                        nSigChecks++;
                        if ( !Cec_TranSigMatches(pSim, i, f, iDiv0, -1, 0) )
                        {
                            nSigRejected++;
                            continue;
                        }
                        nSigMatched++;
                        if ( pPars->nDivsMax == 0 || Vec_IntSize(vMatches) < pPars->nDivsMax )
                            Vec_IntPush( vMatches, iDiv0 );
                    }
                }
                Vec_IntForEachEntry( vMatches, iDiv0, j )
                {
                    if ( nTried >= pPars->nCandMax )
                        break;
                    fChanged = Cec_TranTryCommit( &p, pPars, i, f, iDiv0, -1, 0,
                        &nTried, &nPositive, &nAccepted );
                    if ( fChanged )
                        break;
                }
                Vec_IntFree( vMatches );
                if ( !pPars->fUseConstr || fChanged || pPars->nConstrMax == 0 )
                    continue;

                // A bounded base pool makes the O(D^2 W) construction pass
                // predictable.  Its literals include both phases, so AND and
                // complemented-AND cover AND/OR/AND-NOT forms.
                nBaseLimit = pPars->nDivsMax ? pPars->nDivsMax : 64;
                nConstrLimit = pPars->nConstrMax;
                vBases = Vec_IntAlloc( nBaseLimit );
                for ( d = i - 1; d > 0 && Vec_IntSize(vBases) < nBaseLimit; d-- )
                {
                    pDiv = Gia_ManObj( p, d );
                    if ( !Gia_ObjIsCand(pDiv) )
                        continue;
                    Vec_IntPush( vBases, Abc_Var2Lit(d, 0) );
                    if ( Vec_IntSize(vBases) < nBaseLimit )
                        Vec_IntPush( vBases, Abc_Var2Lit(d, 1) );
                }
                vConstr = Vec_IntAlloc( 3 * nConstrLimit );
                Vec_IntForEachEntry( vBases, iDiv0, d )
                {
                    Vec_IntForEachEntryStart( vBases, iDiv1, e, d + 1 )
                    {
                        for ( fDivCompl = 0; fDivCompl < 2; fDivCompl++ )
                        {
                            nConstructed++;
                            nSigChecks++;
                            if ( !Cec_TranSigMatches(pSim, i, f, iDiv0, iDiv1, fDivCompl) )
                            {
                                nSigRejected++;
                                continue;
                            }
                            nSigMatched++;
                            if ( Vec_IntSize(vConstr) < 3 * nConstrLimit )
                            {
                                Vec_IntPush( vConstr, iDiv0 );
                                Vec_IntPush( vConstr, iDiv1 );
                                Vec_IntPush( vConstr, fDivCompl );
                            }
                        }
                    }
                }
                for ( j = 0; j < Vec_IntSize(vConstr) && !fChanged && nTried < pPars->nCandMax; j += 3 )
                {
                    iDiv0 = Vec_IntEntry( vConstr, j );
                    iDiv1 = Vec_IntEntry( vConstr, j + 1 );
                    iEntry = Vec_IntEntry( vConstr, j + 2 );
                    fChanged = Cec_TranTryCommit( &p, pPars, i, f, iDiv0, iDiv1, iEntry,
                        &nTried, &nPositive, &nAccepted );
                }
                Vec_IntFree( vConstr );
                Vec_IntFree( vBases );
            }
            if ( fChanged || nTried >= pPars->nCandMax || nAccepted >= pPars->nChangesMax )
                break;
        }
        Cec_TranSimStop( pSim );
    }
    while ( fChanged && nTried < pPars->nCandMax && nAccepted < pPars->nChangesMax );
    Abc_Print( 1, "Sequential transduction: proofs=%d existing=%d constructed=%d sig-checks=%d sig-rejected=%d sig-matched=%d gain-filtered=%d accepted=%d, AND=%d -> %d, time=%.2f sec.\n",
        nTried, nExisting, nConstructed, nSigChecks, nSigRejected, nSigMatched, nPositive, nAccepted,
        Gia_ManAndNum(pGia), Gia_ManAndNum(p),
        1.0 * (Abc_Clock() - clk) / CLOCKS_PER_SEC );
    return p;
}

ABC_NAMESPACE_IMPL_END
