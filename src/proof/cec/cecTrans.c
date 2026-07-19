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
#include "aig/gia/giaAig.h"
#include "sat/bmc/bmc.h"

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
    p->nConstrBaseMax = 64;
    p->nVictimsMax = 1;
    p->nProfileTop = 20;
    p->nChangesMax = 100;
    p->nGainMin    = 1;
    p->nSimWords   = 4;
    p->nSimFrames  = 8;
    p->nCexFrames  = 4;
    p->nCexMax     = 64;
    p->nProofWindow = 8;
    p->fUseConstr  = 1;
}

typedef struct Cec_TranTargetProf_t_ Cec_TranTargetProf_t;
struct Cec_TranTargetProf_t_
{
    abctime timeTotal;
    abctime timeCare;
    abctime timeSearch;
    abctime timeGain;
    abctime timeWindow;
    abctime timeCexBmc;
    abctime timeProof;
    int     iRound;
    int     iTarget;
    int     nSuperLeaves;
    int     nCareBits;
    int     nVictimSets;
    int     nExistingChecks;
    int     nExistingMatched;
    int     nExistingRetained;
    int     nConstructChecks;
    int     nConstructMatched;
    int     nConstructRetained;
    int     nDuplicates;
    int     nGainCalls;
    int     nGainPositive;
    int     nGainRejected;
    int     nProofs;
    int     nRetainUnproved;
    int     nFinalUnproved;
    int     nAccepted;
    int     nWindowCalls;
    int     nWindowProved;
    int     nWindowExpanded;
    int     nCexBmcCalls;
    int     nCexBmcSat;
};

typedef struct Cec_TranProf_t_ Cec_TranProf_t;
struct Cec_TranProf_t_
{
    abctime timeTotal;
    abctime timeSim;
    abctime timeCare;
    abctime timeSpec;
    abctime timeExisting;
    abctime timeConstruct;
    abctime timeGain;
    abctime timeWindowMiter;
    abctime timeWindowCorr;
    abctime timeRetainMiter;
    abctime timeRetainCorr;
    abctime timeFinalMiter;
    abctime timeFinalCorr;
    abctime timeShadow;
    abctime timeCexBmc;
    int     nSimCalls;
    int     nCareCalls;
    int     nSpecCalls;
    int     nGainCalls;
    int     nRetainCalls;
    int     nFinalCalls;
    int     nShadowCalls;
    int     nWindowCalls;
    int     nWindowProved;
    int     nWindowExpanded;
    int     nCexBmcCalls;
    int     nCexBmcSat;
    int     nCexBmcUnknown;
    int     nCegisRestarts;
    int     nCexStored;
    int     nTargets;
    int     nTargetVictimSets;
    int     nTargetExistingChecks;
    int     nTargetExistingMatched;
    int     nTargetExistingRetained;
    int     nTargetConstructChecks;
    int     nTargetConstructMatched;
    int     nTargetConstructRetained;
    int     nTargetDuplicates;
    int     nTargetGainCalls;
    int     nTargetGainPositive;
    int     nTargetGainRejected;
    int     nTargetProofs;
    int     nTargetRetainUnproved;
    int     nTargetFinalUnproved;
    int     nTargetAccepted;
    int     nTargetMaxChecks;
};

static double Cec_TranTimeSec( abctime Time )
{
    return 1.0 * Time / CLOCKS_PER_SEC;
}

static void Cec_TranTargetProfAdd( Cec_TranProf_t * p, Cec_TranTargetProf_t * pTop,
    int * pnTop, int nTopMax, Cec_TranTargetProf_t * pTarget )
{
    int i, iMin = 0, nChecks = pTarget->nExistingChecks + pTarget->nConstructChecks;
    p->nTargets++;
    p->nTargetVictimSets       += pTarget->nVictimSets;
    p->nTargetExistingChecks   += pTarget->nExistingChecks;
    p->nTargetExistingMatched  += pTarget->nExistingMatched;
    p->nTargetExistingRetained += pTarget->nExistingRetained;
    p->nTargetConstructChecks  += pTarget->nConstructChecks;
    p->nTargetConstructMatched += pTarget->nConstructMatched;
    p->nTargetConstructRetained += pTarget->nConstructRetained;
    p->nTargetDuplicates       += pTarget->nDuplicates;
    p->nTargetGainCalls        += pTarget->nGainCalls;
    p->nTargetGainPositive     += pTarget->nGainPositive;
    p->nTargetGainRejected     += pTarget->nGainRejected;
    p->nTargetProofs           += pTarget->nProofs;
    p->nTargetRetainUnproved   += pTarget->nRetainUnproved;
    p->nTargetFinalUnproved    += pTarget->nFinalUnproved;
    p->nTargetAccepted         += pTarget->nAccepted;
    if ( p->nTargetMaxChecks < nChecks )
        p->nTargetMaxChecks = nChecks;
    if ( nTopMax == 0 )
        return;
    if ( *pnTop < nTopMax )
    {
        pTop[(*pnTop)++] = *pTarget;
        return;
    }
    for ( i = 1; i < *pnTop; i++ )
        if ( pTop[i].timeTotal < pTop[iMin].timeTotal )
            iMin = i;
    if ( pTop[iMin].timeTotal < pTarget->timeTotal )
        pTop[iMin] = *pTarget;
}

static int Cec_TranTargetProfCompare( const void * p0, const void * p1 )
{
    Cec_TranTargetProf_t const * pT0 = (Cec_TranTargetProf_t const *)p0;
    Cec_TranTargetProf_t const * pT1 = (Cec_TranTargetProf_t const *)p1;
    if ( pT0->timeTotal < pT1->timeTotal )
        return 1;
    if ( pT0->timeTotal > pT1->timeTotal )
        return -1;
    return 0;
}

static void Cec_TranPrintProfile( Cec_TranProf_t * p, Cec_TranTargetProf_t * pTop, int nTop )
{
    Cec_TranTargetProf_t * pT;
    int i;
    abctime Accounted = p->timeSim + p->timeCare + p->timeSpec +
        p->timeExisting + p->timeConstruct + p->timeGain +
        p->timeWindowMiter + p->timeWindowCorr +
        p->timeRetainMiter + p->timeRetainCorr +
        p->timeFinalMiter + p->timeFinalCorr + p->timeShadow + p->timeCexBmc;
    abctime Other = p->timeTotal > Accounted ? p->timeTotal - Accounted : 0;
    Abc_Print( 1, "Sequential transduction profile: total=%.3f sim=%.3f(%d) care=%.3f(%d) spec=%.3f(%d) existing=%.3f construct=%.3f gain=%.3f(%d) other=%.3f sec.\n",
        Cec_TranTimeSec(p->timeTotal), Cec_TranTimeSec(p->timeSim), p->nSimCalls,
        Cec_TranTimeSec(p->timeCare), p->nCareCalls,
        Cec_TranTimeSec(p->timeSpec), p->nSpecCalls,
        Cec_TranTimeSec(p->timeExisting), Cec_TranTimeSec(p->timeConstruct),
        Cec_TranTimeSec(p->timeGain), p->nGainCalls, Cec_TranTimeSec(Other) );
    Abc_Print( 1, "Sequential transduction proof profile: window=%d proved=%d expanded=%d miter=%.3f corr=%.3f retain=%d miter=%.3f corr=%.3f final=%d miter=%.3f corr=%.3f shadow=%d time=%.3f sec.\n",
        p->nWindowCalls, p->nWindowProved, p->nWindowExpanded,
        Cec_TranTimeSec(p->timeWindowMiter), Cec_TranTimeSec(p->timeWindowCorr),
        p->nRetainCalls, Cec_TranTimeSec(p->timeRetainMiter), Cec_TranTimeSec(p->timeRetainCorr),
        p->nFinalCalls, Cec_TranTimeSec(p->timeFinalMiter), Cec_TranTimeSec(p->timeFinalCorr),
        p->nShadowCalls, Cec_TranTimeSec(p->timeShadow) );
    Abc_Print( 1, "Sequential transduction CEGIS profile: stored-cex=%d restarts=%d bmc=%d sat=%d inconclusive=%d time=%.3f sec.\n",
        p->nCexStored, p->nCegisRestarts, p->nCexBmcCalls, p->nCexBmcSat,
        p->nCexBmcUnknown, Cec_TranTimeSec(p->timeCexBmc) );
    Abc_Print( 1, "Sequential transduction target aggregate: targets=%d victim-sets=%d existing=%d/%d/%d constructed=%d/%d/%d duplicates=%d gain=%d/%d/%d proofs=%d retain-unproved=%d final-unproved=%d accepted=%d avg-checks=%.1f max-checks=%d.\n",
        p->nTargets, p->nTargetVictimSets,
        p->nTargetExistingChecks, p->nTargetExistingMatched, p->nTargetExistingRetained,
        p->nTargetConstructChecks, p->nTargetConstructMatched, p->nTargetConstructRetained,
        p->nTargetDuplicates, p->nTargetGainCalls, p->nTargetGainPositive, p->nTargetGainRejected,
        p->nTargetProofs, p->nTargetRetainUnproved, p->nTargetFinalUnproved, p->nTargetAccepted,
        p->nTargets ? 1.0 * (p->nTargetExistingChecks + p->nTargetConstructChecks) / p->nTargets : 0.0,
        p->nTargetMaxChecks );
    if ( nTop > 1 )
        qsort( pTop, nTop, sizeof(Cec_TranTargetProf_t), Cec_TranTargetProfCompare );
    for ( i = 0; i < nTop; i++ )
    {
        abctime AccountedTarget, OtherTarget;
        pT = pTop + i;
        AccountedTarget = pT->timeCare + pT->timeSearch + pT->timeGain +
            pT->timeWindow + pT->timeCexBmc + pT->timeProof;
        OtherTarget = pT->timeTotal > AccountedTarget ? pT->timeTotal - AccountedTarget : 0;
        Abc_Print( 1, "Sequential transduction target profile: rank=%d round=%d obj=%d leaves=%d care-bits=%d victim-sets=%d existing=%d/%d/%d constructed=%d/%d/%d duplicates=%d gain=%d/%d/%d proofs=%d retain-unproved=%d final-unproved=%d accepted=%d window=%d/%d/%d cex-bmc=%d/%d total=%.3f care=%.3f search=%.3f gain-time=%.3f window-time=%.3f cex-time=%.3f proof=%.3f other=%.3f sec.\n",
            i + 1, pT->iRound, pT->iTarget, pT->nSuperLeaves, pT->nCareBits, pT->nVictimSets,
            pT->nExistingChecks, pT->nExistingMatched, pT->nExistingRetained,
            pT->nConstructChecks, pT->nConstructMatched, pT->nConstructRetained,
            pT->nDuplicates, pT->nGainCalls, pT->nGainPositive, pT->nGainRejected,
            pT->nProofs, pT->nRetainUnproved, pT->nFinalUnproved, pT->nAccepted,
            pT->nWindowCalls, pT->nWindowProved, pT->nWindowExpanded,
            pT->nCexBmcCalls, pT->nCexBmcSat,
            Cec_TranTimeSec(pT->timeTotal), Cec_TranTimeSec(pT->timeCare),
            Cec_TranTimeSec(pT->timeSearch), Cec_TranTimeSec(pT->timeGain),
            Cec_TranTimeSec(pT->timeWindow), Cec_TranTimeSec(pT->timeCexBmc),
            Cec_TranTimeSec(pT->timeProof), Cec_TranTimeSec(OtherTarget) );
    }
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

// The pattern database owns concrete bounded counterexamples discovered while
// rejecting transactions.  It deliberately stores only PI/state traces, not
// object values: after a committed structural edit the next simulation batch
// evaluates the same traces on the new snapshot.  This makes the bank valid
// across transactions without retaining stale node IDs.
typedef struct Cec_TranPatDb_t_ Cec_TranPatDb_t;
struct Cec_TranPatDb_t_
{
    Vec_Ptr_t *      vCexes;
    int              nPis;
    int              nRegs;
    int              nMax;
};

static Cec_TranPatDb_t * Cec_TranPatDbStart( Gia_Man_t * p, int nMax )
{
    Cec_TranPatDb_t * pDb = ABC_CALLOC( Cec_TranPatDb_t, 1 );
    pDb->vCexes = Vec_PtrAlloc( nMax );
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
    ABC_FREE( pDb );
}

// Returns 1 only when a new trace was retained.  A CEX with incompatible
// interface dimensions cannot be injected into the original design and is
// ignored; this is a quality loss, never a soundness issue.
static int Cec_TranPatDbAddCex( Cec_TranPatDb_t * pDb, Abc_Cex_t * pCex )
{
    if ( pDb->nMax == 0 || pCex == NULL || pCex->nPis != pDb->nPis ||
         Vec_PtrSize(pDb->vCexes) >= pDb->nMax )
        return 0;
    Vec_PtrPush( pDb->vCexes, Abc_CexDup(pCex, -1) );
    return 1;
}

static inline word Cec_TranSetLane( word Value, int iLane, int fValue )
{
    word Mask = ((word)1) << iLane;
    return fValue ? (Value | Mask) : (Value & ~Mask);
}

static void Cec_TranPatDbInjectInit( Cec_TranPatDb_t * pDb, Cec_TranSim_t * p )
{
    Abc_Cex_t * pCex;
    int c, r, w, iLane, nInject = Abc_MinInt( Vec_PtrSize(pDb->vCexes), p->nWords * 64 );
    for ( c = 0; c < nInject; c++ )
    {
        pCex = (Abc_Cex_t *)Vec_PtrEntry( pDb->vCexes, c );
        if ( pCex->nRegs != Gia_ManRegNum(p->pGia) )
            continue;
        w = c >> 6;
        iLane = c & 63;
        for ( r = 0; r < pCex->nRegs; r++ )
            p->pState[r * p->nWords + w] = Cec_TranSetLane(
                p->pState[r * p->nWords + w], iLane, Abc_InfoHasBit(pCex->pData, r) );
    }
}

static word Cec_TranPatDbInjectPi( Cec_TranPatDb_t * pDb, int f, int iPi, int w, word Value )
{
    Abc_Cex_t * pCex;
    int c, iLane, nInject = Abc_MinInt( Vec_PtrSize(pDb->vCexes), (w + 1) * 64 );
    for ( c = w * 64; c < nInject; c++ )
    {
        pCex = (Abc_Cex_t *)Vec_PtrEntry( pDb->vCexes, c );
        if ( f > pCex->iFrame )
            continue;
        iLane = c & 63;
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

static int Cec_TranCountOnes( word * pData, int nWords )
{
    int i, Count = 0;
    for ( i = 0; i < nWords; i++ )
        Count += (int)__builtin_popcountll( pData[i] );
    return Count;
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
    p->nWords = pPars->nSimWords;
    p->nFrames = pPars->nSimFrames;
    p->nSlots = p->nWords * p->nFrames;
    p->pSims = ABC_CALLOC( word, (size_t)Gia_ManObjNum(pGia) * p->nSlots );
    p->pState = ABC_CALLOC( word, (size_t)Gia_ManRegNum(pGia) * p->nWords );
    Cec_TranPatDbInjectInit( pDb, p );
    Abc_RandomW( 1 );
    for ( f = 0; f < p->nFrames; f++ )
    {
        for ( w = 0; w < p->nWords; w++ )
        {
            iSlot = f * p->nWords + w;
            Gia_ManForEachPi( pGia, pObj, i )
                Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot] =
                    Cec_TranPatDbInjectPi( pDb, f, i, w, Abc_RandomW(0) );
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

// Collect the positive-polarity AND supergate rooted at iTarget.  A
// complemented child is a literal rather than an AND factor because flattening
// through it would apply De Morgan's law.  XOR nodes are never supergate
// members.  The vector contains leaf literals, including their phases.
static void Cec_TranCollectSuper_rec( Gia_Man_t * p, int iLit, Vec_Int_t * vSuper )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, Abc_Lit2Var(iLit) );
    if ( Abc_LitIsCompl(iLit) || !Gia_ObjIsAnd(pObj) || Gia_ObjIsXor(pObj) )
    {
        Vec_IntPush( vSuper, iLit );
        return;
    }
    Cec_TranCollectSuper_rec( p, Gia_ObjFaninLit0p(p, pObj), vSuper );
    Cec_TranCollectSuper_rec( p, Gia_ObjFaninLit1p(p, pObj), vSuper );
}

static Vec_Int_t * Cec_TranCollectSuper( Gia_Man_t * p, int iTarget )
{
    Vec_Int_t * vSuper = Vec_IntAlloc( 8 );
    Cec_TranCollectSuper_rec( p, Abc_Var2Lit(iTarget, 0), vSuper );
    assert( Vec_IntSize(vSuper) >= 2 );
    return vSuper;
}

static inline word Cec_TranTempLit( word * pVals, int nWords, int iLit, int w )
{
    return pVals[(size_t)Abc_Lit2Var(iLit) * nWords + w] ^
        (Abc_LitIsCompl(iLit) ? ~(word)0 : 0);
}

// For each sampled trace/timepoint, flip the target exactly at that frame and
// resimulate the remaining suffix.  A changed PO proves observability.  A
// changed RI is conservatively treated as observable too: its future RO may
// affect a PO beyond the sampled suffix.  The result is a sampled sequential
// care mask C_i^seq, not a formal proof and never a commit criterion.
static word * Cec_TranSimComputeCare( Cec_TranSim_t * p, int iTarget )
{
    Gia_Man_t * pGia = p->pGia;
    Gia_Obj_t * pObj;
    word * pCare, * pVals, * pState, * pNext;
    int fStart, f, w, i, iSlot, iFan0, iFan1, iDriver;
    word v0, v1, v;
    pCare  = ABC_CALLOC( word, p->nSlots );
    pVals  = ABC_CALLOC( word, (size_t)Gia_ManObjNum(pGia) * p->nWords );
    pState = ABC_ALLOC( word, (size_t)Gia_ManRegNum(pGia) * p->nWords );
    pNext  = ABC_ALLOC( word, (size_t)Gia_ManRegNum(pGia) * p->nWords );
    for ( fStart = 0; fStart < p->nFrames; fStart++ )
    {
        Gia_ManForEachRo( pGia, pObj, i )
            for ( w = 0; w < p->nWords; w++ )
                pState[i * p->nWords + w] =
                    Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[fStart * p->nWords + w];
        for ( f = fStart; f < p->nFrames; f++ )
        {
            for ( w = 0; w < p->nWords; w++ )
            {
                iSlot = f * p->nWords + w;
                Gia_ManForEachPi( pGia, pObj, i )
                    pVals[(size_t)Gia_ObjId(pGia, pObj) * p->nWords + w] =
                        Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot];
                Gia_ManForEachRo( pGia, pObj, i )
                    pVals[(size_t)Gia_ObjId(pGia, pObj) * p->nWords + w] =
                        pState[i * p->nWords + w];
                Gia_ManForEachAnd( pGia, pObj, i )
                {
                    iFan0 = Gia_ObjFaninId0p( pGia, pObj );
                    iFan1 = Gia_ObjFaninId1p( pGia, pObj );
                    v0 = pVals[(size_t)iFan0 * p->nWords + w] ^ (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0);
                    v1 = pVals[(size_t)iFan1 * p->nWords + w] ^ (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0);
                    v = Gia_ObjIsXor(pObj) ? (v0 ^ v1) : (v0 & v1);
                    if ( i == iTarget && f == fStart )
                        v = ~Cec_TranSimObj(p, iTarget)[iSlot];
                    pVals[(size_t)i * p->nWords + w] = v;
                }
                Gia_ManForEachPo( pGia, pObj, i )
                {
                    iDriver = Gia_ObjFaninLit0p( pGia, pObj );
                    v = Cec_TranTempLit( pVals, p->nWords, iDriver, w );
                    pCare[fStart * p->nWords + w] |= v ^ Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot];
                }
                Gia_ManForEachRi( pGia, pObj, i )
                {
                    iDriver = Gia_ObjFaninLit0p( pGia, pObj );
                    v = Cec_TranTempLit( pVals, p->nWords, iDriver, w );
                    pVals[(size_t)Gia_ObjId(pGia, pObj) * p->nWords + w] = v;
                    pCare[fStart * p->nWords + w] |= v ^ Cec_TranSimObj(p, Gia_ObjId(pGia, pObj))[iSlot];
                    pNext[i * p->nWords + w] = v;
                }
            }
            for ( i = 0; i < Gia_ManRegNum(pGia) * p->nWords; i++ )
                pState[i] = pNext[i];
        }
    }
    ABC_FREE( pVals );
    ABC_FREE( pState );
    ABC_FREE( pNext );
    return pCare;
}

// This is the conservative first implementation of the specification from
// the design document.  It deliberately takes C_i=1, so it recognizes
// requirements at the target itself and never treats sampled ODC as proof.
// Phase C will replace this with exact sequential-TFO care masks.
typedef struct Cec_TranSpec_t_ Cec_TranSpec_t;
struct Cec_TranSpec_t_
{
    Cec_TranSim_t * pSim;
    word *          pMust1;
    word *          pMust0;
};

static Cec_TranSpec_t * Cec_TranSpecStart( Cec_TranSim_t * p, word * pCare,
    int iTarget, int iFanin0, int iFanin1 )
{
    Cec_TranSpec_t * pSpec = ABC_CALLOC( Cec_TranSpec_t, 1 );
    Vec_Int_t * vSuper = Cec_TranCollectSuper( p->pGia, iTarget );
    int s, i, iLeaf;
    word k, q;
    pSpec->pSim = p;
    pSpec->pMust1 = ABC_ALLOC( word, p->nSlots );
    pSpec->pMust0 = ABC_ALLOC( word, p->nSlots );
    for ( s = 0; s < p->nSlots; s++ )
    {
        k = Cec_TranSimLit( p, Vec_IntEntry(vSuper, iFanin0), s );
        if ( iFanin1 >= 0 )
            k &= Cec_TranSimLit( p, Vec_IntEntry(vSuper, iFanin1), s );
        q = ~(word)0;
        Vec_IntForEachEntry( vSuper, iLeaf, i )
            if ( i != iFanin0 && i != iFanin1 )
                q &= Cec_TranSimLit( p, iLeaf, s );
        pSpec->pMust1[s] = (pCare ? pCare[s] : ~(word)0) & k & q;
        pSpec->pMust0[s] = (pCare ? pCare[s] : ~(word)0) & ~k & q;
    }
    Vec_IntFree( vSuper );
    return pSpec;
}

static void Cec_TranSpecStop( Cec_TranSpec_t * p )
{
    ABC_FREE( p->pMust1 );
    ABC_FREE( p->pMust0 );
    ABC_FREE( p );
}

static int Cec_TranSpecMatches( Cec_TranSpec_t * p, int iDiv0, int iDiv1, int fDivCompl )
{
    int s;
    word h;
    for ( s = 0; s < p->pSim->nSlots; s++ )
    {
        h = Cec_TranSimLit( p->pSim, iDiv0, s );
        if ( iDiv1 != -1 )
            h &= Cec_TranSimLit( p->pSim, iDiv1, s );
        if ( fDivCompl )
            h = ~h;
        if ( (p->pMust1[s] & ~h) || (p->pMust0[s] & h) )
            return 0;
    }
    return 1;
}

static void Cec_TranSpecCompute( Cec_TranSpec_t * p, int iDiv0, int iDiv1,
    int fDivCompl, word * pSig )
{
    int s;
    for ( s = 0; s < p->pSim->nSlots; s++ )
    {
        pSig[s] = Cec_TranSimLit( p->pSim, iDiv0, s );
        if ( iDiv1 != -1 )
            pSig[s] &= Cec_TranSimLit( p->pSim, iDiv1, s );
        if ( fDivCompl )
            pSig[s] = ~pSig[s];
    }
}

// The check is exact over the current signature batch (not hash-based), so a
// duplicate cannot consume one of the expensive formal-proof slots.  Signature
// equality may merge different functions only on unsampled patterns, which
// can lose a search opportunity but can never compromise correctness.
static int Cec_TranSigIsNew( Vec_Wrd_t * vSigs, word * pSig, int nSlots )
{
    int i, k, nSigs = Vec_WrdSize(vSigs) / nSlots;
    for ( i = 0; i < nSigs; i++ )
    {
        for ( k = 0; k < nSlots; k++ )
            if ( Vec_WrdEntry(vSigs, i * nSlots + k) != pSig[k] )
                break;
        if ( k == nSlots )
            return 0;
    }
    for ( k = 0; k < nSlots; k++ )
        Vec_WrdPush( vSigs, pSig[k] );
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
static Gia_Man_t * Cec_TranDupEdit( Gia_Man_t * p, int iTarget, int iFanin0, int iFanin1,
    int iDiv0, int iDiv1, int fDivCompl, int fAdd )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Int_t * vSuper = Cec_TranCollectSuper( p, iTarget );
    int i, k, iLit0, iLit1, iOld, iRep, iLeaf;
    assert( iFanin0 >= 0 && iFanin0 < Vec_IntSize(vSuper) );
    assert( iFanin1 == -1 || (iFanin1 > iFanin0 && iFanin1 < Vec_IntSize(vSuper)) );
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
                Vec_IntForEachEntry( vSuper, iLeaf, k )
                    if ( k != iFanin0 && k != iFanin1 )
                        iRep = Gia_ManHashAnd( pNew, iRep, Cec_TranCopyLit(p, iLeaf) );
                pObj->Value = iRep;
            }
            continue;
        }
        pObj->Value = Gia_ManHashAnd( pNew, iLit0, iLit1 );
    }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Vec_IntFree( vSuper );
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
static char * Cec_TranMarkTfo( Gia_Man_t * p, int iTarget, int nDepth )
{
    Gia_Obj_t * pObj;
    Vec_Int_t * vQueue = Vec_IntAlloc( 100 );
    Vec_Int_t * vDepth = Vec_IntAlloc( 100 );
    char * pMark = ABC_CALLOC( char, Gia_ManObjNum(p) );
    int i, k, iFan;
    Gia_ManStaticFanoutStart( p );
    pMark[iTarget] = 1;
    Vec_IntPush( vQueue, iTarget );
    Vec_IntPush( vDepth, 0 );
    for ( i = 0; i < Vec_IntSize(vQueue); i++ )
    {
        int iObj = Vec_IntEntry( vQueue, i );
        int iDepth = Vec_IntEntry( vDepth, i );
        for ( k = 0; k < Gia_ObjFanoutNumId(p, iObj); k++ )
        {
            iFan = Gia_ObjFanoutId( p, iObj, k );
            if ( pMark[iFan] )
                continue;
            pMark[iFan] = 1;
            pObj = Gia_ManObj( p, iFan );
            if ( !Gia_ObjIsCo(pObj) && (!nDepth || iDepth < nDepth) )
            {
                Vec_IntPush( vQueue, iFan );
                Vec_IntPush( vDepth, iDepth + 1 );
            }
        }
    }
    Gia_ManStaticFanoutStop( p );
    Vec_IntFree( vQueue );
    Vec_IntFree( vDepth );
    return pMark;
}

// Construct a single-state sequential difference machine.  It shares the
// original transition relation, duplicates only the target's combinational
// TFO for the edited variant, and emits differences at all affected PO/RI
// boundaries.  Equality of the affected RIs, together with unchanged
// unmarked RIs, inductively establishes a common state trajectory.  Thus this
// is an exact COI reduction for these pure combinational edits, not a bounded
// window approximation.
static Gia_Man_t * Cec_TranBuildLocalMiter( Gia_Man_t * p, int iTarget, int iFanin0, int iFanin1,
    int iDiv0, int iDiv1, int fDivCompl, int fRemove, int nTfoDepth )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vBase, * vEdit, * vSuper;
    char * pMark;
    int i, k, iLit0, iLit1, iOld, iRep, iEdit, iLeaf, nOuts = 0;
    assert( !Gia_ObjIsXor(Gia_ManObj(p, iTarget)) );
    vSuper = Cec_TranCollectSuper( p, iTarget );
    assert( iFanin0 >= 0 && iFanin0 < Vec_IntSize(vSuper) );
    assert( iFanin1 == -1 || (iFanin1 > iFanin0 && iFanin1 < Vec_IntSize(vSuper)) );
    pMark = Cec_TranMarkTfo( p, iTarget, nTfoDepth );
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
                Vec_IntForEachEntry( vSuper, iLeaf, k )
                    if ( k != iFanin0 && k != iFanin1 )
                        iRep = Gia_ManHashAnd( pNew, iRep, Cec_TranVecLit(vBase, iLeaf) );
                iEdit = iRep;
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
    // For a bounded TFO, every marked AND with an unmarked fanout is a cut
    // boundary.  Proving equality at these boundaries is stronger than the
    // full-TFO query and therefore sound; a failing bounded proof merely
    // triggers expansion and never rejects the transaction.
    if ( nTfoDepth )
    {
        Gia_ManStaticFanoutStart( p );
        Gia_ManForEachAnd( p, pObj, i )
        {
            if ( !pMark[i] )
                continue;
            for ( k = 0; k < Gia_ObjFanoutNumId(p, i); k++ )
                if ( !pMark[Gia_ObjFanoutId(p, i, k)] )
                    break;
            if ( k == Gia_ObjFanoutNumId(p, i) )
                continue;
            Gia_ManAppendCo( pNew, Gia_ManHashXor(pNew,
                Cec_TranVecLit(vBase, Abc_Var2Lit(i, 0)),
                Cec_TranVecLit(vEdit, Abc_Var2Lit(i, 0))) );
            nOuts++;
        }
        Gia_ManStaticFanoutStop( p );
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
    Vec_IntFree( vSuper );
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

// Recover a concrete bounded counterexample only after the complete local
// proof has rejected a transaction.  The main &scorr oracle remains the
// acceptance proof; this BMC is solely a witness extractor for CEGIS.  A
// timeout/UNKNOWN cannot refine the pattern bank and is kept conservative.
static int Cec_TranHarvestCex( Gia_Man_t * pMiter, Cec_ParTran_t * pPars,
    Cec_TranPatDb_t * pDb, Cec_TranProf_t * pProf )
{
    Aig_Man_t * pAig;
    int RetValue, fAdded = 0;
    abctime clk;
    if ( pPars->nCexFrames == 0 || pDb->nMax == 0 ||
         Vec_PtrSize(pDb->vCexes) >= pDb->nMax )
        return 0;
    clk = Abc_Clock();
    pAig = Gia_ManToAigSimple( pMiter );
    RetValue = Saig_ManBmcSimple( pAig, pPars->nCexFrames, 0,
        pPars->nBTLimit, 0, 0, NULL, 0, 0 );
    pProf->timeCexBmc += Abc_Clock() - clk;
    pProf->nCexBmcCalls++;
    if ( RetValue == 0 && pAig->pSeqModel )
    {
        fAdded = Cec_TranPatDbAddCex( pDb, pAig->pSeqModel );
        pProf->nCexBmcSat += fAdded;
    }
    else if ( RetValue == -1 )
        pProf->nCexBmcUnknown++;
    Aig_ManStop( pAig );
    return fAdded;
}

static int Cec_TranProveLocalMiter( Gia_Man_t * pMiter, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, int fRemove, int fWindow )
{
    Cec_ParCor_t Cor;
    Gia_Man_t * pReduced;
    int fProved;
    abctime clk = Abc_Clock();
    Cec_ManCorSetDefaultParams( &Cor );
    Cor.nFrames   = pPars->nFrames;
    Cor.nBTLimit  = pPars->nBTLimit;
    Cor.nStepsMax = pPars->nStepsMax;
    Cor.fVerbose  = 0;
    pReduced = Cec_ManLSCorrespondence( pMiter, &Cor );
    if ( fWindow )
        pProf->timeWindowCorr += Abc_Clock() - clk;
    else if ( fRemove )
        pProf->timeFinalCorr += Abc_Clock() - clk;
    else
        pProf->timeRetainCorr += Abc_Clock() - clk;
    fProved = Cec_TranAllPosAreZero( pReduced );
    Gia_ManStop( pReduced );
    return fProved;
}

static int Cec_TranProveTransaction( Gia_Man_t * p, Gia_Man_t * pWhole0,
    Gia_Man_t * pWhole1, Cec_ParTran_t * pPars, int iTarget, int iFanin0, int iFanin1,
    int iDiv0, int iDiv1, int fDivCompl, int fRemove, Cec_TranPatDb_t * pDb,
    int * pfCexAdded, Cec_TranProf_t * pProf )
{
    Gia_Man_t * pMiter;
    int fProved;
    abctime clk = Abc_Clock();
    if ( pPars->nProofWindow )
    {
        pMiter = Cec_TranBuildLocalMiter( p, iTarget, iFanin0, iFanin1,
            iDiv0, iDiv1, fDivCompl, fRemove, pPars->nProofWindow );
        pProf->timeWindowMiter += Abc_Clock() - clk;
        pProf->nWindowCalls++;
        fProved = Cec_TranProveLocalMiter( pMiter, pPars, pProf, fRemove, 1 );
        Gia_ManStop( pMiter );
        if ( fProved )
        {
            pProf->nWindowProved++;
            goto shadow;
        }
        pProf->nWindowExpanded++;
        clk = Abc_Clock();
    }
    pMiter = Cec_TranBuildLocalMiter( p, iTarget, iFanin0, iFanin1,
        iDiv0, iDiv1, fDivCompl, fRemove, 0 );
    if ( fRemove )
        pProf->timeFinalMiter += Abc_Clock() - clk, pProf->nFinalCalls++;
    else
        pProf->timeRetainMiter += Abc_Clock() - clk, pProf->nRetainCalls++;
    fProved = Cec_TranProveLocalMiter( pMiter, pPars, pProf, fRemove, 0 );
    if ( !fProved )
        *pfCexAdded |= Cec_TranHarvestCex( pMiter, pPars, pDb, pProf );
    Gia_ManStop( pMiter );
shadow:
    if ( fProved && pPars->fShadow )
    {
        clk = Abc_Clock();
        fProved = Cec_TranProveWhole( pWhole0, pWhole1, pPars );
        pProf->timeShadow += Abc_Clock() - clk;
        pProf->nShadowCalls++;
    }
    return fProved;
}

// The candidate has already passed the exact structural-gain test.  This
// routine is the transactional boundary: no speculative wiring reaches p
// unless the sequential miter is discharged by scorr's proof infrastructure.
static int Cec_TranTryCommit( Gia_Man_t ** pp, Cec_ParTran_t * pPars,
    int iTarget, int iFanin0, int iFanin1, int iDiv0, int iDiv1, int fDivCompl, int * pnTried,
    int * pnPositive, int * pnGainRejected, int * pnRetainUnproved,
    int * pnFinalUnproved, int * pnAccepted, Cec_TranPatDb_t * pDb,
    int * pfCegisRestart, Cec_TranProf_t * pProf )
{
    Gia_Man_t * p = *pp, * pAdd, * pFinal, * pCand;
    int Gain, fRetain, fRemove, fCexAdded = 0;
    abctime clk = Abc_Clock();
    pAdd   = Cec_TranDupEdit( p, iTarget, iFanin0, iFanin1, iDiv0, iDiv1, fDivCompl, 1 );
    pFinal = Cec_TranDupEdit( p, iTarget, iFanin0, iFanin1, iDiv0, iDiv1, fDivCompl, 0 );
    pCand  = Cec_TranCleanup( pFinal );
    Gain = Cec_TranGain( p, pCand );
    pProf->timeGain += Abc_Clock() - clk;
    pProf->nGainCalls++;
    if ( Gain < pPars->nGainMin || Gia_ManRegNum(pCand) == 0 )
    {
        (*pnGainRejected)++;
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
        {
            if ( iFanin1 < 0 )
                Abc_Print( 1, "  proof %d: n%d.f%d <- lit%d  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iDiv0, Gain );
            else
                Abc_Print( 1, "  proof %d: n%d.f%d+f%d <- lit%d  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iFanin1, iDiv0, Gain );
        }
        else if ( !fDivCompl )
        {
            if ( iFanin1 < 0 )
                Abc_Print( 1, "  proof %d: n%d.f%d <- (lit%d & lit%d)  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iDiv0, iDiv1, Gain );
            else
                Abc_Print( 1, "  proof %d: n%d.f%d+f%d <- (lit%d & lit%d)  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iFanin1, iDiv0, iDiv1, Gain );
        }
        else
        {
            if ( iFanin1 < 0 )
                Abc_Print( 1, "  proof %d: n%d.f%d <- !(lit%d & lit%d)  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iDiv0, iDiv1, Gain );
            else
                Abc_Print( 1, "  proof %d: n%d.f%d+f%d <- !(lit%d & lit%d)  gain=%d\n",
                    *pnTried, iTarget, iFanin0, iFanin1, iDiv0, iDiv1, Gain );
        }
    }
    // Prove the explicit add stage, then prove the final removal network
    // against the same original source machine.  This second local query is
    // stronger than C_add == C_final; together with retention, transitivity
    // establishes the intended add-then-remove transaction.  When -f is on,
    // Cec_TranProveTransaction additionally shadows the direct whole miter.
    fRetain = Cec_TranProveTransaction(p, p, pAdd, pPars,
        iTarget, iFanin0, iFanin1, iDiv0, iDiv1, fDivCompl, 0, pDb, &fCexAdded, pProf);
    fRemove = fRetain && Cec_TranProveTransaction(p, pAdd, pFinal, pPars,
        iTarget, iFanin0, iFanin1, iDiv0, iDiv1, fDivCompl, 1, pDb, &fCexAdded, pProf);
    if ( !fRemove )
    {
        if ( !fRetain )
            (*pnRetainUnproved)++;
        else
            (*pnFinalUnproved)++;
        Gia_ManStop( pAdd );
        Gia_ManStop( pFinal );
        Gia_ManStop( pCand );
        if ( fCexAdded )
            *pfCegisRestart = 1;
        return 0;
    }
    if ( pPars->fVerbose )
    {
        if ( iFanin1 < 0 )
            Abc_Print( 1, "  accepted transaction: obj %d fanin %d, gain=%d.\n",
                iTarget, iFanin0, Gain );
        else
            Abc_Print( 1, "  accepted transaction: obj %d fanins %d+%d, gain=%d.\n",
                iTarget, iFanin0, iFanin1, Gain );
    }
    Gia_ManStop( p );
    Gia_ManStop( pAdd );
    Gia_ManStop( pFinal );
    *pp = pCand;
    (*pnAccepted)++;
    return 1;
}

Gia_Man_t * Cec_ManSequentialTransduction( Gia_Man_t * pGia, Cec_ParTran_t * pPars )
{
    Cec_TranProf_t Prof = {0};
    Cec_TranTargetProf_t Target, Snap, * pTop;
    Gia_Man_t * p;
    Gia_Obj_t * pObj, * pDiv;
    Cec_TranSim_t * pSim;
    Cec_TranPatDb_t * pDb;
    Cec_TranSpec_t * pSpec;
    word * pCare;
    Vec_Int_t * vMatches, * vBases, * vConstr, * vSuper;
    Vec_Wrd_t * vConstrSigs;
    word * pConstrSig;
    int i, f, f2, d, e, j, iDiv0, iDiv1, fDivCompl, iEntry;
    int nExisting = 0, nExistingMatched = 0, nExistingRetained = 0;
    int nConstructed = 0, nConstructMatched = 0, nConstructRetained = 0;
    int nPositive = 0, nGainRejected = 0;
    int nRetainUnproved = 0, nFinalUnproved = 0, nTried = 0, nAccepted = 0;
    int nSigChecks = 0, nSigRejected = 0, nSigMatched = 0, nSigDuplicate = 0;
    int nCareBits = 0, nThisCareBits, nTop = 0, nRound = 0;
    int nVictim, nVictim2, iFanin1, nBaseLimit, nConstrLimit, nVictimSets = 0;
    int fChanged, fCegisRestart;
    abctime clk = Abc_Clock(), clkPhase, clkTarget;
    assert( Gia_ManRegNum(pGia) > 0 );
    Abc_Print( 1, "Sequential transduction: AND = %d, Reg = %d, frames = %d, conf = %d.\n",
        Gia_ManAndNum(pGia), Gia_ManRegNum(pGia), pPars->nFrames, pPars->nBTLimit );
    p = Gia_ManDup( pGia );
    pDb = Cec_TranPatDbStart( p, pPars->nCexMax );
    pTop = pPars->fProfile && pPars->nProfileTop ?
        ABC_ALLOC( Cec_TranTargetProf_t, pPars->nProfileTop ) : NULL;
    do
    {
        fChanged = 0;
        fCegisRestart = 0;
        // Signatures are rebuilt after every committed transaction.  This is
        // intentionally conservative while structural edit caches do not yet
        // exist; no candidate is ever proved against a stale snapshot.
        clkPhase = Abc_Clock();
        pSim = Cec_TranSimStart( p, pPars, pDb );
        Prof.timeSim += Abc_Clock() - clkPhase;
        Prof.nSimCalls++;
        // Structural filtering is free: a topologically earlier object cannot
        // be in the target's TFO, so it cannot create a combinational cycle.
        Gia_ManForEachAnd( p, pObj, i )
        {
            if ( Gia_ObjIsXor(pObj) )
                continue;
            if ( pPars->fProfile )
            {
                memset( &Target, 0, sizeof(Target) );
                memset( &Snap, 0, sizeof(Snap) );
                clkTarget = Abc_Clock();
                Target.iRound = nRound;
                Target.iTarget = i;
                Snap.nVictimSets = nVictimSets;
                Snap.nExistingChecks = nExisting;
                Snap.nExistingMatched = nExistingMatched;
                Snap.nExistingRetained = nExistingRetained;
                Snap.nConstructChecks = nConstructed;
                Snap.nConstructMatched = nConstructMatched;
                Snap.nConstructRetained = nConstructRetained;
                Snap.nDuplicates = nSigDuplicate;
                Snap.nGainCalls = Prof.nGainCalls;
                Snap.nGainPositive = nPositive;
                Snap.nGainRejected = nGainRejected;
                Snap.nProofs = nTried;
                Snap.nRetainUnproved = nRetainUnproved;
                Snap.nFinalUnproved = nFinalUnproved;
                Snap.nAccepted = nAccepted;
                Snap.timeCare = Prof.timeCare;
                Snap.timeSearch = Prof.timeSpec + Prof.timeExisting + Prof.timeConstruct;
                Snap.timeGain = Prof.timeGain;
                Snap.timeWindow = Prof.timeWindowMiter + Prof.timeWindowCorr;
                Snap.timeCexBmc = Prof.timeCexBmc;
                Snap.timeProof = Prof.timeRetainMiter + Prof.timeRetainCorr +
                    Prof.timeFinalMiter + Prof.timeFinalCorr + Prof.timeShadow;
                Snap.nWindowCalls = Prof.nWindowCalls;
                Snap.nWindowProved = Prof.nWindowProved;
                Snap.nWindowExpanded = Prof.nWindowExpanded;
                Snap.nCexBmcCalls = Prof.nCexBmcCalls;
                Snap.nCexBmcSat = Prof.nCexBmcSat;
            }
            vSuper = Cec_TranCollectSuper( p, i );
            if ( pPars->fProfile )
                Target.nSuperLeaves = Vec_IntSize(vSuper);
            clkPhase = Abc_Clock();
            pCare = Cec_TranSimComputeCare( pSim, i );
            Prof.timeCare += Abc_Clock() - clkPhase;
            Prof.nCareCalls++;
            nThisCareBits = Cec_TranCountOnes( pCare, pSim->nSlots );
            nCareBits += nThisCareBits;
            if ( pPars->fProfile )
                Target.nCareBits = nThisCareBits;
            for ( f = 0; f < Vec_IntSize(vSuper) && !fChanged && !fCegisRestart; f++ )
            {
                // A transaction may replace either one leaf or a pair of
                // leaves in the same positive AND supergate.  The latter is
                // the smallest multi-victim extension: h is required to
                // equal the conjunction of the removed leaves wherever the
                // remaining product is sequentially observable.
                for ( f2 = f; f2 < Vec_IntSize(vSuper) && !fChanged && !fCegisRestart; f2++ )
                {
                if ( pPars->nVictimsMax == 1 && f2 != f )
                    break;
                if ( pPars->nVictimsMax == 2 && f2 == f )
                    continue;
                iFanin1 = f2 == f ? -1 : f2;
                nVictim = Vec_IntEntry( vSuper, f );
                nVictim2 = iFanin1 < 0 ? -1 : Vec_IntEntry( vSuper, iFanin1 );
                nVictimSets++;
                // Compute the specification once.  Every existing divisor
                // and every one-gate construction below shares these masks.
                clkPhase = Abc_Clock();
                pSpec = Cec_TranSpecStart( pSim, pCare, i, f, iFanin1 );
                Prof.timeSpec += Abc_Clock() - clkPhase;
                Prof.nSpecCalls++;
                vMatches = Vec_IntAlloc( pPars->nDivsMax );
                // Test the full topologically-safe pool with bit-parallel
                // Must1/Must0 masks, but retain only the nearest matching
                // literals for expensive formal proof attempts.
                clkPhase = Abc_Clock();
                for ( d = i - 1; d > 0; d-- )
                {
                    pDiv = Gia_ManObj( p, d );
                    if ( !Gia_ObjIsCand(pDiv) )
                        continue;
                    for ( fDivCompl = 0; fDivCompl < 2; fDivCompl++ )
                    {
                        iDiv0 = Abc_Var2Lit( d, fDivCompl );
                        if ( iDiv0 == nVictim || iDiv0 == nVictim2 )
                            continue;
                        nExisting++;
                        nSigChecks++;
                        if ( !Cec_TranSpecMatches(pSpec, iDiv0, -1, 0) )
                        {
                            nSigRejected++;
                            continue;
                        }
                        nSigMatched++;
                        nExistingMatched++;
                        if ( pPars->nDivsMax == 0 || Vec_IntSize(vMatches) < pPars->nDivsMax )
                            Vec_IntPush( vMatches, iDiv0 );
                    }
                }
                Prof.timeExisting += Abc_Clock() - clkPhase;
                nExistingRetained += Vec_IntSize(vMatches);
                Vec_IntForEachEntry( vMatches, iDiv0, j )
                {
                    if ( nTried >= pPars->nCandMax )
                        break;
                    fChanged = Cec_TranTryCommit( &p, pPars, i, f, iFanin1, iDiv0, -1, 0,
                        &nTried, &nPositive, &nGainRejected, &nRetainUnproved,
                        &nFinalUnproved, &nAccepted, pDb, &fCegisRestart, &Prof );
                    if ( fChanged || fCegisRestart )
                        break;
                }
                Vec_IntFree( vMatches );
                if ( !pPars->fUseConstr || fChanged || fCegisRestart || pPars->nConstrMax == 0 )
                {
                    Cec_TranSpecStop( pSpec );
                    continue;
                }

                // A bounded base pool makes the O(D^2 W) construction pass
                // predictable.  Its literals include both phases, so AND and
                // complemented-AND cover AND/OR/AND-NOT forms.
                clkPhase = Abc_Clock();
                nBaseLimit = pPars->nConstrBaseMax;
                nConstrLimit = pPars->nConstrMax;
                vBases = Vec_IntAlloc( nBaseLimit ? nBaseLimit : 100 );
                for ( d = i - 1; d > 0 && (nBaseLimit == 0 || Vec_IntSize(vBases) < nBaseLimit); d-- )
                {
                    pDiv = Gia_ManObj( p, d );
                    if ( !Gia_ObjIsCand(pDiv) )
                        continue;
                    Vec_IntPush( vBases, Abc_Var2Lit(d, 0) );
                    if ( nBaseLimit == 0 || Vec_IntSize(vBases) < nBaseLimit )
                        Vec_IntPush( vBases, Abc_Var2Lit(d, 1) );
                }
                vConstr = Vec_IntAlloc( 3 * nConstrLimit );
                vConstrSigs = Vec_WrdAlloc( nConstrLimit * pSim->nSlots );
                pConstrSig = ABC_ALLOC( word, pSim->nSlots );
                Vec_IntForEachEntry( vBases, iDiv0, d )
                {
                    Vec_IntForEachEntryStart( vBases, iDiv1, e, d + 1 )
                    {
                        for ( fDivCompl = 0; fDivCompl < 2; fDivCompl++ )
                        {
                            nConstructed++;
                            nSigChecks++;
                            if ( !Cec_TranSpecMatches(pSpec, iDiv0, iDiv1, fDivCompl) )
                            {
                                nSigRejected++;
                                continue;
                            }
                            nSigMatched++;
                            nConstructMatched++;
                            if ( Vec_IntSize(vConstr) < 3 * nConstrLimit )
                            {
                                Cec_TranSpecCompute( pSpec, iDiv0, iDiv1, fDivCompl, pConstrSig );
                                if ( !Cec_TranSigIsNew(vConstrSigs, pConstrSig, pSim->nSlots) )
                                {
                                    nSigDuplicate++;
                                    continue;
                                }
                                Vec_IntPush( vConstr, iDiv0 );
                                Vec_IntPush( vConstr, iDiv1 );
                                Vec_IntPush( vConstr, fDivCompl );
                            }
                        }
                    }
                }
                Prof.timeConstruct += Abc_Clock() - clkPhase;
                nConstructRetained += Vec_IntSize(vConstr) / 3;
                for ( j = 0; j < Vec_IntSize(vConstr) && !fChanged && !fCegisRestart && nTried < pPars->nCandMax; j += 3 )
                {
                    iDiv0 = Vec_IntEntry( vConstr, j );
                    iDiv1 = Vec_IntEntry( vConstr, j + 1 );
                    iEntry = Vec_IntEntry( vConstr, j + 2 );
                    fChanged = Cec_TranTryCommit( &p, pPars, i, f, iFanin1, iDiv0, iDiv1, iEntry,
                        &nTried, &nPositive, &nGainRejected, &nRetainUnproved,
                        &nFinalUnproved, &nAccepted, pDb, &fCegisRestart, &Prof );
                }
                Vec_IntFree( vConstr );
                Vec_WrdFree( vConstrSigs );
                ABC_FREE( pConstrSig );
                Vec_IntFree( vBases );
                Cec_TranSpecStop( pSpec );
                }
            }
            ABC_FREE( pCare );
            Vec_IntFree( vSuper );
            if ( pPars->fProfile )
            {
                Target.timeTotal = Abc_Clock() - clkTarget;
                Target.timeCare = Prof.timeCare - Snap.timeCare;
                Target.timeSearch = Prof.timeSpec + Prof.timeExisting + Prof.timeConstruct - Snap.timeSearch;
                Target.timeGain = Prof.timeGain - Snap.timeGain;
                Target.timeWindow = Prof.timeWindowMiter + Prof.timeWindowCorr - Snap.timeWindow;
                Target.timeCexBmc = Prof.timeCexBmc - Snap.timeCexBmc;
                Target.timeProof = Prof.timeRetainMiter + Prof.timeRetainCorr +
                    Prof.timeFinalMiter + Prof.timeFinalCorr + Prof.timeShadow - Snap.timeProof;
                Target.nVictimSets = nVictimSets - Snap.nVictimSets;
                Target.nExistingChecks = nExisting - Snap.nExistingChecks;
                Target.nExistingMatched = nExistingMatched - Snap.nExistingMatched;
                Target.nExistingRetained = nExistingRetained - Snap.nExistingRetained;
                Target.nConstructChecks = nConstructed - Snap.nConstructChecks;
                Target.nConstructMatched = nConstructMatched - Snap.nConstructMatched;
                Target.nConstructRetained = nConstructRetained - Snap.nConstructRetained;
                Target.nDuplicates = nSigDuplicate - Snap.nDuplicates;
                Target.nGainCalls = Prof.nGainCalls - Snap.nGainCalls;
                Target.nGainPositive = nPositive - Snap.nGainPositive;
                Target.nGainRejected = nGainRejected - Snap.nGainRejected;
                Target.nProofs = nTried - Snap.nProofs;
                Target.nRetainUnproved = nRetainUnproved - Snap.nRetainUnproved;
                Target.nFinalUnproved = nFinalUnproved - Snap.nFinalUnproved;
                Target.nAccepted = nAccepted - Snap.nAccepted;
                Target.nWindowCalls = Prof.nWindowCalls - Snap.nWindowCalls;
                Target.nWindowProved = Prof.nWindowProved - Snap.nWindowProved;
                Target.nWindowExpanded = Prof.nWindowExpanded - Snap.nWindowExpanded;
                Target.nCexBmcCalls = Prof.nCexBmcCalls - Snap.nCexBmcCalls;
                Target.nCexBmcSat = Prof.nCexBmcSat - Snap.nCexBmcSat;
                Cec_TranTargetProfAdd( &Prof, pTop, &nTop, pPars->nProfileTop, &Target );
            }
            if ( fChanged || fCegisRestart || nTried >= pPars->nCandMax || nAccepted >= pPars->nChangesMax )
                break;
        }
        Cec_TranSimStop( pSim );
        if ( fCegisRestart )
            Prof.nCegisRestarts++;
        nRound++;
    }
    while ( (fChanged || fCegisRestart) && nTried < pPars->nCandMax && nAccepted < pPars->nChangesMax );
    Prof.timeTotal = Abc_Clock() - clk;
    Abc_Print( 1, "Sequential transduction: victim-sets=%d proofs=%d existing=%d constructed=%d care-bits=%d sig-checks=%d sig-rejected=%d sig-matched=%d sig-duplicates=%d gain-positive=%d gain-rejected=%d retain-unproved=%d final-unproved=%d accepted=%d, AND=%d -> %d, time=%.2f sec.\n",
        nVictimSets, nTried, nExisting, nConstructed, nCareBits, nSigChecks, nSigRejected, nSigMatched, nSigDuplicate,
        nPositive, nGainRejected, nRetainUnproved, nFinalUnproved, nAccepted,
        Gia_ManAndNum(pGia), Gia_ManAndNum(p),
        Cec_TranTimeSec(Prof.timeTotal) );
    Prof.nCexStored = Vec_PtrSize(pDb->vCexes);
    if ( pPars->fProfile )
        Cec_TranPrintProfile( &Prof, pTop, nTop );
    ABC_FREE( pTop );
    Cec_TranPatDbStop( pDb );
    return p;
}

ABC_NAMESPACE_IMPL_END
