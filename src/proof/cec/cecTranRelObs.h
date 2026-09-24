// Experimental temporal observability: construction evidence is deliberately
// separate from the unbounded, permanent-product acceptance proposition.
// No state correspondence, old helper or old reachable-state assumption is
// imported into a product proof.  Every accepted edit ends its snapshot.
#include <sys/stat.h>
#include <unistd.h>

static int s_RelProofId = 0;

// Path observability through a finite unrolling.  PO care is one, and RI care
// comes from the corresponding RO in the next frame.  Terminal RI care is
// zero: this is an incomplete *proposal* mask, never an invariant.  Path
// sensitization also approximates reconvergence.  Both limits
// affect search only; the permanent product below is the sole acceptance test.
static word * Cec_TranRelCare( Cec_TranSim_t * pSim )
{
    Gia_Man_t * p = pSim->pGia;
    Gia_Obj_t * pObj;
    word * pCare = ABC_CALLOC( word, (size_t)Gia_ManObjNum(p) * pSim->nSlots );
    int f, w, i, s, a, b;
    for ( f = pSim->nFrames - 1; f >= 0; --f )
        for ( w = 0; w < pSim->nWords; ++w )
        {
            s = f * pSim->nWords + w;
            Gia_ManForEachPo( p, pObj, i )
                pCare[(size_t)Gia_ObjFaninId0p(p, pObj)*pSim->nSlots+s] = ~(word)0;
            if ( f + 1 < pSim->nFrames )
                Gia_ManForEachRi( p, pObj, i )
                    pCare[(size_t)Gia_ObjFaninId0p(p, pObj)*pSim->nSlots+s] |=
                        pCare[(size_t)Gia_ObjId(p, Gia_ManRo(p, i))*pSim->nSlots+s+pSim->nWords];
            Gia_ManForEachAndReverse( p, pObj, i )
            {
                word c = pCare[(size_t)i*pSim->nSlots+s];
                a = Gia_ObjFaninLit0p(p, pObj);
                b = Gia_ObjFaninLit1p(p, pObj);
                pCare[(size_t)Abc_Lit2Var(a)*pSim->nSlots+s] |= c &
                    (Gia_ObjIsXor(pObj) ? ~(word)0 : Cec_TranSimLit(pSim, b, s));
                pCare[(size_t)Abc_Lit2Var(b)*pSim->nSlots+s] |= c &
                    (Gia_ObjIsXor(pObj) ? ~(word)0 : Cec_TranSimLit(pSim, a, s));
            }
        }
    return pCare;
}

static void Cec_TranRelDumpGia( Gia_Man_t * p, int Id, char const * pTag )
{
    char const * pDir = getenv("ABC_RELOBS_DUMP");
    char File[4096];
    if ( !pDir ) return;
    snprintf(File, sizeof(File), "%s/%ld-%06d-%s.aig", pDir, (long)getpid(), Id, pTag);
    Gia_AigerWriteS(p, File, 0, 0, 1, 1);
}

// 1 = inductively proved safe, 0 = verified reset-reachable CEX, -1 = unknown.
// Only an actual PDR fixed point may return 1.  No finite bound is success.
static int Cec_TranRelPdr( Gia_Man_t * pMiter, char const * pTag, int * pId, Vec_Ptr_t * vBank )
{
    Pdr_Par_t Pars;
    Aig_Man_t * pAig = Gia_ManToAig(pMiter, 0);
    char const * pDir = getenv("ABC_RELOBS_DUMP");
    char File[4096];
    abctime clk = Abc_Clock();
    int Status, Id = ++s_RelProofId;
    if ( pId ) *pId = Id;
    Pdr_ManSetDefaultParams(&Pars);
    Pars.fSilent = 1;
    Pars.nFrameMax = 0;
    Pars.nConfLimit = 0;
    if ( pDir )
    {
        // PDR's PLA dumper obtains names from the global legacy NTK, which is
        // unrelated to this temporary GIA product (and may be NULL).  Save
        // the exact query here; standalone replay can dump its invariant with
        // the matching product installed as the current legacy network.
        Cec_TranRelDumpGia(pMiter, Id, pTag);
    }
    Status = Pdr_ManSolve(pAig, &Pars);
    assert(Status >= -1 && Status <= 1);
    if ( Status == 0 )
    {
        Abc_Cex_t * pCex = pAig->pSeqModel;
        assert(pCex && Saig_ManVerifyCex(pAig, pCex));
        // Preserve only the real external input sequence.  Product RO samples
        // never become root labels or state assumptions on a later snapshot.
        if ( vBank ) Vec_PtrPush(vBank, Abc_CexDup(pCex, 0));
        if ( pDir )
        {
            FILE * f;
            int i, t;
            snprintf(File, sizeof(File), "%s/%ld-%06d-%s.cex", pDir, (long)getpid(), Id, pTag);
            f = fopen(File, "w"); assert(f);
            fprintf(f, "zero-init regs=%d pis=%d po=%d frame=%d\n", pCex->nRegs, pCex->nPis, pCex->iPo, pCex->iFrame);
            for ( i = 0; i < pCex->nRegs; ++i ) assert(!Abc_InfoHasBit(pCex->pData, i));
            for ( t = 0; t <= pCex->iFrame; ++t )
            {
                for ( i = 0; i < pCex->nPis; ++i )
                    fputc('0' + Abc_InfoHasBit(pCex->pData, pCex->nRegs+t*pCex->nPis+i), f);
                fputc('\n', f);
            }
            fclose(f);
        }
    }
    Abc_Print(1, "relobs-proof id=%d tag=%s status=%d frame=%d cex-frame=%d regs=%d pos=%d seconds=%.6f\n",
        Id, pTag, Status, Pars.iFrame, pAig->pSeqModel ? pAig->pSeqModel->iFrame : -1,
        Gia_ManRegNum(pMiter), Gia_ManPoNum(pMiter), Cec_TranTimeSec(Abc_Clock()-clk));
    Aig_ManStop(pAig);
    return Status;
}

// Original machine with root/window XOR query POs.  This tests the *old*
// proposition for attribution, not permanent replacement correctness.
static int Cec_TranRelOldProof( Gia_Man_t * p, Cec_TranCand_t const * pCand,
    Cec_ParTran_t * pPars, int fWindow )
{
    Cec_TranCandVec_t Obs = {0};
    Vec_Int_t * vPairs, * vComb, * vQueries;
    Gia_Man_t * pQuery;
    int Status;
    if ( fWindow ) Cec_TranWindowObligations(p, pCand, pPars, &Obs);
    else Cec_TranCandVecPush(&Obs, *pCand);
    pQuery = Cec_TranBuildRootBatch(p, NULL, 0, Obs.pArray, Obs.nSize, 1,
        &vPairs, &vComb, &vQueries, NULL, NULL);
    Status = Cec_TranRelPdr(pQuery, fWindow ? "window" : "root", NULL, NULL);
    Gia_ManStop(pQuery);
    Vec_IntFree(vPairs); Vec_IntFree(vComb); Vec_IntFree(vQueries);
    Cec_TranCandVecStop(&Obs);
    return Status;
}

// Observe state divergence in an independent product.  The appended state
// outputs are diagnostic properties, never assumptions of the PO proof.
static Gia_Man_t * Cec_TranRelExposeState( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, nRegs = Gia_ManRegNum(p);
    Gia_ManFillValue(p);
    pNew = Gia_ManStart(Gia_ManObjNum(p)+nRegs);
    pNew->pName = Abc_UtilStrsav("relobs_state");
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi(p, pObj, i) pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManHashAlloc(pNew);
    Gia_ManForEachAnd(p, pObj, i)
        pObj->Value = Cec_TranHashGate(pNew, pObj, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
    Gia_ManForEachRo(p, pObj, i) Gia_ManAppendCo(pNew, pObj->Value);
    Gia_ManForEachRi(p, pObj, i) Gia_ManAppendCo(pNew, Gia_ObjFanin0Copy(pObj));
    Gia_ManHashStop(pNew); Gia_ManSetRegNum(pNew, nRegs);
    return pNew;
}

static int Cec_TranRelStateProof( Gia_Man_t * p, Gia_Man_t * pNew )
{
    Gia_Man_t * a = Cec_TranRelExposeState(p), * b = Cec_TranRelExposeState(pNew);
    Gia_Man_t * m = Gia_ManMiter(a, b, 0, 0, 1, 0, 0);
    int Status = Cec_TranRelPdr(m, "state", NULL, NULL);
    Gia_ManStop(a); Gia_ManStop(b); Gia_ManStop(m);
    return Status;
}

// Permanent two-machine replay of a real PO counterexample.  A new candidate
// is rejected only if this exact input sequence also distinguishes its POs.
// Passing replay has no proof status and imposes no equality on internal nodes.
static int Cec_TranRelReplay( Gia_Man_t * p, Gia_Man_t * q, Abc_Cex_t * cex )
{
    Gia_Man_t * gs[2] = {p, q};
    unsigned char * vals[2] = {ABC_CALLOC(unsigned char, Gia_ManObjNum(p)), ABC_CALLOC(unsigned char, Gia_ManObjNum(q))};
    unsigned char * states[2] = {ABC_CALLOC(unsigned char, Gia_ManRegNum(p)), ABC_CALLOC(unsigned char, Gia_ManRegNum(q))};
    int f, side, i, bad = 0;
    Gia_Obj_t * o;
    assert(cex->nPis == Gia_ManPiNum(p) && Gia_ManPiNum(p) == Gia_ManPiNum(q));
    for ( f = 0; f <= cex->iFrame && !bad; ++f )
    {
        for ( side = 0; side < 2; ++side )
        {
            Gia_Man_t * g = gs[side];
            unsigned char * v = vals[side];
            Gia_ManForEachPi(g, o, i) v[Gia_ObjId(g, o)] = Abc_InfoHasBit(cex->pData, cex->nRegs+f*cex->nPis+i);
            Gia_ManForEachRo(g, o, i) v[Gia_ObjId(g, o)] = states[side][i];
            Gia_ManForEachAnd(g, o, i)
            {
                int a = v[Gia_ObjFaninId0p(g, o)] ^ Gia_ObjFaninC0(o);
                int b = v[Gia_ObjFaninId1p(g, o)] ^ Gia_ObjFaninC1(o);
                v[i] = Gia_ObjIsXor(o) ? a ^ b : a & b;
            }
            Gia_ManForEachCo(g, o, i) v[Gia_ObjId(g, o)] = v[Gia_ObjFaninId0p(g, o)] ^ Gia_ObjFaninC0(o);
            Gia_ManForEachRi(g, o, i) states[side][i] = v[Gia_ObjId(g, o)];
        }
        Gia_ManForEachPo(p, o, i)
            bad |= vals[0][Gia_ObjId(p, o)] != vals[1][Gia_ObjId(q, Gia_ManPo(q, i))];
    }
    ABC_FREE(vals[0]); ABC_FREE(vals[1]); ABC_FREE(states[0]); ABC_FREE(states[1]);
    return bad;
}

static void Cec_TranRelCommitProfile( int Before, int After, int Regs,
    int * Counts, int * Gains, double Total, double Proof )
{
    int k, Selected = Counts[0]+Counts[1]+Counts[2], Gain = Before-After;
    assert(Gain == Gains[0]+Gains[1]+Gains[2]);
    Abc_Print(1, "stran-root experiment-time profile: schema=8 phase=seq scope=relobs total-sec=%.6f sim-sec=0 root-refresh-sec=0 direct-discovery-sec=0 divisor-discovery-sec=0 resub-init-sec=0 resub-enum-sec=0 cbs-graph-sec=0 cbs-screen-sec=0 cbs-solve-sec=0 scorr-graph-sec=0 scorr-bmc-sec=0 scorr-induction-sec=0 scorr-resim-sec=0 scorr-other-sec=0 selection-repair-sec=0 bundle-sec=0 cleanup-sec=0 exact-audit-sec=%.6f shadow-sec=0 unprofiled-sec=%.6f\n", Total, Proof, Total > Proof ? Total-Proof : 0.0);
    Abc_Print(1, "stran-root experiment-summary profile: schema=8 phase=seq scope=relobs selected-roots=%d marginal-and=%d final-and-gain=%d final-reg-gain=0 and-before=%d and-after=%d reg-before=%d reg-after=%d\n", Selected, Gain, Gain, Before, After, Regs, Regs);
    for ( k = 0; k < 3; ++k )
        Abc_Print(1, "stran-root experiment-commit profile: schema=8 phase=seq kind=%s selected=%d marginal-and=%d marginal-reg=0\n", k == 0 ? "constant" : k == 1 ? "existing" : "build", Counts[k], Gains[k]);
}

static Gia_Man_t * Cec_TranRunRelObs( Gia_Man_t * p, Cec_ParTran_t * pPars )
{
    Cec_ParTran_t BuildPars = *pPars;
    Vec_Ptr_t * vBank = Vec_PtrAlloc(16);
    Abc_Cex_t * pCex;
    int k;
    int Round = 0, TotalGain = 0, TotalCommits = 0;
    assert(pPars->nRelObs == 6 && pPars->fOutputProof);
    // Same material/recipe envelope as the frozen ODC preset.  No H2 free-RO
    // full-care samples: these are not reachable traces of a product machine.
    if ( pPars->nExplore & 524288 ) BuildPars.nRootConstrTop = 320;
    if ( pPars->nExplore & 8388608 ) BuildPars.nConstrBaseMax = 128;
    BuildPars.nRootProofBatch = 0;
    for ( ; !pPars->nOutputRounds || Round < pPars->nOutputRounds; )
    {
        Cec_TranProf_t Prof = {0};
        Cec_TranDiscStat_t Disc = {0};
        Cec_TranCandVec_t Cands = {0}, Known = {0};
        Cec_TranPatDb_t * pDb = Cec_TranPatDbStart(p, 0);
        Cec_TranSim_t * pSim = Cec_TranSimStart(p, &BuildPars, pDb);
        Cec_TranRoot_t * pRoots = ABC_ALLOC(Cec_TranRoot_t, Gia_ManAndNum(p));
        Vec_Int_t * vMffc = Vec_IntAlloc(128), * vTfo = Vec_IntAlloc(128), * vOne = Vec_IntAlloc(1);
        char * pMffc = ABC_CALLOC(char, Gia_ManObjNum(p));
        word * pCare = Cec_TranRelCare(pSim);
        Gia_Obj_t * pObj;
        Gia_Man_t * pNext = NULL;
        int i, r, nRoots = 0, Tried = 0, Sat = 0, Unknown = 0, Replay = 0;
        int Generated[3] = {0};
        int Counts[3] = {0}, Gains[3] = {0}, Before = Gia_ManAndNum(p);
        abctime clk = Abc_Clock(), TimeProof = 0;
        Prof.DiagPhase = 1;
        Gia_ManCreateRefs(p); Gia_ManStaticFanoutStart(p);
        Gia_ManForEachAnd(p, pObj, i)
        {
            pRoots[nRoots].iObj = i;
            pRoots[nRoots++].nMffc = Gia_NodeMffcSize(p, pObj);
        }
        qsort(pRoots, nRoots, sizeof(Cec_TranRoot_t), Cec_TranRootCompare);
        for ( r = 0; r < nRoots; ++r )
        {
            Cec_TranRoot_t * pRoot = pRoots+r;
            Cec_TranCandVec_t Direct = {0};
            Cec_TranDivRank_t * pRanks;
            Vec_Int_t * vPool = Cec_TranCollectDivPool(p, pRoot->iObj,
                BuildPars.nConstrMax, BuildPars.nConstrBaseMax ? Abc_MaxInt(4*BuildPars.nConstrBaseMax, BuildPars.nConstrBaseMax+32) : 0,
                BuildPars.fUseMffcDivs, NULL, NULL, pMffc, vMffc,
                BuildPars.fUseTfoDivs, BuildPars.nConstrBaseMax, vTfo, NULL);
            word * pRootCare = pCare+(size_t)pRoot->iObj*pSim->nSlots;
            pRanks = Cec_TranRankDivReservoir(pSim, pRoot->iObj, vPool, &BuildPars, &Prof, pRootCare);
            Cec_TranSelectRankedDivPool(vPool, pRanks, BuildPars.nConstrBaseMax, NULL);
            Prof.nRootDivPoolNodes += Vec_IntSize(vPool);
            Cec_TranCollectRootDirectTfi(p, pSim, &BuildPars, pRoot, vPool,
                pRootCare, 0, &Known, &Direct, &Disc, &Prof);
            for ( i = 0; i < Direct.nSize; ++i ) Cec_TranCandVecPush(&Cands, Direct.pArray[i]);
            Cec_TranCandVecStop(&Direct);
            ABC_FREE(pRanks); Vec_IntFree(vPool);
        }
        Cec_TranCandVecEvalSortTail(p, &Cands, 0, &Prof);
        for ( i = 0; i < Cands.nSize; ++i ) ++Generated[Cands.pArray[i].nKind];
        Abc_Print(1, "relobs-discovery round=%d roots=%d candidates=%d words=%d frames=%d B=%d q=%d N=%d constant=%d existing=%d build=%d material=%d\n",
            Round, nRoots, Cands.nSize, pSim->nWords, pSim->nFrames,
            BuildPars.nConstrBaseMax, BuildPars.nRootConstrTop, BuildPars.nDepNodesMax,
            Generated[0], Generated[1], Generated[2], Prof.nRootDivPoolNodes);
        Vec_IntPush(vOne, 0);
        for ( i = 0; i < Cands.nSize; ++i )
        {
            Cec_TranCand_t * c = Cands.pArray+i;
            Gia_Man_t * pDup, * pClean, * pMiter;
            int Status, Id, Gain, RootStatus = -2, WindowStatus = -2, StateStatus;
            abctime cp;
            if ( c->Gain <= 0 ) continue;
            assert(Cec_TranProofHistoryTopoValid(p, c));
            pDup = Cec_TranDupRootBundle(p, c, vOne);
            pClean = Cec_TranCleanupKeepRegs(pDup, NULL); Gia_ManStop(pDup);
            Gain = Cec_TranGain(p, pClean);
            if ( Gain <= 0 ) { Gia_ManStop(pClean); continue; }
            Vec_PtrForEachEntry(Abc_Cex_t *, vBank, pCex, k)
                if ( Cec_TranRelReplay(p, pClean, pCex) ) break;
            if ( k < Vec_PtrSize(vBank) ) { ++Replay; Gia_ManStop(pClean); continue; }
            ++Tried;
            cp = Abc_Clock();
            pMiter = Gia_ManMiter(p, pClean, 0, 0, 1, 0, 0);
            assert(pMiter && Gia_ManRegNum(pMiter) == 2*Gia_ManRegNum(p));
            Status = Cec_TranRelPdr(pMiter, "product", &Id, vBank);
            Gia_ManStop(pMiter);
            if ( Status != 1 )
            { Sat += Status == 0; Unknown += Status < 0; Gia_ManStop(pClean); TimeProof += Abc_Clock()-cp; continue; }
            RootStatus = Cec_TranRelOldProof(p, c, pPars, 0);
            if ( WindowStatus == -2 ) WindowStatus = Cec_TranRelOldProof(p, c, pPars, 1);
            StateStatus = Cec_TranRelStateProof(p, pClean);
            TimeProof += Abc_Clock()-cp;
            Cec_TranRelDumpGia(p, Id, "before"); Cec_TranRelDumpGia(pClean, Id, "after");
            Abc_Print(1, "relobs-commit round=%d proof=%d root=%d kind=%d gates=%d out=%d gain=%d root-status=%d window-status=%d state-status=%d recipe=",
                Round, Id, c->iTarget, c->nKind, c->nGates, c->iOut, Gain, RootStatus, WindowStatus, StateStatus);
            for ( r = 0; r < 2*c->nGates; ++r ) Abc_Print(1, "%s%d", r ? "," : "", c->Recipe[r]);
            Abc_Print(1, "\n");
            Counts[c->nKind] = 1; Gains[c->nKind] = Gain;
            pNext = pClean; TotalGain += Gain; ++TotalCommits;
            break;
        }
        Abc_Print(1, "relobs-round round=%d tried=%d sat=%d unknown=%d committed=%d gain=%d replay=%d bank=%d\n",
            Round, Tried, Sat, Unknown, pNext != NULL, Before-(pNext ? Gia_ManAndNum(pNext) : Before), Replay, Vec_PtrSize(vBank));
        // Preserve existing conservation schema, with a distinct scope tag.
        Cec_TranRelCommitProfile(Before, pNext ? Gia_ManAndNum(pNext) : Before,
            Gia_ManRegNum(p), Counts, Gains, Cec_TranTimeSec(Abc_Clock()-clk), Cec_TranTimeSec(TimeProof));
        Cec_TranCandVecStop(&Cands); Cec_TranCandVecStop(&Known);
        Cec_TranSimStop(pSim); Cec_TranPatDbStop(pDb);
        Vec_IntFree(vMffc); Vec_IntFree(vTfo); Vec_IntFree(vOne);
        ABC_FREE(pCare); ABC_FREE(pMffc); ABC_FREE(pRoots);
        Gia_ManStaticFanoutStop(p); ABC_FREE(p->pRefs);
        if ( !pNext ) break;
        Gia_ManStop(p); p = pNext; ++Round;
    }
    Abc_Print(1, "relobs-summary mode=%d commits=%d gain=%d\n", pPars->nRelObs, TotalCommits, TotalGain);
    Vec_PtrForEachEntry(Abc_Cex_t *, vBank, pCex, k) Abc_CexFree(pCex);
    Vec_PtrFree(vBank);
    return p;
}

static Gia_Man_t * Cec_TranRelWitness( int fBuild, int nDelay, int * pRoot )
{
    Gia_Man_t * p = Gia_ManStart(64);
    int en = Gia_ManAppendCi(p), d = Gia_ManAppendCi(p);
    int e = fBuild ? Gia_ManAppendCi(p) : 1;
    int valid = Gia_ManAppendCi(p), data = Gia_ManAppendCi(p);
    int delay[16] = {0}, i, root;
    assert(nDelay <= 16);
    p->pName = Abc_UtilStrsav("relobs_witness");
    for ( i = 0; i < nDelay; ++i ) delay[i] = Gia_ManAppendCi(p);
    Gia_ManHashAlloc(p);
    root = Gia_ManHashAnd(p, en, d);
    if ( fBuild ) root = Gia_ManHashAnd(p, root, e);
    Gia_ManAppendCo(p, nDelay ? delay[nDelay-1] : Gia_ManHashAnd(p, valid, data));
    Gia_ManAppendCo(p, en); Gia_ManAppendCo(p, root);
    for ( i = 0; i < nDelay; ++i ) Gia_ManAppendCo(p, i ? delay[i-1] : data);
    Gia_ManHashStop(p); Gia_ManSetRegNum(p, 2+nDelay);
    *pRoot = Abc_Lit2Var(root);
    return p;
}

static int Cec_TranRelObsSelfTest()
{
    Cec_ParTran_t Pars;
    Cec_TranProf_t Prof = {0};
    int fBuild, root;
    Cec_ManTranSetDefaultParams(&Pars);
    Pars.nFrames = 2; Pars.nBTLimit = 1000;
    for ( fBuild = 0; fBuild <= 1; ++fBuild )
    {
        Gia_Man_t * p = Cec_TranRelWitness(fBuild, 0, &root), * q, * m;
        Cec_TranPatDb_t * db = Cec_TranPatDbStart(p, 0);
        Cec_TranSim_t * sim = Cec_TranSimStart(p, &Pars, db);
        Cec_TranCand_t c = Cec_TranCandCreateLiteral(root, 4, 1+fBuild, CEC_TRAN_CAND_EXIST, 0);
        word * care = Cec_TranRelCare(sim);
        Vec_Int_t * one = Vec_IntAlloc(1);
        if ( fBuild )
        {
            c.nGates = 1; c.nKind = CEC_TRAN_CAND_CONSTR;
            c.Recipe = Cec_TranRecipeAlloc(2); c.Recipe[0] = 4; c.Recipe[1] = 6;
            c.iOut = Cec_TranRecipeGateCode(0, 0);
        }
        assert(!Cec_TranRecipeMatchesRoot(sim, &c, NULL));
        assert(Cec_TranRecipeMatchesRoot(sim, &c, care+(size_t)root*sim->nSlots));
        // Ask the native AND/inverter iterator to construct the 1-AND witness.
        if ( fBuild )
        {
            Cec_TranDepScratch_t dep;
            Cec_TranRoot_t Root = {root, 2};
            Vec_Int_t * pool = Vec_IntAlloc(3);
            void * cache = NULL, * it;
            int cursor[6] = {0}, attempt, exhausted = 0, raw, found = 0, status;
            Cec_TranCand_t got;
            abctime t = 0;
            Vec_IntPush(pool, 1); Vec_IntPush(pool, 2); Vec_IntPush(pool, 3);
            Abc_ResubPrepareManager(sim->nSlots);
            Cec_TranDepScratchStart(&dep, sim->nSlots, 3, 1);
            it = Cec_TranDependencyIteratorStart(sim, &Pars, &Root, pool,
                care+(size_t)root*sim->nSlots, &dep, cursor, &cache);
            while ( !exhausted && !found )
            {
                status = Cec_TranDependencyIteratorNext(sim, &Root, pool, care+(size_t)root*sim->nSlots,
                    0, &dep, it, &got, &attempt, &exhausted, NULL, &raw, &t);
                if ( status > 0 )
                {
                    found = got.nGates == 1 && !Cec_TranRecipeMatchesRoot(sim, &got, NULL);
                    Cec_TranCandRecipeRelease(&got);
                }
            }
            assert(found);
            Abc_ResubIteratorResumeStop(it, cursor); Abc_ResubRootCacheStop(cache);
            Cec_TranDepScratchStop(&dep); Abc_ResubPrepareManager(0); Vec_IntFree(pool);
        }
        Vec_IntPush(one, 0); q = Cec_TranDupRootBundle(p, &c, one);
        Gia_ManStaticFanoutStart(p);
        assert(Cec_TranRelOldProof(p, &c, &Pars, 0) == 0);
        assert(Cec_TranRelOldProof(p, &c, &Pars, 1) == 0);
        m = Gia_ManMiter(p, q, 0, 0, 1, 0, 0);
        assert(Cec_TranRelPdr(m, "witness-product", NULL, NULL) == 1);
        assert(Cec_TranRelStateProof(p, q) == 0);
        Abc_Print(1, "relobs-witness build=%d legacy-whole=%d\n", fBuild, Cec_TranProveWhole(p, q, &Pars, &Prof));
        Cec_TranRelDumpGia(p, fBuild, "witness-before"); Cec_TranRelDumpGia(q, fBuild, "witness-after");
        if ( !fBuild )
        {
            Gia_Man_t * pTail;
            Pars.nRelObs = 6; Pars.fOutputProof = 1;
            pTail = Cec_TranRunRelObs(Gia_ManDup(p), &Pars);
            assert(Gia_ManAndNum(pTail) < Gia_ManAndNum(p));
            assert(Gia_ManRegNum(pTail) == Gia_ManRegNum(p));
            assert(Cec_TranRelStateProof(p, pTail) == 0);
            Cec_TranRelDumpGia(p, 3, "tail-before"); Cec_TranRelDumpGia(pTail, 3, "tail-after");
            Gia_ManStop(pTail);
        }
        Gia_ManStaticFanoutStop(p); Gia_ManStop(m); Gia_ManStop(q);
        ABC_FREE(care); Cec_TranCandRecipeRelease(&c); Vec_IntFree(one);
        Cec_TranSimStop(sim); Cec_TranPatDbStop(db); Gia_ManStop(p);
    }
    {
        Gia_Man_t * p = Cec_TranRelWitness(0, 9, &root), * q, * m;
        Cec_TranCand_t c = Cec_TranCandCreateLiteral(root, 4, 1, CEC_TRAN_CAND_EXIST, 0);
        Vec_Int_t * one = Vec_IntAlloc(1);
        Vec_Ptr_t * bank = Vec_PtrAlloc(1);
        Abc_Cex_t * cex;
        Vec_IntPush(one, 0); q = Cec_TranDupRootBundle(p, &c, one);
        m = Gia_ManMiter(p, q, 0, 0, 1, 0, 0);
        assert(Cec_TranRelPdr(m, "delayed-negative", NULL, bank) == 0);
        cex = (Abc_Cex_t *)Vec_PtrEntry(bank, 0);
        assert(cex->iFrame >= 10 && Cec_TranRelReplay(p, q, cex));
        Cec_TranRelDumpGia(p, 2, "negative-before"); Cec_TranRelDumpGia(q, 2, "negative-after");
        Abc_CexFree(cex); Vec_PtrFree(bank); Vec_IntFree(one);
        Gia_ManStop(m); Gia_ManStop(q); Gia_ManStop(p);
    }
    Abc_Print(1, "relobs-selftest PASS: native Build, divergent states, permanent PO proof, delayed negative\n");
    return 1;
}
