/** Native integration test: nomination, ownership, withdrawal, and counts. */
static int Cec_TranConstHelperSelfTest()
{
    char const * RelEnv = "ABC_ODC_RELATIONAL_PROOF";
    char const * HelpEnv = "ABC_ODC_CONST_HELPERS";
    char * SavedRel = getenv(RelEnv) ? Abc_UtilStrsav(getenv(RelEnv)) : NULL;
    char * SavedHelp = getenv(HelpEnv) ? Abc_UtilStrsav(getenv(HelpEnv)) : NULL;
    Cec_ParTran_t Pars;
    Cec_TranProf_t NomProf = {0};
    Cec_TranCandVec_t Helpers = {0}, Mixed = {0}, Obligations = {0};
    Cec_TranPatDb_t * pDb;
    Cec_TranSim_t * pSource;
    Cec_TranCand_t Build, Direct, False, Universal;
    Gia_Man_t * p;
    int a, b, q0, q1, d, h, t, r, k, i, Factor, Multi;
    if ( setenv(RelEnv,"1",1) || setenv(HelpEnv,"1",1) ) abort();
    Cec_ManTranSetDefaultParams(&Pars);
    Pars.fOdcFanout = Pars.fOdcProofScope = Pars.fOdcStrict = 1;
    Pars.nFrames = 1; Pars.nBTLimit = Pars.nCombBTLimit = 1000;
    Pars.nStepsMax = -1; Pars.nExplore = 134217728; Pars.nOdcProofMax = 0;
    assert(Pars.nSimWords == 4 && Pars.nSimFrames == 8);
    assert(Cec_TranConstHelpersEnabled(&Pars));
    assert(!Cec_TranConstHelperPolicyAllowed(&Pars,0));
    assert(!Cec_TranConstHelperPolicyAllowed(&Pars,2));
    Pars.fOdcProofScope = 0;
    assert(!Cec_TranConstHelperPolicyAllowed(&Pars,1));
    Pars.fOdcProofScope = 1;
    if ( setenv(HelpEnv,"0",1) ) abort();
    assert(!Cec_TranConstHelpersEnabled(&Pars));
    if ( setenv(HelpEnv,"1",1) ) abort();

    // h=q0&q1 is a stable reset CONST0, k=~q0&~q1 a stable CONST1.
    // R: (~h&a)&b == a&b is true from reset, but R alone is not inductive:
    // h=1,a=0 satisfies R, then fresh a=b=1 violates it.  Helpers close R.
    // d resets to 0 and becomes 1, giving a reset-valid false induction helper.
    p = Gia_ManStart(32);
    a = Gia_ManAppendCi(p); b = Gia_ManAppendCi(p);
    q0 = Gia_ManAppendCi(p); q1 = Gia_ManAppendCi(p); d = Gia_ManAppendCi(p);
    h = Gia_ManAppendAnd(p,q0,q1);
    t = Gia_ManAppendAnd(p,h^1,a); r = Gia_ManAppendAnd(p,t,b);
    k = Gia_ManAppendAnd(p,q0^1,q1^1);
    Gia_ManAppendCo(p,r); Gia_ManAppendCo(p,k);
    Gia_ManAppendCo(p,q0); Gia_ManAppendCo(p,q1); Gia_ManAppendCo(p,1);
    Gia_ManSetRegNum(p,3); Gia_ManCreateRefs(p); Gia_ManStaticFanoutStart(p);
    assert(Gia_NodeMffcSize(p,Gia_ManObj(p,Abc_Lit2Var(h))) == 1);
    pDb = Cec_TranPatDbStart(p,0);
    pSource = Cec_TranSimStart(p,&Pars,pDb);
    Cec_TranConstHelperNominate(p,pSource,&Helpers,&NomProf);
    assert(NomProf.nOdcConstScanned == 4 && Helpers.nSize == 2);
    assert(NomProf.nOdcConstZero == 1 && NomProf.nOdcConstOne == 1);
    assert(Helpers.pArray[0].iTarget == Abc_Lit2Var(h) && Helpers.pArray[0].iOut == 0);
    assert(Helpers.pArray[1].iTarget == Abc_Lit2Var(k) && Helpers.pArray[1].iOut == 1);
    for ( i = 0; i < pSource->nSlots; i++ )
        Cec_TranSimObj(pSource,Abc_Lit2Var(h))[i] = ~(word)0;
    Cec_TranSimStop(pSource); Cec_TranPatDbStop(pDb);
    assert(Helpers.pArray[0].iOut == 0 && Helpers.pArray[0].Recipe == NULL);
    Build = Cec_TranCandCreateLiteral(Abc_Lit2Var(r),0,3,CEC_TRAN_CAND_CONSTR,0);
    Build.nGates = 1; Build.Gain = 2;
    Build.Recipe = Cec_TranRecipeAlloc(2);
    Build.Recipe[0] = a; Build.Recipe[1] = b;
    Build.iOut = Cec_TranRecipeGateCode(0,0);
    Direct = Cec_TranCandCreateLiteral(Abc_Lit2Var(h),0,1,CEC_TRAN_CAND_CONST,1);
    Direct.Gain = 1;
    for ( i = 0; i < Helpers.nSize; i++ ) Cec_TranCandVecPush(&Mixed,Helpers.pArray[i]);
    False = Cec_TranCandCreateLiteral(Abc_Lit2Var(h),1,0,CEC_TRAN_CAND_CONST,1);
    False.Gain = 0; Cec_TranCandVecPush(&Mixed,False);
    False = Cec_TranCandCreateLiteral(Abc_Lit2Var(d),0,0,CEC_TRAN_CAND_CONST,1);
    False.Gain = 0; Cec_TranCandVecPush(&Mixed,False);
    Cec_TranCandVecPush(&Obligations,Build); Cec_TranCandVecPush(&Obligations,Direct);

    for ( Factor = 0; Factor < 2; Factor++ )
    for ( Multi = 0; Multi < 2; Multi++ )
    {
        Cec_TranProf_t Prof = {0};
        Vec_Int_t * Status, * Pairs, * Comb, * Queries, * Leaves, * Raw;
        Vec_Str_t * Stage = NULL, * Counts;
        Gia_Man_t * Batch;
        int Full = 0, Rounds;
        Pars.fWindowFactor = Factor; Pars.fUseCbsMultiLit = Multi;
        Status = Factor ? Cec_TranProveWindowFactorBatch(p,NULL,0,&Build,1,
            &Pars,&Prof,0,&Stage,&Full) : Cec_TranProveRootBatch(p,NULL,0,
            &Build,1,&Pars,&Prof,0,&Stage);
        assert(Vec_IntSize(Status) == 1 && Vec_IntEntry(Status,0) == 0);
        assert(Prof.nOdcConstInjected == 0 && Prof.nOdcConstChecked == 0);
        Vec_IntFree(Status); Vec_StrFree(Stage); memset(&Prof,0,sizeof(Prof));
        Status = Factor ? Cec_TranProveWindowFactorBatch(p,Mixed.pArray,Mixed.nSize,
            &Build,1,&Pars,&Prof,0,&Stage,&Full) : Cec_TranProveRootBatch(p,
            Mixed.pArray,Mixed.nSize,&Build,1,&Pars,&Prof,0,&Stage);
        assert(Vec_IntSize(Status) == 1 && Vec_StrSize(Stage) == 1);
        assert(Vec_IntEntry(Status,0) == 1 && Vec_StrEntry(Stage,0) == 2);
        assert(Prof.nSeqCands == 1 && Prof.nSeqProved == 1);
        assert(Prof.nOdcConstInjected == 4 && Prof.nOdcConstChecked == 4);
        assert(Prof.nOdcConstSurvived == 2 && Prof.nOdcConstWithdrawn == 2 &&
            Prof.nOdcConstUnknown == 0 && Prof.nSeqSeeded == 5);
        Vec_IntFree(Status); Vec_StrFree(Stage);

        // CBS proves this identity without using any speculative helper.
        // Injected but unchecked helpers must not be called surviving proofs.
        Universal = Cec_TranCandCreateLiteral(Abc_Lit2Var(r),r,0,CEC_TRAN_CAND_EXIST,1);
        memset(&Prof,0,sizeof(Prof));
        Status = Factor ? Cec_TranProveWindowFactorBatch(p,Mixed.pArray,Mixed.nSize,
            &Universal,1,&Pars,&Prof,0,&Stage,&Full) : Cec_TranProveRootBatch(p,
            Mixed.pArray,Mixed.nSize,&Universal,1,&Pars,&Prof,0,&Stage);
        assert(Vec_IntSize(Status) == 1 && Vec_IntEntry(Status,0) == 1 &&
            Vec_StrEntry(Stage,0) == 1 && Prof.nSeqCands == 0);
        assert(Prof.nOdcConstInjected == 4 && !Prof.nOdcConstChecked &&
            !Prof.nOdcConstSurvived && !Prof.nOdcConstWithdrawn && !Prof.nSeqSeeded);
        Vec_IntFree(Status); Vec_StrFree(Stage);

        // Independent raw statuses certify both withdrawals and the exact
        // helper-first candidate offset, with the original RI functions intact.
        Leaves = NULL; Counts = NULL;
        Batch = Factor ? Cec_TranBuildWindowFactorBatch(p,Mixed.pArray,Mixed.nSize,
            &Build,1,&Pars,&Pairs,&Comb,&Queries,&Leaves,&Counts,&Full) :
            Cec_TranBuildRootBatch(p,Mixed.pArray,Mixed.nSize,&Build,1,Multi ? 0 : 2,
            &Pairs,&Comb,&Queries,Multi ? &Leaves : NULL,Multi ? &Counts : NULL);
        assert(Vec_IntSize(Pairs) == 10 && Vec_IntSize(Comb) == 2);
        assert(Vec_IntSize(Queries) == (Multi ? 0 : 1));
        assert(!Counts || Vec_StrSize(Counts) == 1);
        assert(Gia_ManRegNum(Batch) == 3);
        assert(Gia_ObjFaninLit0p(Batch,Gia_ManRi(Batch,0)) == q0);
        assert(Gia_ObjFaninLit0p(Batch,Gia_ManRi(Batch,1)) == q1);
        assert(Gia_ObjFaninLit0p(Batch,Gia_ManRi(Batch,2)) == 1);
        Raw = Cec_TranRelationalProve(Batch,Pairs,&Pars,&Rounds);
        assert(Vec_IntSize(Raw) == 5 && Vec_IntEntry(Raw,0) == 1 &&
            Vec_IntEntry(Raw,1) == 1 && Vec_IntEntry(Raw,2) == 0 &&
            Vec_IntEntry(Raw,3) == 0 && Vec_IntEntry(Raw,4) == 1);
        Vec_IntFree(Raw); Vec_IntFree(Pairs); Vec_IntFree(Comb); Vec_IntFree(Queries);
        Vec_IntFreeP(&Leaves); Vec_StrFreeP(&Counts); Gia_ManStop(Batch);

        // A mixed candidate batch shares the same helper prefix. Helpers
        // contribute no returned candidate rows or committed-edit counts.
        memset(&Prof,0,sizeof(Prof)); Full = 0;
        Status = Factor ? Cec_TranProveWindowFactorBatch(p,Helpers.pArray,
            Helpers.nSize,Obligations.pArray,Obligations.nSize,&Pars,&Prof,
            0,&Stage,&Full) : Cec_TranProveRootBatch(p,Helpers.pArray,
            Helpers.nSize,Obligations.pArray,Obligations.nSize,&Pars,&Prof,0,&Stage);
        assert(Vec_IntSize(Status) == 2 && Vec_StrSize(Stage) == 2);
        assert(Vec_IntEntry(Status,0) == 1 && Vec_IntEntry(Status,1) == 1);
        assert(Prof.nSeqCands == 2 && Prof.nSeqProved == 2 && Prof.nSeqSeeded == 4);
        assert(Prof.nOdcConstInjected == 2 && Prof.nOdcConstChecked == 2 &&
            Prof.nOdcConstSurvived == 2 && !Prof.nOdcConstWithdrawn);
        assert(Full >= 0 && Full <= 2);
        Vec_IntFree(Status); Vec_StrFree(Stage);
    }
    Cec_TranCandRecipeRelease(&Build); Cec_TranCandVecStop(&Obligations);
    Cec_TranCandVecStop(&Mixed); Cec_TranCandVecStop(&Helpers);
    Gia_ManStaticFanoutStop(p); Gia_ManStop(p);
    if ( SavedRel ) { if ( setenv(RelEnv,SavedRel,1) ) abort(); ABC_FREE(SavedRel); }
    else if ( unsetenv(RelEnv) ) abort();
    if ( SavedHelp ) { if ( setenv(HelpEnv,SavedHelp,1) ) abort(); ABC_FREE(SavedHelp); }
    else if ( unsetenv(HelpEnv) ) abort();
    Abc_Print(1,"ODC CONST-helper self-test passed: nomination ownership factor unfactored withdrawal candidate-offsets.\n");
    return 1;
}
