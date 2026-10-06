// Independent finite-state oracle for the research relation prover.
// No CNF, unroll helper, proof status, or inferred relation is used by the
// scalar transition evaluator, reachable BFS, or greatest k-inductive subset.
#define CEC_REL_TEST_REQUIRE(C) do { if (!(C)) { \
    Abc_Print(-1,"relational exhaustive self-test failed at %s:%d: %s\n",__FILE__,__LINE__,#C); \
    abort(); } } while (0)

static unsigned Cec_TranRelTestRandom( unsigned * pSeed )
{
    *pSeed = 1664525u * *pSeed + 1013904223u;
    return *pSeed;
}

static word Cec_TranRelTestStep( Gia_Man_t * p, Vec_Int_t * vPairs,
    int State, int Inputs, int * pNext )
{
    int * Values = ABC_CALLOC(int, Gia_ManObjNum(p));
    Gia_Obj_t * o;
    int i, x, y, a, b, n = Vec_IntSize(vPairs)/2;
    word True = 0;
    CEC_REL_TEST_REQUIRE(n < 64);
    Gia_ManForEachPi(p,o,i) Values[Gia_ObjId(p,o)] = (Inputs >> i) & 1;
    Gia_ManForEachRo(p,o,i) Values[Gia_ObjId(p,o)] = (State >> i) & 1;
    Gia_ManForEachObj1(p,o,i)
    {
        if ( Gia_ObjIsCi(o) ) continue;
        x = Values[Gia_ObjFaninId0p(p,o)] ^ Gia_ObjFaninC0(o);
        if ( Gia_ObjIsCo(o) || Gia_ObjIsBuf(o) ) Values[i] = x;
        else
        {
            y = Values[Gia_ObjFaninId1p(p,o)] ^ Gia_ObjFaninC1(o);
            Values[i] = Gia_ObjIsXor(o) ? x ^ y : x & y;
        }
    }
    *pNext = 0;
    Gia_ManForEachRi(p,o,i) *pNext |= Values[Gia_ObjId(p,o)] << i;
    for ( i = 0; i < n; ++i )
    {
        a = Vec_IntEntry(vPairs,2*i); b = Vec_IntEntry(vPairs,2*i+1);
        x = Values[Abc_Lit2Var(a)] ^ Abc_LitIsCompl(a);
        y = Values[Abc_Lit2Var(b)] ^ Abc_LitIsCompl(b);
        if ( x == y ) True |= (word)1 << i;
    }
    ABC_FREE(Values);
    return True;
}

static word Cec_TranRelTestReachable( int nStates, int nInputs,
    int * Next, word * Truth, word All, int * pReached )
{
    int Queue[16], Seen[16] = {0}, Head = 0, Tail = 1, s, u, t;
    word Invariants = All;
    CEC_REL_TEST_REQUIRE(nStates <= 16);
    Seen[0] = 1; Queue[0] = 0;
    while ( Head < Tail )
    {
        s = Queue[Head++];
        for ( u = 0; u < nInputs; ++u )
        {
            Invariants &= Truth[s*nInputs+u];
            t = Next[s*nInputs+u];
            if ( !Seen[t] ) { Seen[t] = 1; Queue[Tail++] = t; }
        }
    }
    *pReached = Tail;
    return Invariants;
}

static word Cec_TranRelTestHoudini( int nStates, int nInputs,
    int * Next, word * Truth, word All, int k, int * pRounds )
{
    // Exhaust all reset prefixes of length k. Each frame has independent PIs.
    int nTraces = 1, nBaseTraces, trace, code, s, u, f, start, Changed;
    word Alive = All, Bad;
    for ( f = 0; f < k; ++f ) nTraces *= nInputs;
    nBaseTraces = nTraces;
    for ( trace = 0; trace < nBaseTraces; ++trace )
    {
        s = 0; code = trace;
        for ( f = 0; f < k; ++f )
        {
            u = code % nInputs; code /= nInputs;
            Alive &= Truth[s*nInputs+u];
            s = Next[s*nInputs+u];
        }
    }
    nTraces *= nInputs;
    *pRounds = 0;
    do
    {
        Bad = 0; ++*pRounds;
        // The hypothesis set is frozen for the whole round, exactly the
        // mathematical simultaneous greatest-subset operator.
        for ( start = 0; start < nStates; ++start )
        for ( trace = 0; trace < nTraces; ++trace )
        {
            s = start; code = trace;
            for ( f = 0; f < k; ++f )
            {
                u = code % nInputs; code /= nInputs;
                if ( (Truth[s*nInputs+u] & Alive) != Alive ) break;
                s = Next[s*nInputs+u];
            }
            if ( f != k ) continue;
            u = code % nInputs;
            Bad |= Alive & ~Truth[s*nInputs+u];
        }
        Changed = Bad != 0; Alive &= ~Bad;
    } while ( Changed && Alive );
    return Alive;
}

static Gia_Man_t * Cec_TranRelTestGraph( int Graph, unsigned * Seed,
    Vec_Int_t * vPairs )
{
    Gia_Man_t * p = Gia_ManStart(128);
    int nPis = Graph % 3, nRegs = 1 + Graph % 4;
    int Pi[2], Ro[4], Next[4], i, j, a, b, x, Last, Buf;
    for ( i = 0; i < nPis; ++i ) Pi[i] = Gia_ManAppendCi(p);
    for ( i = 0; i < nRegs; ++i ) Ro[i] = Gia_ManAppendCi(p);
    for ( i = 0; i < 12; ++i )
    {
        a = (int)(Cec_TranRelTestRandom(Seed) % (2*Gia_ManObjNum(p)));
        b = (int)(Cec_TranRelTestRandom(Seed) % (2*Gia_ManObjNum(p)));
        if ( i % 3 == 0 ) x = Gia_ManAppendBuf(p, a);
        else if ( i % 3 == 1 ) x = Gia_ManAppendXorReal2(p, a, b);
        else x = Gia_ManAppendAnd2(p, a, b);
        (void)x;
    }
    Last = 2*(Gia_ManObjNum(p)-1);
    Buf = Gia_ManAppendBuf(p, Ro[0]);
    for ( i = 0; i < nRegs; ++i )
    {
        switch ( Graph % 6 )
        {
        case 0: Next[i] = Ro[(i+1)%nRegs]; break;
        case 1: Next[i] = Ro[(i+1)%nRegs]^1; break;
        case 2: Next[i] = nPis ? Pi[0] : Last; break;
        case 3: Next[i] = i+1 < nRegs ? Ro[i+1] : 1; break;
        case 4: Next[i] = (int)(Cec_TranRelTestRandom(Seed) % (2*Gia_ManObjNum(p))); break;
        default: Next[i] = Gia_ManAppendXorReal2(p, Ro[(i+1)%nRegs], nPis ? Pi[0] : 1); break;
        }
    }
    Vec_IntClear(vPairs);
    for ( i = 0; i < nRegs; ++i )
    {
        Vec_IntPushTwo(vPairs,Ro[i],0); Vec_IntPushTwo(vPairs,Ro[i],1);
        for ( j = 0; j < i; ++j )
        {
            Vec_IntPushTwo(vPairs,Ro[i],Ro[j]);
            Vec_IntPushTwo(vPairs,Ro[i],Ro[j]^1);
        }
    }
    for ( i = 0; i < 16; ++i )
    {
        a = (int)(Cec_TranRelTestRandom(Seed) % (2*Gia_ManObjNum(p)));
        b = (int)(Cec_TranRelTestRandom(Seed) % (2*Gia_ManObjNum(p)));
        Vec_IntPushTwo(vPairs,a,b);
    }
    Vec_IntPushTwo(vPairs,0,0); Vec_IntPushTwo(vPairs,0,1);
    Vec_IntPushTwo(vPairs,Buf,Ro[0]); Vec_IntPushTwo(vPairs,Last,Last);
    for ( i = 0; i < nPis; ++i ) Vec_IntPushTwo(vPairs,Pi[i],0);
    Gia_ManAppendCo(p,Last); Gia_ManAppendCo(p,Buf);
    for ( i = 0; i < nRegs; ++i ) Gia_ManAppendCo(p,Next[i]);
    Gia_ManSetRegNum(p,nRegs);
    return p;
}

static int Cec_TranRelationalBfsSelfTest()
{
    unsigned Seed = 0x6C656761u;
    Vec_Int_t * Pairs = Vec_IntAlloc(128), * Status;
    Cec_ParTran_t Pars;
    int Graph, k, s, u, i, n, nStates, nInputs, Reached, Rounds, OracleRounds;
    int Next[64], Graphs = 48, Proved = 0, Refuted = 0, Compared = 0, MultiRound = 0;
    word Truth[64], All, Reachable, Oracle, Actual;
    Cec_ManTranSetDefaultParams(&Pars); Pars.nBTLimit = 10000;
    for ( Graph = 0; Graph < Graphs; ++Graph )
    {
        Gia_Man_t * p = Cec_TranRelTestGraph(Graph,&Seed,Pairs);
        n = Vec_IntSize(Pairs)/2; All = ((word)1 << n)-1;
        nStates = 1 << Gia_ManRegNum(p); nInputs = 1 << Gia_ManPiNum(p);
        CEC_REL_TEST_REQUIRE(nStates*nInputs <= 64);
        for ( s = 0; s < nStates; ++s )
        for ( u = 0; u < nInputs; ++u )
            Truth[s*nInputs+u] = Cec_TranRelTestStep(p,Pairs,s,u,&Next[s*nInputs+u]);
        Reachable = Cec_TranRelTestReachable(nStates,nInputs,Next,Truth,All,&Reached);
        for ( k = 1; k <= 3; ++k )
        {
            Pars.nFrames = k;
            Oracle = Cec_TranRelTestHoudini(nStates,nInputs,Next,Truth,All,k,&OracleRounds);
            Status = Cec_TranRelationalProve(p,Pairs,&Pars,&Rounds); Actual = 0;
            CEC_REL_TEST_REQUIRE(Vec_IntSize(Status) == n);
            for ( i = 0; i < n; ++i )
            {
                int Value = Vec_IntEntry(Status,i);
                CEC_REL_TEST_REQUIRE(Value == 0 || Value == 1);
                if ( Value == 1 ) { Actual |= (word)1 << i; ++Proved; }
                else ++Refuted;
                ++Compared;
            }
            CEC_REL_TEST_REQUIRE(Actual == Oracle);
            CEC_REL_TEST_REQUIRE((Actual & ~Reachable) == 0);
            CEC_REL_TEST_REQUIRE(Rounds == OracleRounds);
            MultiRound += Rounds > 1;
            Vec_IntFree(Status);
        }
        Gia_ManStop(p);
    }
    Vec_IntFree(Pairs);
    CEC_REL_TEST_REQUIRE(Proved > 0 && Refuted > 0 && MultiRound > 0);
    Abc_Print(1,"Relational exhaustive BFS / maximum k-inductive subset self-test: PASS graphs=%d depths=1,2,3 comparisons=%d proved=%d refuted=%d multiround=%d unknown=0\n",Graphs,Compared,Proved,Refuted,MultiRound);
    return 1;
}
#undef CEC_REL_TEST_REQUIRE
