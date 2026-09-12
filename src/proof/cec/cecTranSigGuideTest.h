// Deterministic invariants for auxiliary sampling, not an equivalence oracle.
static int Cec_TranSigGuideSelfTest()
{
    Gia_Man_t * g = Gia_ManStart( 128 );
    Cec_TranSigGuide_t * p;
    Cec_TranSim_t * old, * sim;
    Vec_Int_t * pool = Vec_IntAlloc( 40 );
    Gia_Obj_t * obj;
    int a, b, root, i, j, conflict, found, literal, x, buf;
    word * care;
    a = Gia_ManAppendCi(g); b = Gia_ManAppendCi(g);
    root = Gia_ManAppendAnd(g, a, b);
    Gia_ManAppendCo(g, root);
    Vec_IntPush(pool, Abc_Lit2Var(a)); Vec_IntPush(pool, Abc_Lit2Var(b));
    assert( Cec_TranSigGuideStart(g, 0) == NULL );
    p = Cec_TranSigGuideStart(g, 1);
    old = Cec_TranSimStartRootBatch(g, 513, 1);
    for ( i = 0; i < old->nSlots; i++ )
        Cec_TranSimObj(old, Abc_Lit2Var(b))[i] = ABC_CONST(0xaaaaaaaaaaaaaaaa);
    care = ABC_ALLOC(word, old->nSlots);
    for ( i = 0; i < old->nSlots; i++ ) care[i] = ~(word)0;
    sim = old; conflict = 0;
    Cec_TranSigGuideApply(p, Abc_Lit2Var(root), pool, &sim, &care, &conflict);
    assert( !conflict && p->nCapacity == 514 && sim->nSlots == 1 );
    assert( p->nRowsAfter == 4 && p->nChanged == 1 && p->nSplit == 1 );
    for ( x = 0; x < 4; x++ )
    {
        found = 0;
        for ( j = 0; j < 64; j++ )
            if ( (care[0] >> j) & 1 )
            {
                int v = ((Cec_TranSimObj(sim, Abc_Lit2Var(a))[0] >> j) & 1) |
                    (((Cec_TranSimObj(sim, Abc_Lit2Var(b))[0] >> j) & 1) << 1);
                assert( ((Cec_TranSimObj(sim, Abc_Lit2Var(root))[0] >> j) & 1) == (v == 3) );
                found += v == x;
            }
        assert( found == 1 );
    }
    ABC_FREE(care);
    // Conflicting target labels must survive compaction and stop construction.
    Vec_IntShrink(pool, 1);
    for ( i = 0; i < old->nSlots; i++ )
    {
        Cec_TranSimObj(old, Abc_Lit2Var(a))[i] = ABC_CONST(0xaaaaaaaaaaaaaaaa);
        Cec_TranSimObj(old, Abc_Lit2Var(b))[i] = 0;
    }
    care = ABC_ALLOC(word, old->nSlots);
    for ( i = 0; i < old->nSlots; i++ ) care[i] = ~(word)0;
    sim = old; conflict = 0;
    Cec_TranSigGuideApply(p, Abc_Lit2Var(root), pool, &sim, &care, &conflict);
    assert( conflict && p->nConflicts == 1 );
    ABC_FREE(care);
    Cec_TranSimStop(old); Cec_TranSigGuideStop(p, 0, 0); Gia_ManStop(g);

    // A rare 32-input conjunction is absent in the fixed 64 random lanes.
    // Its SAT cube supplies the positive label without touching source Value.
    g = Gia_ManStart(128); Vec_IntClear(pool);
    for ( i = 0; i < 32; i++ ) Vec_IntPush(pool, Gia_ManAppendCi(g) >> 1);
    root = 2 * Vec_IntEntry(pool, 0);
    for ( i = 1; i < 32; i++ ) root = Gia_ManAppendAnd(g, root, 2 * Vec_IntEntry(pool, i));
    Gia_ManAppendCo(g, root);
    Gia_ManForEachObj(g, obj, i) obj->Value = 1000 + i;
    p = Cec_TranSigGuideStart(g, 2);
    assert( Cec_TranSimObj(p->pExtra, root >> 1)[0] == 0 );
    for ( i = 0; i < CEC_TRAN_GUIDE_SAT_QUERIES; i++ )
        assert( Cec_TranSigGuideCube(p, root >> 1, pool) );
    assert( !Cec_TranSigGuideCube(p, root >> 1, pool) );
    assert( p->nSatCalls == CEC_TRAN_GUIDE_SAT_QUERIES && p->nSatYes == p->nSatCalls );
    Gia_ManForEachObj(g, obj, i) assert( obj->Value == (unsigned)(1000 + i) );
    assert( p->pValues[root >> 1] == ~(word)0 );
    Cec_TranSigGuideStop(p, 0, 0); Gia_ManStop(g);

    // Private SAT mapping handles buffers/XORs and uses the same CI order.
    g = Gia_ManStart(32); Vec_IntClear(pool);
    a = Gia_ManAppendCi(g); b = Gia_ManAppendCi(g);
    x = Gia_ManAppendXorReal(g, a, b); buf = Gia_ManAppendBuf(g, x);
    Gia_ManAppendCo(g, buf);
    p = Cec_TranSigGuideStart(g, 2); Cec_TranSigGuideStartSat(p);
    for ( i = 0; i < 4; i++ )
    {
        int lits[3] = { Abc_LitNotCond(p->pSatLits[a >> 1], !(i & 1)),
            Abc_LitNotCond(p->pSatLits[b >> 1], !(i & 2)),
            Abc_LitNotCond(p->pSatLits[buf >> 1], !!((i & 1) ^ ((i >> 1) & 1))) };
        assert( Cbs_ManSolveLits(p->pSat, lits, 3) == 1 );
        lits[2] ^= 1;
        assert( Cbs_ManSolveLits(p->pSat, lits, 3) == 0 );
    }
    Cec_TranSigGuideStop(p, 0, 0); Gia_ManStop(g);

    // An unsatisfiable CNF requires a branch. A zero-conflict budget returns
    // UNKNOWN and must not add a cube; a regular budget establishes UNSAT.
    g = Gia_ManStart(32); Vec_IntClear(pool);
    a = Gia_ManAppendCi(g); b = Gia_ManAppendCi(g);
    root = 1;
    for ( i = 0; i < 4; i++ )
    {
        literal = Gia_ManAppendOr(g, a ^ (i & 1), b ^ ((i >> 1) & 1));
        root = Gia_ManAppendAnd2(g, root, literal);
    }
    Gia_ManAppendCo(g, root);
    p = Cec_TranSigGuideStart(g, 2); Cec_TranSigGuideStartSat(p);
    Cbs_ManSetConflictNum(p->pSat, 0);
    assert( !Cec_TranSigGuideCube(p, root >> 1, pool) && p->nSatUnknown == 1 );
    Cbs_ManSetConflictNum(p->pSat, CEC_TRAN_GUIDE_SAT_CONFLICTS);
    assert( !Cec_TranSigGuideCube(p, root >> 1, pool) && p->nSatNo == 1 );
    assert( !p->Stamp && !p->nSatYes );
    Cec_TranSigGuideStop(p, 0, 0); Gia_ManStop(g);
    Vec_IntFree(pool);
    ABC_FREE(s_CexWeights);
    return 1;
}
