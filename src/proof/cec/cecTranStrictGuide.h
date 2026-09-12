/* Auxiliary observations for the native strict single-root constructor.
 *
 * Every original reset-reachable observation is preserved. Add one independent
 * combinational observation per Q lane with free PIs and ROs. This strengthens
 * construction constraints and can exclude valid sequential recipes; these
 * are NOT reachable CEX and confer NO proof privileges. Ranking and Build use
 * the joined table; Direct matching retains the original reset teacher. The
 * existing complete root proof, composition and exact cleanup remain required.
 *
 * The flat table belongs to one immutable snapshot. No node IDs, RO values,
 * or auxiliary samples are carried across cleanup. No SAT recipe or extra
 * search pass is introduced. Randomness is independent of the Q/W teacher.
 */
static Cec_TranSim_t * Cec_TranStrictGuide( Cec_TranSim_t * pSource, int fProfile )
{
    abctime Start = Abc_Clock();
    Gia_Man_t * p = pSource->pGia;
    Cec_TranSim_t * pBuild = Cec_TranSimStartRootBatch( p,
        pSource->nSlots + pSource->nWords, 1 );
    word * pValues = ABC_CALLOC( word, Gia_ManObjNum(p) );
    word Random = ABC_CONST(0x319e7ad0604b), a, b;
    Gia_Obj_t * pObj;
    int i, w;
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        memcpy( Cec_TranSimObj(pBuild, i), Cec_TranSimObj(pSource, i),
            pSource->nSlots * sizeof(word) );
    for ( w = 0; w < pSource->nWords; w++ )
    {
        // Retain the measured prototype's independent stream and CI order.
        Gia_ManForEachRo( p, pObj, i )
            pValues[Gia_ObjId(p, pObj)] = Cec_TranSigGuideRandom( &Random );
        Gia_ManForEachPi( p, pObj, i )
            pValues[Gia_ObjId(p, pObj)] = Cec_TranSigGuideRandom( &Random );
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( Gia_ObjIsCi(pObj) ) continue;
            a = pValues[Gia_ObjFaninId0p(p, pObj)] ^
                (Gia_ObjFaninC0(pObj) ? ~(word)0 : 0);
            if ( Gia_ObjIsCo(pObj) || Gia_ObjIsBuf(pObj) )
                pValues[i] = a;
            else
            {
                b = pValues[Gia_ObjFaninId1p(p, pObj)] ^
                    (Gia_ObjFaninC1(pObj) ? ~(word)0 : 0);
                pValues[i] = Gia_ObjIsXor(pObj) ? a ^ b : a & b;
            }
        }
        for ( i = 0; i < Gia_ManObjNum(p); i++ )
            Cec_TranSimObj(pBuild, i)[pSource->nSlots + w] = pValues[i];
    }
    if ( fProfile )
        Abc_Print(1, "stran-root strict-signature-guide: schema=1 snapshots=1 source-rows=%d auxiliary-rows=%d skipped-overflow=0 prep-sec=%.6f\n",
            64 * pSource->nSlots, 64 * pSource->nWords,
            Cec_TranTimeSec(Abc_Clock() - Start));
    ABC_FREE( pValues );
    return pBuild;
}

static int Cec_TranStrictGuideSelfTest()
{
    Gia_Man_t * p = Gia_ManStart(32);
    int a = Gia_ManAppendCi(p), b = Gia_ManAppendCi(p);
    int q = Gia_ManAppendCi(p), ab = Gia_ManAppendAnd(p, a, b);
    int Root = Abc_LitNot(Gia_ManAppendAnd(p, Abc_LitNot(q), Abc_LitNot(ab)));
    Cec_ParTran_t Pars;
    Cec_TranPatDb_t * pDb;
    Cec_TranSim_t * pSource, * pBuild;
    int i, w, nExcluded = 0;
    Gia_ManAppendCo(p, Root); Gia_ManAppendCo(p, 0); Gia_ManSetRegNum(p, 1);
    Cec_ManTranSetDefaultParams(&Pars); Pars.nSimWords = 2; Pars.nSimFrames = 3;
    pDb = Cec_TranPatDbStart(p, 0);
    pSource = Cec_TranSimStart(p, &Pars, pDb);
    pBuild = Cec_TranStrictGuide(pSource, 0);
    assert(pBuild->nSlots == pSource->nSlots + 2);
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        assert(!memcmp(Cec_TranSimObj(pBuild, i), Cec_TranSimObj(pSource, i),
            pSource->nSlots * sizeof(word)));
    for ( w = 0; w < pBuild->nSlots; w++ )
    {
        word av = Cec_TranSimLit(pBuild, a, w), bv = Cec_TranSimLit(pBuild, b, w);
        word qv = Cec_TranSimLit(pBuild, q, w), rv = Cec_TranSimLit(pBuild, Root, w);
        assert(rv == (qv | (av & bv)));
        if ( w < pSource->nSlots ) assert(qv == 0 && rv == (av & bv));
        else nExcluded += Abc_TtCountOnes(rv ^ (av & bv));
    }
    // q starts at zero and q'=0, so Root=a&b is sequentially valid. Auxiliary
    // states deliberately exclude some such recipes: guidance is conservative,
    // not a claim of reset reachability or completeness.
    assert(nExcluded > 0);
    Cec_TranSimStop(pBuild); Cec_TranSimStop(pSource);
    Cec_TranPatDbStop(pDb); Gia_ManStop(p);
    Abc_Print(1, "Strict auxiliary signature preservation / free-state semantics / sequential exclusion self-test: PASS\n");
    return 1;
}
