/**CFile****************************************************************

  FileName    [cec_sim_round.inc]

  Synopsis    [Template body for Cec_ManSimSimulateRound_<backend>.

               This file is #included three times by cecClass.c, each time
               with different macros, producing three specialised round
               functions that fully inline the inner AND/CO kernel.

               Required macros at #include site:
                 ROUND_SUFFIX                       (token used as suffix)
                 ROUND_AND(pd, p0, c0, p1, c1, n)   inline AND kernel call
                 ROUND_CO(po, pi, c0, n)            inline CO  kernel call

               Layout reminder for callers (see cecClass.c near line 420):
                 Each AIG object i has a slot of size (p->nWords + 1)
                 uint32 in p->pMems. pSim[0] is the refcount; pSim[1..nWords]
                 is the simulation data. The kernels take pRes+1 as the
                 0-indexed data pointer and write pRes[0..n-1] from there.
                 The outer logic still touches pRes[0] for refcount bumps.]

***********************************************************************/

#ifndef ROUND_SUFFIX
#  error "cec_sim_round.inc: define ROUND_SUFFIX, ROUND_AND, ROUND_CO before include"
#endif

#define ROUND_FN_(nm, sfx)  nm##_##sfx
#define ROUND_FN(nm, sfx)   ROUND_FN_(nm, sfx)

static int ROUND_FN(Cec_ManSimSimulateRound, ROUND_SUFFIX) (
    Cec_ManSim_t * p, Vec_Ptr_t * vInfoCis, Vec_Ptr_t * vInfoCos )
{
    Gia_Obj_t * pObj;
    unsigned * pRes0, * pRes1, * pRes;
    int i, k, w, Ent, iCiId = 0, iCoId = 0;

    if ( p->nWordsOld != p->nWords )
        Cec_ManSimMemRelink( p );
    p->nMemsMax = 0;
    ABC_FREE( p->pScores );
    if ( p->pBestState )
        p->pScores = ABC_CALLOC( int, 32 * p->nWords );

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
            pRes[1] ^= (pRes[1] & 1);
            goto references;
        }
        if ( Gia_ObjIsCo(pObj) )
        {
            pRes0 = Cec_ManSimSimDeref( p, Gia_ObjFaninId0(pObj,i) );
            if ( vInfoCos )
            {
                pRes = (unsigned *)Vec_PtrEntry( vInfoCos, iCoId++ );
                ROUND_CO( pRes, pRes0 + 1, Gia_ObjFaninC0(pObj), p->nWords );
            }
            continue;
        }
        assert( Gia_ObjValue(pObj) );
        pRes  = Cec_ManSimSimRef( p, i );
        pRes0 = Cec_ManSimSimDeref( p, Gia_ObjFaninId0(pObj,i) );
        pRes1 = Cec_ManSimSimDeref( p, Gia_ObjFaninId1(pObj,i) );

        ROUND_AND( pRes + 1,
                   pRes0 + 1, Gia_ObjFaninC0(pObj),
                   pRes1 + 1, Gia_ObjFaninC1(pObj),
                   p->nWords );

references:
        if ( Gia_ObjIsConst(p->pAig, i) && !Cec_ManSimCompareConst(pRes + 1, p->nWords) )
        {
            pRes[0]++;
            Vec_IntPush( p->vRefinedC, i );
            if ( p->pBestState )
                Cec_ManSimCompareConstScore( pRes + 1, p->nWords, p->pScores );
        }
        if ( Gia_ObjIsClass(p->pAig, i) )
            pRes[0]++;
        if ( Gia_ObjIsTail(p->pAig, i) )
        {
            Vec_IntClear( p->vClassTemp );
            Gia_ClassForEachObj( p->pAig, Gia_ObjRepr(p->pAig, i), Ent )
                Vec_IntPush( p->vClassTemp, Ent );
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
    return Cec_ManSimAnalyzeOutputs( p );
}

#undef ROUND_FN
#undef ROUND_FN_
