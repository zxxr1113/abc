/**CFile****************************************************************

  FileName    [sim_accel_kernel.inc]

  Synopsis    [Template inner kernel — included 3× by the backend .c files.
               Each inclusion defines SIM_BACKEND to a unique token suffix,
               producing three distinct function symbols.

               Convention:
                 pRes, pRes0, pRes1  point to simulation data (NOT the
                 refcount slot — caller passes pRes+1 from cecClass.c).
                 Length is nWords32 uint32_t elements.

               The XOR-mask idiom unifies all 4 fanin-complement cases
               into one formula:
                 result[w] = (p0[w] ^ mask0) & (p1[w] ^ mask1)
               which is bitwise-equivalent to the original 4-branch code.]

***********************************************************************/

/* Name-mangling helpers — one level of indirection to force expansion */
#define SIM_KFN_(nm, sfx)  Sim_Kernel_##nm##_##sfx
#define SIM_KFN(nm, sfx)   SIM_KFN_(nm, sfx)

/* ------------------------------------------------------------------ */
/* AND inner kernel                                                     */
/* ------------------------------------------------------------------ */
static void
SIM_KFN(AndNode, SIM_BACKEND)(
    unsigned       *  pRes,
    const unsigned *  p0, int c0,
    const unsigned *  p1, int c1,
    int nWords32 )
{
    Sim_Vec_t m0 = SIM_VBCAST_FROM_BIT(c0);
    Sim_Vec_t m1 = SIM_VBCAST_FROM_BIT(c1);
    int nVec = SIM_NVEC(nWords32);
    int v;

    for ( v = 0; v < nVec; v++ )
    {
        const unsigned *pp0 = p0   + v * SIM_VEC_WORDS32;
        const unsigned *pp1 = p1   + v * SIM_VEC_WORDS32;
        unsigned       *ppd = pRes + v * SIM_VEC_WORDS32;
        Sim_Vec_t a = SIM_VXOR(SIM_VLOAD(pp0), m0);
        Sim_Vec_t b = SIM_VXOR(SIM_VLOAD(pp1), m1);
        SIM_VSTORE(ppd, SIM_VAND(a, b));
    }

    /* scalar tail: (nWords32*4) % SIM_VEC_BYTES bytes remaining */
    {
        int wOff = nVec * SIM_VEC_WORDS32;
        uint32_t mm0 = c0 ? ~0u : 0u;
        uint32_t mm1 = c1 ? ~0u : 0u;
        int w;
        for ( w = wOff; w < nWords32; w++ )
            pRes[w] = (p0[w] ^ mm0) & (p1[w] ^ mm1);
    }
}

/* ------------------------------------------------------------------ */
/* CO output kernel  (copy fanin to output buffer, optional invert)    */
/* ------------------------------------------------------------------ */
static void
SIM_KFN(CoNode, SIM_BACKEND)(
    unsigned       *  pOut,
    const unsigned *  pIn, int c0,
    int nWords32 )
{
    Sim_Vec_t mask = SIM_VBCAST_FROM_BIT(c0);
    int nVec = SIM_NVEC(nWords32);
    int v;

    for ( v = 0; v < nVec; v++ )
    {
        const unsigned *pp = pIn  + v * SIM_VEC_WORDS32;
        unsigned       *pd = pOut + v * SIM_VEC_WORDS32;
        SIM_VSTORE(pd, SIM_VXOR(SIM_VLOAD(pp), mask));
    }

    {
        int wOff = nVec * SIM_VEC_WORDS32;
        uint32_t mm = c0 ? ~0u : 0u;
        int w;
        for ( w = wOff; w < nWords32; w++ )
            pOut[w] = pIn[w] ^ mm;
    }
}

#undef SIM_KFN
#undef SIM_KFN_
