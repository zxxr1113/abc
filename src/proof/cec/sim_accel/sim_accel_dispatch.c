/**CFile****************************************************************

  FileName    [sim_accel_dispatch.c]

  Synopsis    [CPUID detection, global backend selection, context alloc/free.]

***********************************************************************/

#include "sim_accel_internal.h"
#include <stdlib.h>
#include <string.h>

ABC_NAMESPACE_IMPL_START

/* Selected once at Sim_AccelGlobalInit(); read-only afterwards. */
const Sim_BackendOps_t * g_pSimAccelBackend = NULL;

/* ------------------------------------------------------------------ */
void Sim_AccelGlobalInit( void )
{
    const char *pEnv;

    if ( g_pSimAccelBackend != NULL )
        return; /* idempotent */

    /* Environment variable override */
    pEnv = getenv("ABC_SIM_BACKEND");
    if ( pEnv )
    {
        if ( strcmp(pEnv, "scalar32") == 0 ) { g_pSimAccelBackend = &g_BackendScalar32; return; }
        if ( strcmp(pEnv, "scalar64") == 0 ) { g_pSimAccelBackend = &g_BackendScalar64; return; }
#if defined(SIM_ACCEL_HAS_AVX2_BUILD)
        if ( strcmp(pEnv, "avx2")     == 0 )
        {
            __builtin_cpu_init();
            if ( __builtin_cpu_supports("avx2") )
                { g_pSimAccelBackend = &g_BackendAVX2; return; }
            Abc_Print( 0, "sim_accel: AVX2 requested but not supported; falling back to scalar64\n" );
        }
#endif
    }

    /* Auto-select: best available */
#if defined(SIM_ACCEL_HAS_AVX2_BUILD)
    __builtin_cpu_init();
    if ( __builtin_cpu_supports("avx2") )
        { g_pSimAccelBackend = &g_BackendAVX2; return; }
#endif
    g_pSimAccelBackend = &g_BackendScalar64;
}

/* ------------------------------------------------------------------ */
void Sim_AccelGlobalQuit( void )
{
    g_pSimAccelBackend = NULL;
}

/* ------------------------------------------------------------------ */
const char * Sim_AccelBackendName( void )
{
    if ( g_pSimAccelBackend == NULL )
        return "(uninitialised)";
    return g_pSimAccelBackend->name;
}

/* ------------------------------------------------------------------ */
Sim_AccelCtx_t * Sim_AccelCtxAlloc( int nWords32, Sim_BackendId_t override )
{
    Sim_AccelCtx_t *p;

    if ( g_pSimAccelBackend == NULL )
        Sim_AccelGlobalInit();

    p = ABC_CALLOC( Sim_AccelCtx_t, 1 );
    p->nWords32 = nWords32;
    p->ops      = ( override == SIM_BACKEND_AUTO )
                  ? g_pSimAccelBackend
                  : Sim_AccelGetOpsById(override);
    return p;
}

/* ------------------------------------------------------------------ */
void Sim_AccelCtxFree( Sim_AccelCtx_t * pCtx )
{
    if ( pCtx )
        ABC_FREE( pCtx );
}

/* ------------------------------------------------------------------ */
/* Public kernel entry points (thin wrappers that update stats)         */
/* ------------------------------------------------------------------ */

void Sim_AccelAndKernel( Sim_AccelCtx_t * pCtx,
                         unsigned       * pRes,
                         const unsigned * pRes0, int compl0,
                         const unsigned * pRes1, int compl1,
                         int nWords32 )
{
    if ( pCtx->fShadow )
    {
        unsigned shadow[SIM_SHADOW_CAPTURE_WORDS];
        int n = nWords32;
        if ( n > SIM_SHADOW_CAPTURE_WORDS ) n = SIM_SHADOW_CAPTURE_WORDS;
        int w;

        g_BackendScalar32.and_kernel( shadow, pRes0, compl0, pRes1, compl1, nWords32 );
        pCtx->ops->and_kernel( pRes, pRes0, compl0, pRes1, compl1, nWords32 );

        for ( w = 0; w < n; w++ )
        {
            if ( pRes[w] != shadow[w] && pCtx->nShadowMismatch == 0 )
            {
                Sim_ShadowCapture_t *sc = &pCtx->shadowFirst;
                memcpy(sc->in0,  pRes0,  n * 4);
                memcpy(sc->in1,  pRes1,  n * 4);
                memcpy(sc->fast, pRes,   n * 4);
                memcpy(sc->ref,  shadow, n * 4);
                sc->c0 = compl0; sc->c1 = compl1; sc->nWords32 = nWords32;
                sc->fMismatch = 1;
            }
            if ( pRes[w] != shadow[w] )
                pCtx->nShadowMismatch++;
        }
    }
    else
    {
        pCtx->ops->and_kernel( pRes, pRes0, compl0, pRes1, compl1, nWords32 );
    }

    pCtx->nKernelCalls++;
    pCtx->nGateBitsAnd += (uint64_t)nWords32 * 32;
}

void Sim_AccelCoKernel( Sim_AccelCtx_t * pCtx,
                        unsigned       * pResOut,
                        const unsigned * pResIn, int compl0,
                        int nWords32 )
{
    pCtx->ops->co_kernel( pResOut, pResIn, compl0, nWords32 );
    pCtx->nGateBitsCo += (uint64_t)nWords32 * 32;
}

/* ------------------------------------------------------------------ */
/* Shadow control                                                        */
/* ------------------------------------------------------------------ */
void Sim_AccelEnableShadow( Sim_AccelCtx_t * pCtx, int fEnable )
{
    pCtx->fShadow = fEnable;
}

int Sim_AccelShadowMismatchCount( const Sim_AccelCtx_t * pCtx )
{
    return pCtx->nShadowMismatch;
}

void Sim_AccelShadowDumpFirst( const Sim_AccelCtx_t * pCtx, FILE * fp )
{
    const Sim_ShadowCapture_t *sc = &pCtx->shadowFirst;
    int w;
    if ( !sc->fMismatch ) { fprintf(fp, "sim_accel shadow: no mismatch recorded\n"); return; }
    fprintf(fp, "=== sim_accel SHADOW MISMATCH (first occurrence) ===\n");
    fprintf(fp, "nWords32=%d  c0=%d  c1=%d\n", sc->nWords32, sc->c0, sc->c1);
    fprintf(fp, "w   in0        in1        fast       ref\n");
    for ( w = 0; w < sc->nWords32 && w < SIM_SHADOW_CAPTURE_WORDS; w++ )
        fprintf(fp, "%2d  %08x   %08x   %08x   %08x%s\n",
                w, sc->in0[w], sc->in1[w], sc->fast[w], sc->ref[w],
                (sc->fast[w] != sc->ref[w]) ? " <-- DIFF" : "");
}

ABC_NAMESPACE_IMPL_END
