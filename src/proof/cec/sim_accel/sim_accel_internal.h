/**CFile****************************************************************

  FileName    [sim_accel_internal.h]

  Synopsis    [Internal data structures — not exposed to cecClass.c etc.]

***********************************************************************/

#ifndef ABC__proof__cec__sim_accel__sim_accel_internal_h
#define ABC__proof__cec__sim_accel__sim_accel_internal_h

#include "sim_accel.h"
#include <string.h>

ABC_NAMESPACE_HEADER_START

/* ------------------------------------------------------------------ */
/* Backend ops table (function pointer dispatch)                        */
/* ------------------------------------------------------------------ */
typedef struct {
    void (*and_kernel)( unsigned       * pRes,
                        const unsigned * p0, int c0,
                        const unsigned * p1, int c1,
                        int nWords32 );
    void (*co_kernel) ( unsigned       * pOut,
                        const unsigned * pIn, int c0,
                        int nWords32 );
    Sim_BackendId_t  id;
    const char      *name;
} Sim_BackendOps_t;

/* Declared in sim_accel_scalar32.c / scalar64.c / avx2.c */
extern Sim_BackendOps_t g_BackendScalar32;
extern Sim_BackendOps_t g_BackendScalar64;
#if defined(SIM_ACCEL_HAS_AVX2_BUILD)
extern Sim_BackendOps_t g_BackendAVX2;
#endif

/* Selected at Sim_AccelGlobalInit() */
extern const Sim_BackendOps_t * g_pSimAccelBackend;

/* ------------------------------------------------------------------ */
/* Shadow verification state                                            */
/* ------------------------------------------------------------------ */
#define SIM_SHADOW_CAPTURE_WORDS  64   /* enough for nWords32 <= 64    */

typedef struct {
    int      fMismatch;
    unsigned in0 [SIM_SHADOW_CAPTURE_WORDS];
    unsigned in1 [SIM_SHADOW_CAPTURE_WORDS];
    unsigned fast[SIM_SHADOW_CAPTURE_WORDS];
    unsigned ref [SIM_SHADOW_CAPTURE_WORDS];
    int      c0, c1, nWords32;
} Sim_ShadowCapture_t;

/* ------------------------------------------------------------------ */
/* Per-context struct                                                    */
/* ------------------------------------------------------------------ */
struct Sim_AccelCtx_t_ {
    const Sim_BackendOps_t * ops;
    int                      nWords32;

    /* shadow check */
    int                      fShadow;
    int                      nShadowMismatch;
    Sim_ShadowCapture_t      shadowFirst;

    /* stats */
    abctime                  tKernelStart;   /* used for per-call sampling */
    abctime                  tKernel;
    uint64_t                 nGateBitsAnd;
    uint64_t                 nGateBitsCo;
    uint64_t                 nKernelCalls;
};

/* ------------------------------------------------------------------ */
/* Helper: select backend by id                                         */
/* ------------------------------------------------------------------ */
static inline const Sim_BackendOps_t * Sim_AccelGetOpsById( Sim_BackendId_t id )
{
    switch (id)
    {
        case SIM_BACKEND_SCALAR64: return &g_BackendScalar64;
#if defined(SIM_ACCEL_HAS_AVX2_BUILD)
        case SIM_BACKEND_AVX2:     return &g_BackendAVX2;
#endif
        default:                   return &g_BackendScalar32;
    }
}

ABC_NAMESPACE_HEADER_END

#endif /* sim_accel_internal.h */
