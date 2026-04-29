/**CFile****************************************************************

  FileName    [sim_accel.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Simulation acceleration layer for CEC/scorr.]

  Synopsis    [Public API — the only header cecClass.c / cecMan.c need to include.]

***********************************************************************/

#ifndef ABC__proof__cec__sim_accel__sim_accel_h
#define ABC__proof__cec__sim_accel__sim_accel_h

#include <stdio.h>
#include <stdint.h>
#include "misc/util/abc_global.h"

ABC_NAMESPACE_HEADER_START

/* ------------------------------------------------------------------ */
/* Backend identifiers                                                  */
/* ------------------------------------------------------------------ */
typedef enum {
    SIM_BACKEND_AUTO     = -1,  /* CPUID / env auto-select            */
    SIM_BACKEND_SCALAR32 =  0,  /* original uint32 path               */
    SIM_BACKEND_SCALAR64 =  1,  /* 2× free widening via uint64        */
    SIM_BACKEND_AVX2     =  2,  /* 256-bit AVX2                       */
} Sim_BackendId_t;

/* ------------------------------------------------------------------ */
/* Opaque context (one per Cec_ManSim_t)                               */
/* ------------------------------------------------------------------ */
typedef struct Sim_AccelCtx_t_ Sim_AccelCtx_t;

/* ------------------------------------------------------------------ */
/* Global init / teardown  (call once at program start / end)          */
/* ------------------------------------------------------------------ */
void  Sim_AccelGlobalInit ( void );
void  Sim_AccelGlobalQuit ( void );

/* Returns the name of the currently selected backend. */
const char * Sim_AccelBackendName ( void );

/* ------------------------------------------------------------------ */
/* Per-manager context                                                  */
/* ------------------------------------------------------------------ */
Sim_AccelCtx_t * Sim_AccelCtxAlloc ( int nWords32, Sim_BackendId_t override );
void             Sim_AccelCtxFree  ( Sim_AccelCtx_t * pCtx );

/* ------------------------------------------------------------------ */
/* Inner kernels called from cecClass.c                                 */
/*                                                                      */
/* AND node:                                                            */
/*   pRes[0..nWords32-1] = (pRes0 ^ compl0_mask) & (pRes1 ^ compl1_mask) */
/*                                                                      */
/* CO output kernel (copy-with-optional-invert from fanin to output):  */
/*   pResOut[0..nWords32-1] = compl0 ? ~pResIn[0..] : pResIn[0..]     */
/* ------------------------------------------------------------------ */
/* nWords32 must be p->nWords (which changes during ClassesPrepare). */
void Sim_AccelAndKernel ( Sim_AccelCtx_t * pCtx,
                          unsigned       * pRes,
                          const unsigned * pRes0, int compl0,
                          const unsigned * pRes1, int compl1,
                          int nWords32 );

void Sim_AccelCoKernel  ( Sim_AccelCtx_t * pCtx,
                          unsigned       * pResOut,
                          const unsigned * pResIn, int compl0,
                          int nWords32 );

/* ------------------------------------------------------------------ */
/* Shadow (correctness) verification                                    */
/* ------------------------------------------------------------------ */
void Sim_AccelEnableShadow       ( Sim_AccelCtx_t * pCtx, int fEnable );
int  Sim_AccelShadowMismatchCount( const Sim_AccelCtx_t * pCtx );
void Sim_AccelShadowDumpFirst    ( const Sim_AccelCtx_t * pCtx, FILE * fp );

/* ------------------------------------------------------------------ */
/* Statistics                                                           */
/* ------------------------------------------------------------------ */
typedef struct {
    Sim_BackendId_t backendUsed;
    abctime         tKernel;         /* cumulative AND+CO kernel time  */
    uint64_t        nGateBitsAnd;    /* AND gate-bits processed        */
    uint64_t        nGateBitsCo;
    uint64_t        nKernelCalls;
} Sim_AccelStats_t;

void Sim_AccelStatsRead  ( const Sim_AccelCtx_t * pCtx, Sim_AccelStats_t * pOut );
void Sim_AccelStatsReset ( Sim_AccelCtx_t * pCtx );
void Sim_AccelStatsPrint ( const Sim_AccelCtx_t * pCtx, FILE * fp,
                           const Sim_AccelStats_t * pBaseline );

ABC_NAMESPACE_HEADER_END

#endif /* sim_accel.h */
