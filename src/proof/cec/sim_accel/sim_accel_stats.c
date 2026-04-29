/**CFile****************************************************************

  FileName    [sim_accel_stats.c]

  Synopsis    [Statistics collection and report printing.]

***********************************************************************/

#include "sim_accel_internal.h"

ABC_NAMESPACE_IMPL_START

void Sim_AccelStatsRead( const Sim_AccelCtx_t * pCtx, Sim_AccelStats_t * pOut )
{
    pOut->backendUsed  = pCtx->ops->id;
    pOut->tKernel      = pCtx->tKernel;
    pOut->nGateBitsAnd = pCtx->nGateBitsAnd;
    pOut->nGateBitsCo  = pCtx->nGateBitsCo;
    pOut->nKernelCalls = pCtx->nKernelCalls;
}

void Sim_AccelStatsReset( Sim_AccelCtx_t * pCtx )
{
    pCtx->tKernel      = 0;
    pCtx->nGateBitsAnd = 0;
    pCtx->nGateBitsCo  = 0;
    pCtx->nKernelCalls = 0;
    pCtx->nShadowMismatch = 0;
}

void Sim_AccelStatsPrint( const Sim_AccelCtx_t * pCtx, FILE * fp,
                          const Sim_AccelStats_t * pBase )
{
    double tSec, gbps, speedup;
    uint64_t totalBits;

    if ( fp == NULL ) fp = stdout;

    tSec     = (double)pCtx->tKernel / (double)CLOCKS_PER_SEC;
    totalBits = pCtx->nGateBitsAnd + pCtx->nGateBitsCo;
    gbps     = (tSec > 1e-9) ? (double)totalBits / tSec / 1e9 : 0.0;

    fprintf(fp, "\n=== sim_accel report ===\n");
    fprintf(fp, "Backend       : %s\n", pCtx->ops->name);
    fprintf(fp, "nWords32      : %d (%d bits/node/call)\n",
            pCtx->nWords32, pCtx->nWords32 * 32);
    fprintf(fp, "Shadow check  : %s\n", pCtx->fShadow ? "enabled" : "disabled");
    if ( pCtx->fShadow )
        fprintf(fp, "Shadow mismatches: %d\n", pCtx->nShadowMismatch);
    fprintf(fp, "Kernel calls  : %llu\n",  (unsigned long long)pCtx->nKernelCalls);
    fprintf(fp, "AND gate-bits : %llu\n",  (unsigned long long)pCtx->nGateBitsAnd);
    fprintf(fp, "CO  gate-bits : %llu\n",  (unsigned long long)pCtx->nGateBitsCo);
    fprintf(fp, "Kernel time   : %.3f s\n", tSec);
    fprintf(fp, "Throughput    : %.3f Gbit/s\n", gbps);

    if ( pBase && pBase->tKernel > 0 )
    {
        double tBaseSec = (double)pBase->tKernel / (double)CLOCKS_PER_SEC;
        speedup = (tSec > 1e-9) ? tBaseSec / tSec : 0.0;
        fprintf(fp, "Speedup vs %-10s: %.2f×\n",
                (pBase->backendUsed == SIM_BACKEND_SCALAR32) ? "scalar32" :
                (pBase->backendUsed == SIM_BACKEND_SCALAR64) ? "scalar64" : "avx2",
                speedup);
    }
    fprintf(fp, "========================\n");
}

ABC_NAMESPACE_IMPL_END
