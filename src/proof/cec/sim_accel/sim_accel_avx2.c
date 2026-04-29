/* AVX2 backend — the #pragma target is scoped to this TU only.
   The rest of the ABC binary is NOT compiled with -mavx2.
   Runtime CPUID guard ensures these functions are only called on
   machines that actually support AVX2. */

#pragma GCC push_options
#pragma GCC target("avx2")

#include "sim_accel_internal.h"

#define SIM_BACKEND         avx2
#define SIM_BACKEND_AVX2
#include "sim_accel_macros.h"
#include "sim_accel_kernel.inc"
#undef SIM_BACKEND_AVX2
#undef SIM_BACKEND

#pragma GCC pop_options

ABC_NAMESPACE_IMPL_START

Sim_BackendOps_t g_BackendAVX2 = {
    Sim_Kernel_AndNode_avx2,
    Sim_Kernel_CoNode_avx2,
    2, /* SIM_BACKEND_AVX2 */
    "avx2"
};

ABC_NAMESPACE_IMPL_END
