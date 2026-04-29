#include "sim_accel_internal.h"

#define SIM_BACKEND         scalar64
#define SIM_BACKEND_SCALAR64
#include "sim_accel_macros.h"
#include "sim_accel_kernel.inc"
#undef SIM_BACKEND_SCALAR64
#undef SIM_BACKEND

ABC_NAMESPACE_IMPL_START

Sim_BackendOps_t g_BackendScalar64 = {
    Sim_Kernel_AndNode_scalar64,
    Sim_Kernel_CoNode_scalar64,
    1, /* SIM_BACKEND_SCALAR64 */
    "scalar64"
};

ABC_NAMESPACE_IMPL_END
