#include "sim_accel_internal.h"

#define SIM_BACKEND         scalar32
#define SIM_BACKEND_SCALAR32
#include "sim_accel_macros.h"
#include "sim_accel_kernel.inc"
#undef SIM_BACKEND_SCALAR32
#undef SIM_BACKEND

ABC_NAMESPACE_IMPL_START

Sim_BackendOps_t g_BackendScalar32 = {
    Sim_Kernel_AndNode_scalar32,
    Sim_Kernel_CoNode_scalar32,
    0, /* SIM_BACKEND_SCALAR32 */
    "scalar32"
};

ABC_NAMESPACE_IMPL_END
