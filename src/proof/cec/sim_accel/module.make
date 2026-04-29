SRC += src/proof/cec/sim_accel/sim_accel_dispatch.c \
       src/proof/cec/sim_accel/sim_accel_stats.c    \
       src/proof/cec/sim_accel/sim_accel_scalar32.c \
       src/proof/cec/sim_accel/sim_accel_scalar64.c

# AVX2 backend: optional, enabled by default on x86_64.
# Disable with: make ABC_NO_AVX=1
ifndef ABC_NO_AVX
  ifneq ($(filter x86_64 amd64,$(shell uname -m)),)
    SRC    += src/proof/cec/sim_accel/sim_accel_avx2.c
    CFLAGS += -DSIM_ACCEL_HAS_AVX2_BUILD
    # NOTE: -mavx2 is NOT set globally; sim_accel_avx2.c uses
    #       #pragma GCC target("avx2") to enable it locally only.
  endif
endif
