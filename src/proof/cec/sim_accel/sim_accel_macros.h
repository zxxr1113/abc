/**CFile****************************************************************

  FileName    [sim_accel_macros.h]

  Synopsis    [Backend selection macros — included by each backend .c after
               defining exactly one of:
                 SIM_BACKEND_SCALAR32
                 SIM_BACKEND_SCALAR64
                 SIM_BACKEND_AVX2
               and setting SIM_BACKEND to the token used as suffix.]

***********************************************************************/

/* ------------------------------------------------------------------ */
/* AVX2 backend                                                         */
/* ------------------------------------------------------------------ */
#if defined(SIM_BACKEND_AVX2)

  #include <immintrin.h>
  typedef __m256i Sim_Vec_t;
  #define SIM_VEC_BYTES       32
  #define SIM_VEC_BITS        256
  #define SIM_BACKEND_NAME    "avx2"
  #define SIM_BACKEND_ID_VAL  2

  #define SIM_VLOAD(p32)          _mm256_loadu_si256((const __m256i*)(p32))
  #define SIM_VSTORE(p32,v)       _mm256_storeu_si256((__m256i*)(p32),(v))
  #define SIM_VAND(a,b)           _mm256_and_si256((a),(b))
  #define SIM_VOR(a,b)            _mm256_or_si256((a),(b))
  #define SIM_VXOR(a,b)           _mm256_xor_si256((a),(b))
  #define SIM_VNOT(a)             _mm256_xor_si256((a), _mm256_set1_epi64x((long long)~0ULL))
  #define SIM_VBCAST_ZERO()       _mm256_setzero_si256()
  #define SIM_VBCAST_ONES()       _mm256_set1_epi64x((long long)~0ULL)
  #define SIM_VBCAST_FROM_BIT(b)  ((b) ? SIM_VBCAST_ONES() : SIM_VBCAST_ZERO())

/* ------------------------------------------------------------------ */
/* scalar64 backend                                                     */
/* ------------------------------------------------------------------ */
#elif defined(SIM_BACKEND_SCALAR64)

  typedef uint64_t Sim_Vec_t;
  #define SIM_VEC_BYTES       8
  #define SIM_VEC_BITS        64
  #define SIM_BACKEND_NAME    "scalar64"
  #define SIM_BACKEND_ID_VAL  1

  /* Use memcpy for strict-aliasing safety; compiler optimises to mov. */
  static inline uint64_t Sim__ld64(const void *p) {
      uint64_t v; memcpy(&v, p, 8); return v;
  }
  static inline void Sim__st64(void *p, uint64_t v) {
      memcpy(p, &v, 8);
  }
  #define SIM_VLOAD(p32)          Sim__ld64((const void*)(p32))
  #define SIM_VSTORE(p32,v)       Sim__st64((void*)(p32),(v))
  #define SIM_VAND(a,b)           ((a)&(b))
  #define SIM_VOR(a,b)            ((a)|(b))
  #define SIM_VXOR(a,b)           ((a)^(b))
  #define SIM_VNOT(a)             (~(a))
  #define SIM_VBCAST_ZERO()       ((uint64_t)0)
  #define SIM_VBCAST_ONES()       (~(uint64_t)0)
  #define SIM_VBCAST_FROM_BIT(b)  ((b) ? ~(uint64_t)0 : (uint64_t)0)

/* ------------------------------------------------------------------ */
/* scalar32 backend (baseline, identical to original cecClass.c logic) */
/* ------------------------------------------------------------------ */
#elif defined(SIM_BACKEND_SCALAR32)

  typedef uint32_t Sim_Vec_t;
  #define SIM_VEC_BYTES       4
  #define SIM_VEC_BITS        32
  #define SIM_BACKEND_NAME    "scalar32"
  #define SIM_BACKEND_ID_VAL  0

  static inline uint32_t Sim__ld32(const void *p) {
      uint32_t v; memcpy(&v, p, 4); return v;
  }
  static inline void Sim__st32(void *p, uint32_t v) {
      memcpy(p, &v, 4);
  }
  #define SIM_VLOAD(p32)          Sim__ld32((const void*)(p32))
  #define SIM_VSTORE(p32,v)       Sim__st32((void*)(p32),(v))
  #define SIM_VAND(a,b)           ((uint32_t)((a)&(b)))
  #define SIM_VOR(a,b)            ((uint32_t)((a)|(b)))
  #define SIM_VXOR(a,b)           ((uint32_t)((a)^(b)))
  #define SIM_VNOT(a)             ((uint32_t)(~(a)))
  #define SIM_VBCAST_ZERO()       ((uint32_t)0)
  #define SIM_VBCAST_ONES()       ((uint32_t)~0u)
  #define SIM_VBCAST_FROM_BIT(b)  ((b) ? (uint32_t)~0u : (uint32_t)0)

#else
  #error "sim_accel_macros.h: define SIM_BACKEND_SCALAR32 / SCALAR64 / AVX2 before including"
#endif

/* ------------------------------------------------------------------ */
/* Derived: vec-count and tail from nWords32                            */
/* ------------------------------------------------------------------ */
#define SIM_NVEC(nWords32)       ( ((nWords32) * 4) / SIM_VEC_BYTES )
#define SIM_TAIL_BYTES(nWords32) ( ((nWords32) * 4) % SIM_VEC_BYTES )
#define SIM_VEC_WORDS32          ( SIM_VEC_BYTES / 4 )
