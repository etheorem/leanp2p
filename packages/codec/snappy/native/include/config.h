#ifndef THIRD_PARTY_SNAPPY_OPENSOURCE_CMAKE_CONFIG_H_
#define THIRD_PARTY_SNAPPY_OPENSOURCE_CMAKE_CONFIG_H_

/*
 * Feature macros for the vendored Snappy 1.3.1 sources.
 *
 * snappy-stubs-internal.h includes this file only when the translation
 * unit is compiled with -DHAVE_CONFIG_H. Phase 2C owns that compile.
 * This header does not record a compiled result.
 *
 * An instruction-set macro is 1 only when the compiler target already
 * defines the matching feature macro. The host CPU does not turn a
 * macro on. macOS arm64 and Ubuntu x86-64 therefore stay on their own
 * compiler defaults.
 */

#if defined(__GNUC__)
#define HAVE_ATTRIBUTE_ALWAYS_INLINE 1
#define HAVE_BUILTIN_CTZ 1
#define HAVE_BUILTIN_EXPECT 1
#define HAVE_BUILTIN_PREFETCH 1
#else
#define HAVE_ATTRIBUTE_ALWAYS_INLINE 0
#define HAVE_BUILTIN_CTZ 0
#define HAVE_BUILTIN_EXPECT 0
#define HAVE_BUILTIN_PREFETCH 0
#endif

#if defined(__APPLE__) || defined(__linux__)
#define HAVE_SYS_MMAN_H 1
#define HAVE_UNISTD_H 1
#else
#define HAVE_SYS_MMAN_H 0
#define HAVE_UNISTD_H 0
#endif

#if defined(__SSSE3__)
#define SNAPPY_HAVE_SSSE3 1
#else
#define SNAPPY_HAVE_SSSE3 0
#endif

#if defined(__SSE4_2__)
#define SNAPPY_HAVE_X86_CRC32 1
#else
#define SNAPPY_HAVE_X86_CRC32 0
#endif

#if defined(__BMI2__)
#define SNAPPY_HAVE_BMI2 1
#else
#define SNAPPY_HAVE_BMI2 0
#endif

#if defined(__ARM_NEON) || defined(__ARM_NEON__)
#define SNAPPY_HAVE_NEON 1
#else
#define SNAPPY_HAVE_NEON 0
#endif

/* The supported builds are not RISC-V. */
#define SNAPPY_RVV_1 0
#define SNAPPY_RVV_0_7 0

/*
 * NEON and CRC32 are separate compiler features. Enable the CRC path
 * only when the compiler defines both. A NEON target without
 * __ARM_FEATURE_CRC32 keeps the portable path.
 */
#if SNAPPY_HAVE_NEON && defined(__ARM_FEATURE_CRC32)
#define SNAPPY_HAVE_NEON_CRC32 1
#else
#define SNAPPY_HAVE_NEON_CRC32 0
#endif

#if defined(__BYTE_ORDER__) && defined(__ORDER_BIG_ENDIAN__) && \
    (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__)
#define SNAPPY_IS_BIG_ENDIAN 1
#else
#define SNAPPY_IS_BIG_ENDIAN 0
#endif

#endif  // THIRD_PARTY_SNAPPY_OPENSOURCE_CMAKE_CONFIG_H_
