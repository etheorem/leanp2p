/* The build-support configuration header of the pinned ngtcp2. It is no
   upstream source. CMake writes `config.h` from `cmakeconfig.h.in` after
   it probes the system. This file answers the same probes with
   `__has_include`, so the Lake build needs no configure step. Every
   macro below is one the pinned sources test; they test no other
   `HAVE_` macro (packages/net/quic/docs/ARCHITECTURE.md, "The native
   build"). */
#ifndef LEANP2P_NGTCP2_CONFIG_H
#define LEANP2P_NGTCP2_CONFIG_H

#if __has_include(<arpa/inet.h>)
#  define HAVE_ARPA_INET_H 1
#endif
#if __has_include(<netinet/in.h>)
#  define HAVE_NETINET_IN_H 1
#endif
#if __has_include(<unistd.h>)
#  define HAVE_UNISTD_H 1
#endif
#if __has_include(<byteswap.h>)
#  define HAVE_BYTESWAP_H 1
#  define HAVE_DECL_BSWAP_64 1
#else
#  define HAVE_DECL_BSWAP_64 0
#endif
#if __has_include(<endian.h>)
#  define HAVE_ENDIAN_H 1
#  define HAVE_DECL_BE64TOH 1
#elif __has_include(<sys/endian.h>)
#  define HAVE_SYS_ENDIAN_H 1
#  define HAVE_DECL_BE64TOH 1
#else
#  define HAVE_DECL_BE64TOH 0
#endif
/* HAVE_EXPLICIT_BZERO and HAVE_MEMSET_S stay unset: `__has_include`
   cannot see a function, and `ngtcp2_secure_clear` then clears through
   a volatile `memset` pointer, which the compiler cannot drop. */

#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#  define WORDS_BIGENDIAN 1
#endif

#endif /* LEANP2P_NGTCP2_CONFIG_H */
