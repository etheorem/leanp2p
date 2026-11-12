/*
 * tls_shim.h: the two C entries that `net/tls` gives another shim.
 *
 * The QUIC transport (W4.4, etheorem/leanp2p#92) is to run its TLS 1.3 handshake
 * on the same `SSL_CTX` settings as the TLS-over-TCP engine of this
 * package (packages/net/tls/docs/ARCHITECTURE.md, "One context for
 * both transports"). Its Lean side hands its shim a `Tls.Context`
 * object, and these functions read the context and its ALPN list out
 * of it. The object keeps the context alive, so the pointers are valid
 * while the caller holds the object.
 */
#ifndef LEANP2P_TLS_SHIM_H
#define LEANP2P_TLS_SHIM_H

#include <lean/lean.h>
#include <openssl/ssl.h>

/* The `SSL_CTX` inside a `Tls.Context` object. Borrowed: the caller
   takes no reference to the context. */
SSL_CTX *leanp2p_tls_context_get(b_lean_obj_arg context);

/* The ALPN protocol list of the context, in the wire form that
   `SSL_set_alpn_protos` takes (one length byte, then the name). A
   client `SSL` sets it, as `leanp2p_tls_session_new` does. */
const unsigned char *leanp2p_tls_context_alpn(b_lean_obj_arg context, unsigned int *len);

#endif /* LEANP2P_TLS_SHIM_H */
