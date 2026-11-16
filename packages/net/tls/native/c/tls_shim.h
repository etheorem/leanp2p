/*
 * tls_shim.h: the five C entries that `net/tls` gives another shim.
 *
 * The QUIC shim of `net/quic` runs its TLS 1.3 handshake on the same
 * `SSL_CTX` settings as the TLS-over-TCP engine of this package
 * (packages/net/tls/docs/ARCHITECTURE.md, "One context for both
 * transports"). Its Lean side hands it a `Tls.Context` object, and the
 * first two functions read the context and its ALPN list out of that
 * object. The object keeps the context alive, so the pointers are valid
 * while the caller holds the object.
 *
 * The context's verify callback runs the caller's certificate check of
 * each `SSL`, and an `SSL` with no check refuses every certificate. So
 * the other shim attaches its check to each `SSL` it makes from the
 * context. After a failed handshake step it asks whether the step
 * refused the peer's certificate, and reads the reason back.
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

/* Attach the caller's certificate check, a pure Lean
   `ByteArray → Option String`, to an `SSL` made from the context. The
   verify callback runs it on the DER of the peer's one certificate:
   `none` accepts, and `some reason` refuses with the alert
   `bad_certificate`. The `SSL` takes one reference to `check` and drops
   it in `SSL_free`. Borrowed `check`. Attach once per `SSL`. 1 on
   success, 0 on a failure, after which the `SSL` refuses every
   certificate. */
int leanp2p_tls_attach_check(SSL *ssl, b_lean_obj_arg check);

/* The reason of the last refusal by the check of `ssl`: the check's own
   text, or the chain rule's. Empty when there was none. Valid until the
   next handshake step on `ssl` or its `SSL_free`. */
const char *leanp2p_tls_refusal(const SSL *ssl);

/* True when the failed handshake step of `ssl` refused the peer's
   certificate: the check or the chain rule refused it, or a client sent
   none to a server. The answer reads the thread's OpenSSL error queue,
   so the caller asks before it clears the queue. */
int leanp2p_tls_refused(const SSL *ssl);

#endif /* LEANP2P_TLS_SHIM_H */
