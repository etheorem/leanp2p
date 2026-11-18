/*
 * tls_shim.c: the OpenSSL 3 libssl shim behind `net/tls`.
 *
 * The shim runs a TLS 1.3 endpoint over two memory BIOs. The Lean side
 * moves the bytes: it feeds what the connection read into the input
 * BIO, and it writes what the output BIO holds to the connection. So
 * the shim opens no socket, starts no thread, and reads no clock
 * (packages/net/tls/docs/ARCHITECTURE.md, "The engine"). The
 * conventions, binding for every function below:
 *
 * - Every exported symbol carries the `leanp2p_tls_` prefix. Exactly
 *   one `@[extern]` declaration in `TlsNative.lean` reaches it, apart
 *   from the five entries of `tls_shim.h`, which another shim calls.
 * - The shim borrows every argument (`b_lean_obj_arg`), the session
 *   and the context objects included.
 * - One mutex guards each session. libssl allows one thread on an
 *   `SSL` at a time, and the Lean reader and the Lean writer of one
 *   connection run on two tasks. Each call takes the lock for its
 *   whole length, so the output BIO stays in the order the calls
 *   produced it.
 * - A session holds a reference to its context object, so the
 *   `SSL_CTX` outlives every `SSL` made from it.
 * - The certificate check runs inside the handshake, in libssl's verify
 *   callback. The callback enforces the one rule the caller cannot see,
 *   that the peer sent exactly one certificate, and then hands that
 *   certificate to the caller's check, a Lean closure that the `SSL`
 *   holds in its ex_data. Every `SSL` of the context needs one: a
 *   session attaches its own, and another shim attaches one to its own
 *   `SSL` through `tls_shim.h`. A refusal of either kind fails the
 *   handshake with
 *   `X509_V_ERR_CERT_REJECTED`, which libssl sends as the alert
 *   `bad_certificate` (`ssl_x509err2alert`), as Go's `crypto/tls`
 *   sends it when `VerifyPeerCertificate` fails.
 */

#include <lean/lean.h>

#include <limits.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <openssl/err.h>
#include <openssl/ssl.h>
#include <openssl/x509.h>

#include "tls_shim.h"

/* ------------------------------------------------------------------ */
/* Lean object helpers                                                 */
/* ------------------------------------------------------------------ */

static lean_object *mk_bytes(const uint8_t *p, size_t n) {
    lean_object *r = lean_alloc_sarray(1, n, n);
    if (n > 0) memcpy(lean_sarray_cptr(r), p, n);
    return r;
}

static lean_object *none(void) { return lean_box(0); }

static lean_object *some(lean_object *v) {
    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, v);
    return r;
}

/* ------------------------------------------------------------------ */
/* The context                                                         */
/* ------------------------------------------------------------------ */

typedef struct {
    SSL_CTX *ctx;
    /* The ALPN list in wire form: one length byte, then the name. */
    unsigned char alpn[256];
    unsigned int alpn_len;
} tls_context;

static void context_finalize(void *p) {
    tls_context *c = p;
    SSL_CTX_free(c->ctx);
    free(c);
}

static void noop_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; }

static lean_external_class *context_class;
static lean_external_class *session_class;
static void session_finalize(void *p);

/* The caller's certificate check of one `SSL`, and the reason of its
   last refusal. The `SSL` owns it through its ex_data slot. */
typedef struct {
    /* A pure `ByteArray → Option String`: one reference. */
    lean_object *check;
    /* The reason the check gave for its refusal; empty when it gave
       none. */
    char refusal[256];
} peer_check;

/* The free callback of the ex_data slot. libssl calls it from
   `SSL_free` (`CRYPTO_free_ex_data`) with the slot's value, which is
   NULL when no check was attached. */
static void free_peer_check(void *parent, void *ptr, CRYPTO_EX_DATA *ad, int idx, long argl,
                            void *argp) {
    (void)parent;
    (void)ad;
    (void)idx;
    (void)argl;
    (void)argp;
    peer_check *pc = ptr;
    if (pc == NULL) return;
    lean_dec(pc->check);
    free(pc);
}

/* The `SSL` ex_data slot that holds the `peer_check`, so the verify
   callback finds the check from the store it gets. */
static int check_index = -1;

static void register_classes(void) {
    context_class = lean_register_external_class(context_finalize, noop_foreach);
    session_class = lean_register_external_class(session_finalize, noop_foreach);
    check_index = SSL_get_ex_new_index(0, NULL, NULL, NULL, free_peer_check);
}

static pthread_once_t classes_once = PTHREAD_ONCE_INIT;

static tls_context *context_of(b_lean_obj_arg o) { return lean_get_external_data(o); }

SSL_CTX *leanp2p_tls_context_get(b_lean_obj_arg context) { return context_of(context)->ctx; }

const unsigned char *leanp2p_tls_context_alpn(b_lean_obj_arg context, unsigned int *len) {
    tls_context *c = context_of(context);
    *len = c->alpn_len;
    return c->alpn;
}

/* The verify callback; it needs the session struct, below. */
static int verify_peer(X509_STORE_CTX *store, void *arg);

/* The server takes the context's protocol when the client offers it,
   and refuses the handshake when the client does not. */
static int select_alpn(SSL *ssl, const unsigned char **out, unsigned char *outlen,
                       const unsigned char *in, unsigned int inlen, void *arg) {
    (void)ssl;
    tls_context *c = arg;
    unsigned char *selected = NULL;
    if (SSL_select_next_proto(&selected, outlen, c->alpn, c->alpn_len, in, inlen)
        != OPENSSL_NPN_NEGOTIATED)
        return SSL_TLSEXT_ERR_ALERT_FATAL;
    *out = selected;
    return SSL_TLSEXT_ERR_OK;
}

/* A context for one certificate and its key, both DER. TLS 1.3 only,
   no session tickets and no session cache, the context's ALPN, and the
   one-certificate rule. `none` when the certificate or the key does not
   load, when they do not match, or when the ALPN name is empty or
   longer than 255 bytes. */
LEAN_EXPORT lean_obj_res leanp2p_tls_context_new(b_lean_obj_arg cert, b_lean_obj_arg key,
                                                 b_lean_obj_arg alpn) {
    pthread_once(&classes_once, register_classes);
    size_t alpn_len = lean_string_size(alpn) - 1;
    const unsigned char *cp = lean_sarray_cptr(cert);
    const unsigned char *kp = lean_sarray_cptr(key);
    X509 *x = d2i_X509(NULL, &cp, (long)lean_sarray_size(cert));
    EVP_PKEY *k = d2i_AutoPrivateKey(NULL, &kp, (long)lean_sarray_size(key));
    tls_context *c = calloc(1, sizeof *c);
    SSL_CTX *ctx = SSL_CTX_new(TLS_method());
    int ok = x != NULL && k != NULL && c != NULL && ctx != NULL && alpn_len > 0
        && alpn_len <= 255
        && SSL_CTX_set_min_proto_version(ctx, TLS1_3_VERSION) == 1
        && SSL_CTX_set_max_proto_version(ctx, TLS1_3_VERSION) == 1
        && SSL_CTX_set_num_tickets(ctx, 0) == 1
        && SSL_CTX_use_certificate(ctx, x) == 1
        && SSL_CTX_use_PrivateKey(ctx, k) == 1
        && SSL_CTX_check_private_key(ctx) == 1;
    X509_free(x);
    EVP_PKEY_free(k);
    if (!ok) {
        SSL_CTX_free(ctx);
        free(c);
        ERR_clear_error();
        return lean_io_result_mk_ok(none());
    }
    SSL_CTX_set_options(ctx, SSL_OP_NO_TICKET);
    /* Middlebox compatibility mode (RFC 8446 Appendix D.4, optional) is a
       libssl default. In it the client keeps its write side in plaintext
       until its second flight (statem_clnt.c, the change of
       SSL3_CHANGE_CIPHER_CLIENT_WRITE), so the alert of a refused server
       certificate goes out unencrypted, and Go's server, which reads the
       client handshake key from ServerHello on, cannot read it. With the
       mode off the client installs that key at ServerHello. */
    SSL_CTX_clear_options(ctx, SSL_OP_ENABLE_MIDDLEBOX_COMPAT);
    SSL_CTX_set_session_cache_mode(ctx, SSL_SESS_CACHE_OFF);
    SSL_CTX_set_cert_verify_callback(ctx, verify_peer, NULL);
    c->ctx = ctx;
    c->alpn[0] = (unsigned char)alpn_len;
    memcpy(c->alpn + 1, lean_string_cstr(alpn), alpn_len);
    c->alpn_len = (unsigned int)alpn_len + 1;
    SSL_CTX_set_alpn_select_cb(ctx, select_alpn, c);
    return lean_io_result_mk_ok(some(lean_alloc_external(context_class, c)));
}

/* Append a certificate (DER) to the chain the context sends after its
   own certificate. A context that holds one sends a chain of two, which
   the peer's one-certificate rule refuses; the suite checks that rule
   with it. 1 on success. */
LEAN_EXPORT lean_obj_res leanp2p_tls_context_add_chain(b_lean_obj_arg context,
                                                       b_lean_obj_arg cert) {
    const unsigned char *cp = lean_sarray_cptr(cert);
    X509 *x = d2i_X509(NULL, &cp, (long)lean_sarray_size(cert));
    int ok = x != NULL && SSL_CTX_add1_chain_cert(context_of(context)->ctx, x) == 1;
    X509_free(x);
    ERR_clear_error();
    return lean_io_result_mk_ok(lean_box(ok));
}

/* ------------------------------------------------------------------ */
/* The session                                                         */
/* ------------------------------------------------------------------ */

typedef struct {
    SSL *ssl;
    BIO *rbio; /* the bytes the peer sent, fed by the Lean side */
    BIO *wbio; /* the bytes for the peer, drained by the Lean side */
    pthread_mutex_t mu;
    lean_object *context; /* one reference, so the SSL_CTX outlives us */
    char error[256];
} tls_session;

static void session_finalize(void *p) {
    tls_session *s = p;
    SSL_free(s->ssl); /* frees both BIOs and the check (`free_peer_check`) */
    pthread_mutex_destroy(&s->mu);
    lean_dec(s->context);
    free(s);
}

static tls_session *session_of(b_lean_obj_arg o) { return lean_get_external_data(o); }

/* The verify callback, which libssl calls in place of its own chain
   verification (`ssl_verify_internal`). The store's untrusted stack is
   the chain the peer sent, its own certificate first, so a chain of
   one has one entry. The callback then runs the caller's check on that
   certificate's DER. The check is a pure Lean function, so the call
   is `lean_apply_1` and its answer is an `Option String` object:
   `none` is `lean_box(0)`, and `some` is constructor 1 with the reason
   in field 0. The callback keeps the reason in the `peer_check`, for
   `leanp2p_tls_refusal`. An `SSL` with no check attached refuses every
   certificate, fail-closed. libssl sets `verify_result` from the
   store's error, so a refusal is `X509_V_ERR_CERT_REJECTED` there, and
   the alert is `bad_certificate`. */
static int verify_peer(X509_STORE_CTX *store, void *arg) {
    (void)arg;
    X509 *leaf = X509_STORE_CTX_get0_cert(store);
    STACK_OF(X509) *chain = X509_STORE_CTX_get0_untrusted(store);
    SSL *ssl = X509_STORE_CTX_get_ex_data(store, SSL_get_ex_data_X509_STORE_CTX_idx());
    peer_check *pc = ssl != NULL ? SSL_get_ex_data(ssl, check_index) : NULL;
    unsigned char *der = NULL;
    int n = -1;
    if (leaf != NULL && chain != NULL && sk_X509_num(chain) == 1 && pc != NULL)
        n = i2d_X509(leaf, &der);
    int ok = 0;
    if (n > 0) {
        lean_object *bytes = mk_bytes(der, (size_t)n);
        /* `lean_apply_1` consumes the closure and its argument. */
        lean_inc(pc->check);
        lean_object *r = lean_apply_1(pc->check, bytes);
        if (lean_is_scalar(r)) {
            ok = 1;
        } else {
            snprintf(pc->refusal, sizeof pc->refusal, "%s", lean_string_cstr(lean_ctor_get(r, 0)));
        }
        lean_dec(r);
    }
    else if (pc != NULL && chain != NULL && sk_X509_num(chain) != 1)
        snprintf(pc->refusal, sizeof pc->refusal,
                 "the peer sent %d certificates, and the TLS spec allows one",
                 sk_X509_num(chain));
    OPENSSL_free(der);
    if (!ok) X509_STORE_CTX_set_error(store, X509_V_ERR_CERT_REJECTED);
    return ok;
}

/* Attach the caller's check to an `SSL` made from a `Tls.Context`, so the
   verify callback runs it on the peer's certificate. The `SSL` takes one
   reference to `check` and drops it in `SSL_free`. The caller attaches
   once per `SSL`: `SSL_set_ex_data` replaces a value without freeing
   it. 1 on success, 0 when an allocation or the slot failed; the `SSL`
   then holds no check and refuses every certificate. */
int leanp2p_tls_attach_check(SSL *ssl, b_lean_obj_arg check) {
    pthread_once(&classes_once, register_classes);
    peer_check *pc = calloc(1, sizeof *pc);
    if (pc == NULL) return 0;
    lean_inc(check);
    pc->check = check;
    if (SSL_set_ex_data(ssl, check_index, pc) != 1) {
        lean_dec(check);
        free(pc);
        ERR_clear_error();
        return 0;
    }
    return 1;
}

/* The reason of the last refusal by the `SSL`'s check; empty when it
   gave none, or when no check is attached. Valid until the next
   handshake step or `SSL_free`. */
const char *leanp2p_tls_refusal(const SSL *ssl) {
    const peer_check *pc = SSL_get_ex_data(ssl, check_index);
    return pc != NULL ? pc->refusal : "";
}

/* Keep the first error of the thread's queue as the session's error
   text, and clear the queue. */
static void keep_error(tls_session *s, const char *fallback) {
    unsigned long e = ERR_get_error();
    if (e != 0)
        ERR_error_string_n(e, s->error, sizeof s->error);
    else
        snprintf(s->error, sizeof s->error, "%s", fallback);
    ERR_clear_error();
}

/* A session on `context`, as the server (`server` = 1) or the client.
   The server requires a client certificate. The client sends the ALPN
   list and no server name: the TLS spec of the caller forbids a value
   in SNI. `check` is the caller's certificate check, a pure
   `ByteArray → Option String`, which the verify callback runs. `none`
   on a library fault. */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_new(b_lean_obj_arg context, uint8_t server,
                                                 b_lean_obj_arg check) {
    tls_context *c = context_of(context);
    tls_session *s = calloc(1, sizeof *s);
    SSL *ssl = SSL_new(c->ctx);
    BIO *rbio = BIO_new(BIO_s_mem());
    BIO *wbio = BIO_new(BIO_s_mem());
    int ok = s != NULL && ssl != NULL && rbio != NULL && wbio != NULL
        && leanp2p_tls_attach_check(ssl, check) == 1;
    if (ok && !server) ok = SSL_set_alpn_protos(ssl, c->alpn, c->alpn_len) == 0;
    if (!ok) {
        SSL_free(ssl);
        BIO_free(rbio);
        BIO_free(wbio);
        free(s);
        ERR_clear_error();
        return lean_io_result_mk_ok(none());
    }
    /* An empty memory BIO answers "retry" rather than EOF, so a read
       that finds no bytes asks for more. */
    BIO_set_mem_eof_return(rbio, -1);
    SSL_set_bio(ssl, rbio, wbio);
    SSL_set_verify(ssl, server ? SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT
                               : SSL_VERIFY_PEER, NULL);
    if (server) SSL_set_accept_state(ssl); else SSL_set_connect_state(ssl);
    s->ssl = ssl;
    s->rbio = rbio;
    s->wbio = wbio;
    pthread_mutex_init(&s->mu, NULL);
    lean_inc(context);
    s->context = context;
    return lean_io_result_mk_ok(some(lean_alloc_external(session_class, s)));
}

/* Feed the bytes the connection read. A memory BIO grows, so the write
   takes every byte unless an allocation fails. 1 when every byte went,
   0 otherwise (the error text says why): a dropped byte would corrupt
   the record stream, so the caller fails the connection. */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_feed(b_lean_obj_arg session, b_lean_obj_arg bytes) {
    tls_session *s = session_of(session);
    size_t n = lean_sarray_size(bytes);
    if (n == 0) return lean_io_result_mk_ok(lean_box(1));
    pthread_mutex_lock(&s->mu);
    ERR_clear_error();
    int ok = n <= INT_MAX && BIO_write(s->rbio, lean_sarray_cptr(bytes), (int)n) == (int)n;
    if (!ok) keep_error(s, "the input buffer refused the peer's bytes");
    pthread_mutex_unlock(&s->mu);
    return lean_io_result_mk_ok(lean_box(ok));
}

/* True when a failed handshake step refused the peer's certificate: the
   verify callback failed it (a chain of more than one, or the caller's
   check), or a client sent none to a server that requires one (libssl
   raises `SSL_R_PEER_DID_NOT_RETURN_A_CERTIFICATE`). It reads the
   thread's error queue, so the caller asks before it clears the
   queue. */
int leanp2p_tls_refused(const SSL *ssl) {
    unsigned long e = ERR_peek_error();
    return SSL_get_verify_result(ssl) != X509_V_OK
        || (ERR_GET_LIB(e) == ERR_LIB_SSL
            && ERR_GET_REASON(e) == SSL_R_PEER_DID_NOT_RETURN_A_CERTIFICATE);
}

/* One handshake step: 0 done, 1 more input needed, 2 failed, 3 failed
   because the peer's certificate was refused (the error text says why
   in both). The step leaves its output in the output BIO. */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_handshake(b_lean_obj_arg session) {
    tls_session *s = session_of(session);
    pthread_mutex_lock(&s->mu);
    ERR_clear_error();
    int r = SSL_do_handshake(s->ssl);
    uint8_t code;
    if (r == 1) code = 0;
    else if (SSL_get_error(s->ssl, r) == SSL_ERROR_WANT_READ) code = 1;
    else {
        code = leanp2p_tls_refused(s->ssl) ? 3 : 2;
        keep_error(s, "the handshake failed");
        /* A refusal of the verify callback names its own reason, which
           says more than libssl's "certificate verify failed". */
        const char *refusal = leanp2p_tls_refusal(s->ssl);
        if (code == 3 && refusal[0] != '\0')
            snprintf(s->error, sizeof s->error, "%s", refusal);
    }
    pthread_mutex_unlock(&s->mu);
    return lean_io_result_mk_ok(lean_box(code));
}

/* Read up to `max` bytes of plaintext. The answer is the Lean structure
   `TlsNative.ReadRaw`: one object field, the bytes, then one `UInt8`,
   the code. 0 bytes, 1 more input needed, 2 the peer's close_notify,
   3 failed (the error text says why). */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_read(b_lean_obj_arg session, size_t max) {
    tls_session *s = session_of(session);
    if (max == 0 || max > INT32_MAX) max = 16384;
    lean_object *out = lean_alloc_sarray(1, 0, max);
    pthread_mutex_lock(&s->mu);
    ERR_clear_error();
    int r = SSL_read(s->ssl, lean_sarray_cptr(out), (int)max);
    uint8_t code;
    size_t got = 0;
    if (r > 0) {
        code = 0;
        got = (size_t)r;
    } else {
        int e = SSL_get_error(s->ssl, r);
        if (e == SSL_ERROR_WANT_READ) code = 1;
        else if (e == SSL_ERROR_ZERO_RETURN) code = 2;
        else {
            keep_error(s, "the read failed");
            code = 3;
        }
    }
    pthread_mutex_unlock(&s->mu);
    lean_to_sarray(out)->m_size = got;
    lean_object *res = lean_alloc_ctor(0, 1, 1);
    lean_ctor_set(res, 0, out);
    lean_ctor_set_uint8(res, sizeof(void *), code);
    return lean_io_result_mk_ok(res);
}

/* Encrypt the plaintext into the output BIO. 1 when every byte went,
   0 on a failure (the error text says why). */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_write(b_lean_obj_arg session, b_lean_obj_arg bytes) {
    tls_session *s = session_of(session);
    const uint8_t *p = lean_sarray_cptr(bytes);
    size_t n = lean_sarray_size(bytes);
    int ok = 1;
    pthread_mutex_lock(&s->mu);
    ERR_clear_error();
    while (ok && n > 0) {
        int chunk = n > 16384 ? 16384 : (int)n;
        int r = SSL_write(s->ssl, p, chunk);
        if (r <= 0) {
            keep_error(s, "the write failed");
            ok = 0;
        } else {
            p += r;
            n -= (size_t)r;
        }
    }
    pthread_mutex_unlock(&s->mu);
    return lean_io_result_mk_ok(lean_box(ok));
}

/* True when the session holds the bytes of a record it has not read
   whole: the record layer's buffer (`SSL_has_pending`, which counts
   `tls_unprocessed_read_pending`) or the input BIO. At the end of the
   connection this tells a cut record from a record boundary. */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_partial(b_lean_obj_arg session) {
    tls_session *s = session_of(session);
    pthread_mutex_lock(&s->mu);
    int partial = SSL_has_pending(s->ssl) || BIO_ctrl_pending(s->rbio) > 0;
    pthread_mutex_unlock(&s->mu);
    return lean_io_result_mk_ok(lean_box(partial));
}

/* Queue a TLS 1.3 KeyUpdate that asks the peer to update its keys too
   (RFC 8446 §4.6.3), and write it to the output BIO now:
   `SSL_key_update` marks the session as in a handshake, and the next
   `SSL_do_handshake` sends the message. 1 on success, 0 on a failure
   (the error text says why). */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_key_update(b_lean_obj_arg session) {
    tls_session *s = session_of(session);
    pthread_mutex_lock(&s->mu);
    ERR_clear_error();
    int ok = SSL_key_update(s->ssl, SSL_KEY_UPDATE_REQUESTED) == 1
        && SSL_do_handshake(s->ssl) == 1;
    if (!ok) keep_error(s, "the key update failed");
    pthread_mutex_unlock(&s->mu);
    return lean_io_result_mk_ok(lean_box(ok));
}

/* Queue the close_notify alert in the output BIO. */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_shutdown(b_lean_obj_arg session) {
    tls_session *s = session_of(session);
    pthread_mutex_lock(&s->mu);
    ERR_clear_error();
    if (SSL_is_init_finished(s->ssl)) SSL_shutdown(s->ssl);
    ERR_clear_error();
    pthread_mutex_unlock(&s->mu);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Take every byte the output BIO holds. */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_drain(b_lean_obj_arg session) {
    tls_session *s = session_of(session);
    pthread_mutex_lock(&s->mu);
    size_t n = BIO_ctrl_pending(s->wbio);
    lean_object *out = lean_alloc_sarray(1, n, n);
    if (n > 0) BIO_read(s->wbio, lean_sarray_cptr(out), (int)n);
    pthread_mutex_unlock(&s->mu);
    return lean_io_result_mk_ok(out);
}

/* The peer's certificate as DER, once the handshake has seen it. */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_peer_certificate(b_lean_obj_arg session) {
    tls_session *s = session_of(session);
    pthread_mutex_lock(&s->mu);
    X509 *x = SSL_get0_peer_certificate(s->ssl);
    unsigned char *der = NULL;
    int n = x != NULL ? i2d_X509(x, &der) : -1;
    lean_object *r = n > 0 ? some(mk_bytes(der, (size_t)n)) : none();
    OPENSSL_free(der);
    pthread_mutex_unlock(&s->mu);
    return lean_io_result_mk_ok(r);
}

/* The ALPN protocol the handshake selected; empty when none. */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_alpn(b_lean_obj_arg session) {
    tls_session *s = session_of(session);
    const unsigned char *p = NULL;
    unsigned int n = 0;
    pthread_mutex_lock(&s->mu);
    SSL_get0_alpn_selected(s->ssl, &p, &n);
    lean_object *r = lean_mk_string_from_bytes((const char *)(p != NULL ? p : (const unsigned char *)""), n);
    pthread_mutex_unlock(&s->mu);
    return lean_io_result_mk_ok(r);
}

/* The negotiated protocol version text, such as "TLSv1.3". */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_version(b_lean_obj_arg session) {
    tls_session *s = session_of(session);
    pthread_mutex_lock(&s->mu);
    lean_object *r = lean_mk_string(SSL_get_version(s->ssl));
    pthread_mutex_unlock(&s->mu);
    return lean_io_result_mk_ok(r);
}

/* The text of the session's last failure. */
LEAN_EXPORT lean_obj_res leanp2p_tls_session_error(b_lean_obj_arg session) {
    tls_session *s = session_of(session);
    pthread_mutex_lock(&s->mu);
    lean_object *r = lean_mk_string(s->error);
    pthread_mutex_unlock(&s->mu);
    return lean_io_result_mk_ok(r);
}
