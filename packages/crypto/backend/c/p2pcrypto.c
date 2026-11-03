/*
 * p2pcrypto.c: the OpenSSL 3 shim behind `crypto/backend`.
 *
 * One C file, auditable in one sitting (packages/crypto/backend/docs/
 * ARCHITECTURE.md, contract 3). The conventions, binding for every
 * function below:
 *
 * - Every exported symbol carries the `leanp2p_` prefix. Exactly one
 *   `@[extern]` declaration in `Backend/Sym.lean`, `Backend/Sign.lean`,
 *   or `Backend/X509.lean` reaches it.
 * - The shim borrows every `ByteArray` argument (`b_lean_obj_arg`). It
 *   never takes a reference to an argument and never frees one. An
 *   owned parameter leaks one reference per call (contract 1).
 * - Sizes that the Lean side checks cross unchecked: a 32-byte key, a
 *   12-byte nonce, a tag-sized ciphertext, the `int` range of the AEAD
 *   lengths. The shim checks only what the parse alone knows (contract
 *   2). That is the DER-derived facts of a parsed key, and that a DER
 *   input fits the `int` length of its OpenSSL parser.
 * - A pure binding returns `Option ByteArray`: `none` is a failure, and
 *   the Lean wrapper lifts it once into `Except CryptoError`. A verifier
 *   returns `uint8_t` (Lean `Bool`), and every malformed input or
 *   library fault folds into 0, fail-closed.
 * - A binding that draws randomness takes the IO world token and returns
 *   an IO result.
 */

#include <lean/lean.h>

#include <limits.h>
#include <string.h>

#include <openssl/asn1.h>
#include <openssl/bn.h>
#include <openssl/core_names.h>
#include <openssl/ec.h>
#include <openssl/evp.h>
#include <openssl/kdf.h>
#include <openssl/objects.h>
#include <openssl/params.h>
#include <openssl/rand.h>
#include <openssl/x509.h>
#include <openssl/x509v3.h>

/* ------------------------------------------------------------------ */
/* Lean object helpers                                                 */
/* ------------------------------------------------------------------ */

static inline const uint8_t *bptr(b_lean_obj_arg b) { return lean_sarray_cptr(b); }
static inline size_t blen(b_lean_obj_arg b) { return lean_sarray_size(b); }

/* A fresh `ByteArray` of `n` bytes, uninitialized. */
static lean_object *alloc_bytes(size_t n) { return lean_alloc_sarray(1, n, n); }

static lean_object *mk_bytes(const uint8_t *p, size_t n) {
    lean_object *r = alloc_bytes(n);
    if (n > 0) memcpy(lean_sarray_cptr(r), p, n);
    return r;
}

/* Shrink a `ByteArray` to `n` bytes, for a call that reports its real
   output length only after it runs. */
static lean_object *set_len(lean_object *b, size_t n) {
    lean_to_sarray(b)->m_size = n;
    return b;
}

static lean_object *none(void) { return lean_box(0); }

static lean_object *some(lean_object *v) {
    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, v);
    return r;
}

/* `some b` when `ok`, else free `b` and give `none`. */
static lean_object *some_or_free(int ok, lean_object *b) {
    if (ok) return some(b);
    lean_dec(b);
    return none();
}

/* OpenSSL takes `int` lengths in several places. */
static inline int fits_int(size_t n) { return n <= (size_t)INT_MAX; }

/* ------------------------------------------------------------------ */
/* Randomness                                                          */
/* ------------------------------------------------------------------ */

/* `n` random bytes from the OpenSSL DRBG. The Lean side caps `n`. */
LEAN_EXPORT lean_obj_res leanp2p_random_bytes(size_t n, lean_obj_arg w) {
    (void)w;
    lean_object *out = alloc_bytes(n);
    if (n > 0 && RAND_bytes(lean_sarray_cptr(out), (int)n) != 1) {
        lean_dec(out);
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("RAND_bytes failed")));
    }
    return lean_io_result_mk_ok(out);
}

/* ------------------------------------------------------------------ */
/* Digests, HMAC, HKDF                                                 */
/* ------------------------------------------------------------------ */

static lean_object *digest(const EVP_MD *md, b_lean_obj_arg data) {
    lean_object *out = alloc_bytes((size_t)EVP_MD_get_size(md));
    unsigned int n = 0;
    int ok = EVP_Digest(bptr(data), blen(data), lean_sarray_cptr(out), &n, md, NULL) == 1;
    return some_or_free(ok, out);
}

LEAN_EXPORT lean_obj_res leanp2p_sha1(b_lean_obj_arg data) { return digest(EVP_sha1(), data); }
LEAN_EXPORT lean_obj_res leanp2p_sha256(b_lean_obj_arg data) { return digest(EVP_sha256(), data); }
LEAN_EXPORT lean_obj_res leanp2p_sha512(b_lean_obj_arg data) { return digest(EVP_sha512(), data); }

LEAN_EXPORT lean_obj_res leanp2p_hmac_sha256(b_lean_obj_arg key, b_lean_obj_arg data) {
    lean_object *out = alloc_bytes(32);
    size_t n = 0;
    int ok = EVP_Q_mac(NULL, "HMAC", NULL, "SHA256", NULL, bptr(key), blen(key),
                       bptr(data), blen(data), lean_sarray_cptr(out), 32, &n) != NULL
             && n == 32;
    return some_or_free(ok, out);
}

/* HKDF-SHA-256, extract then expand, `len` output bytes. The Lean side
   caps `len` at 255 hash blocks (RFC 5869 §2.3). */
LEAN_EXPORT lean_obj_res leanp2p_hkdf_sha256(b_lean_obj_arg salt, b_lean_obj_arg ikm,
                                             b_lean_obj_arg info, size_t len) {
    EVP_KDF *kdf = EVP_KDF_fetch(NULL, "HKDF", NULL);
    EVP_KDF_CTX *kctx = kdf ? EVP_KDF_CTX_new(kdf) : NULL;
    lean_object *out = alloc_bytes(len);
    OSSL_PARAM params[] = {
        OSSL_PARAM_construct_utf8_string(OSSL_KDF_PARAM_DIGEST, "SHA256", 0),
        OSSL_PARAM_construct_octet_string(OSSL_KDF_PARAM_KEY, (void *)bptr(ikm), blen(ikm)),
        OSSL_PARAM_construct_octet_string(OSSL_KDF_PARAM_SALT, (void *)bptr(salt), blen(salt)),
        OSSL_PARAM_construct_octet_string(OSSL_KDF_PARAM_INFO, (void *)bptr(info), blen(info)),
        OSSL_PARAM_construct_end(),
    };
    int ok = kctx != NULL && EVP_KDF_derive(kctx, lean_sarray_cptr(out), len, params) == 1;
    EVP_KDF_CTX_free(kctx);
    EVP_KDF_free(kdf);
    return some_or_free(ok, out);
}

/* ------------------------------------------------------------------ */
/* ChaCha20-Poly1305 (RFC 8439)                                        */
/* ------------------------------------------------------------------ */

/* The one home of the Poly1305 tag length (RFC 8439 §2.8). The Lean side
   reads it through `Backend.aeadTagLen`, and `chachaOpen` checks it
   before `leanp2p_chacha_open` subtracts it. */
#define TAG_LEN 16

LEAN_EXPORT uint32_t leanp2p_aead_tag_len(lean_obj_arg unit) {
    (void)unit;
    return TAG_LEN;
}

/* Seal: the output is the ciphertext followed by the 16-byte tag. The
   key is 32 bytes and the nonce 12, and `pt` and `ad` fit an `int`, all
   checked on the Lean side. */
LEAN_EXPORT lean_obj_res leanp2p_chacha_seal(b_lean_obj_arg key, b_lean_obj_arg nonce,
                                             b_lean_obj_arg ad, b_lean_obj_arg pt) {
    size_t n = blen(pt);
    EVP_CIPHER_CTX *c = EVP_CIPHER_CTX_new();
    lean_object *out = alloc_bytes(n + TAG_LEN);
    uint8_t *o = lean_sarray_cptr(out);
    int len = 0;
    int ok = c != NULL
        && EVP_EncryptInit_ex(c, EVP_chacha20_poly1305(), NULL, bptr(key), bptr(nonce)) == 1
        && (blen(ad) == 0 || EVP_EncryptUpdate(c, NULL, &len, bptr(ad), (int)blen(ad)) == 1)
        && (n == 0 || EVP_EncryptUpdate(c, o, &len, bptr(pt), (int)n) == 1)
        && EVP_EncryptFinal_ex(c, o + n, &len) == 1
        && EVP_CIPHER_CTX_ctrl(c, EVP_CTRL_AEAD_GET_TAG, TAG_LEN, o + n) == 1;
    EVP_CIPHER_CTX_free(c);
    return some_or_free(ok, out);
}

/* Open: `none` on a tag mismatch. The Lean side checks that `ct` holds at
   least the tag and that `ct` and `ad` fit an `int`. It maps `none` to
   the authentication-failure arm. */
LEAN_EXPORT lean_obj_res leanp2p_chacha_open(b_lean_obj_arg key, b_lean_obj_arg nonce,
                                             b_lean_obj_arg ad, b_lean_obj_arg ct) {
    size_t n = blen(ct) - TAG_LEN;
    EVP_CIPHER_CTX *c = EVP_CIPHER_CTX_new();
    lean_object *out = alloc_bytes(n);
    uint8_t *o = lean_sarray_cptr(out);
    int len = 0;
    int ok = c != NULL
        && EVP_DecryptInit_ex(c, EVP_chacha20_poly1305(), NULL, bptr(key), bptr(nonce)) == 1
        && (blen(ad) == 0 || EVP_DecryptUpdate(c, NULL, &len, bptr(ad), (int)blen(ad)) == 1)
        && (n == 0 || EVP_DecryptUpdate(c, o, &len, bptr(ct), (int)n) == 1)
        && EVP_CIPHER_CTX_ctrl(c, EVP_CTRL_AEAD_SET_TAG, TAG_LEN, (void *)(bptr(ct) + n)) == 1
        && EVP_DecryptFinal_ex(c, o + n, &len) == 1;
    EVP_CIPHER_CTX_free(c);
    return some_or_free(ok, out);
}

/* ------------------------------------------------------------------ */
/* Raw-key curves: Ed25519 (RFC 8032) and X25519 (RFC 7748)            */
/* ------------------------------------------------------------------ */

/* The raw public key of a raw private key of type `type`. */
static lean_object *raw_public(int type, b_lean_obj_arg priv) {
    EVP_PKEY *k = EVP_PKEY_new_raw_private_key(type, NULL, bptr(priv), 32);
    lean_object *out = alloc_bytes(32);
    size_t n = 32;
    int ok = k != NULL && EVP_PKEY_get_raw_public_key(k, lean_sarray_cptr(out), &n) == 1
             && n == 32;
    EVP_PKEY_free(k);
    return some_or_free(ok, out);
}

LEAN_EXPORT lean_obj_res leanp2p_ed25519_public(b_lean_obj_arg seed) {
    return raw_public(EVP_PKEY_ED25519, seed);
}

LEAN_EXPORT lean_obj_res leanp2p_x25519_public(b_lean_obj_arg priv) {
    return raw_public(EVP_PKEY_X25519, priv);
}

/* The one home of the Ed25519 signature length (RFC 8032 §5.1.6). The
   Lean side reads it through `Backend.ed25519SigLen`, and
   `ed25519Verify` checks it before `leanp2p_ed25519_verify` reads that
   many bytes. */
#define ED25519_SIG_LEN 64

LEAN_EXPORT uint32_t leanp2p_ed25519_sig_len(lean_obj_arg unit) {
    (void)unit;
    return ED25519_SIG_LEN;
}

/* Ed25519 signs deterministically: the same seed and message give the
   same signature. */
LEAN_EXPORT lean_obj_res leanp2p_ed25519_sign(b_lean_obj_arg seed, b_lean_obj_arg msg) {
    EVP_PKEY *k = EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519, NULL, bptr(seed), 32);
    EVP_MD_CTX *m = EVP_MD_CTX_new();
    lean_object *out = alloc_bytes(ED25519_SIG_LEN);
    size_t n = ED25519_SIG_LEN;
    int ok = k != NULL && m != NULL
        && EVP_DigestSignInit(m, NULL, NULL, NULL, k) == 1
        && EVP_DigestSign(m, lean_sarray_cptr(out), &n, bptr(msg), blen(msg)) == 1
        && n == ED25519_SIG_LEN;
    EVP_MD_CTX_free(m);
    EVP_PKEY_free(k);
    return some_or_free(ok, out);
}

/* The public key is 32 bytes and the signature `ED25519_SIG_LEN`,
   checked on the Lean side. */
LEAN_EXPORT uint8_t leanp2p_ed25519_verify(b_lean_obj_arg pub, b_lean_obj_arg msg,
                                           b_lean_obj_arg sig) {
    EVP_PKEY *k = EVP_PKEY_new_raw_public_key(EVP_PKEY_ED25519, NULL, bptr(pub), 32);
    EVP_MD_CTX *m = EVP_MD_CTX_new();
    int ok = k != NULL && m != NULL
        && EVP_DigestVerifyInit(m, NULL, NULL, NULL, k) == 1
        && EVP_DigestVerify(m, bptr(sig), ED25519_SIG_LEN, bptr(msg), blen(msg)) == 1;
    EVP_MD_CTX_free(m);
    EVP_PKEY_free(k);
    return ok;
}

/* X25519 DH. OpenSSL fails the derive when the shared secret is all
   zero (a small-order peer key, RFC 7748 §6.1), and the shim passes
   that failure on as `none`. */
LEAN_EXPORT lean_obj_res leanp2p_x25519_dh(b_lean_obj_arg priv, b_lean_obj_arg peer) {
    EVP_PKEY *k = EVP_PKEY_new_raw_private_key(EVP_PKEY_X25519, NULL, bptr(priv), 32);
    EVP_PKEY *p = EVP_PKEY_new_raw_public_key(EVP_PKEY_X25519, NULL, bptr(peer), 32);
    EVP_PKEY_CTX *c = k ? EVP_PKEY_CTX_new(k, NULL) : NULL;
    lean_object *out = alloc_bytes(32);
    size_t n = 32;
    int ok = p != NULL && c != NULL
        && EVP_PKEY_derive_init(c) == 1
        && EVP_PKEY_derive_set_peer(c, p) == 1
        && EVP_PKEY_derive(c, lean_sarray_cptr(out), &n) == 1
        && n == 32;
    EVP_PKEY_CTX_free(c);
    EVP_PKEY_free(p);
    EVP_PKEY_free(k);
    return some_or_free(ok, out);
}

/* ------------------------------------------------------------------ */
/* DER keys: RSA, ECDSA P-256, secp256k1                               */
/* ------------------------------------------------------------------ */

/* The verifier strictness rules (root ARCHITECTURE §4.6) live in this
   section:
   - a key loads only as the type it claims,
   - an RSA key has 2048 to 8192 bits,
   - a secp256k1 signature has a low S in strict DER. */

/* The one home of the RSA modulus range. The Lean side reads it through
   the two getters below (`Backend.rsaMinBits`, `Backend.rsaMaxBits`).
   So the generator's check and the verifiers' check cannot drift. */
#define RSA_MIN_BITS 2048
#define RSA_MAX_BITS 8192

LEAN_EXPORT uint32_t leanp2p_rsa_min_bits(lean_obj_arg unit) {
    (void)unit;
    return RSA_MIN_BITS;
}

LEAN_EXPORT uint32_t leanp2p_rsa_max_bits(lean_obj_arg unit) {
    (void)unit;
    return RSA_MAX_BITS;
}

/* True when `k` is an EC key on the named group. */
static int ec_group_is(EVP_PKEY *k, const char *group) {
    char name[64];
    size_t n = 0;
    return EVP_PKEY_is_a(k, "EC")
        && EVP_PKEY_get_group_name(k, name, sizeof name, &n) == 1
        && strcmp(name, group) == 0;
}

static int rsa_size_ok(EVP_PKEY *k) {
    int bits = EVP_PKEY_get_bits(k);
    return EVP_PKEY_is_a(k, "RSA") && bits >= RSA_MIN_BITS && bits <= RSA_MAX_BITS;
}

/* A private key of OpenSSL type `type` in its type-specific DER form
   (PKCS#1 for RSA, SEC1 for EC). NULL on any parse failure, or when
   bytes remain after the structure. */
static EVP_PKEY *load_private_der(int type, b_lean_obj_arg der) {
    if (!fits_int(blen(der))) return NULL;
    const unsigned char *p = bptr(der);
    EVP_PKEY *k = d2i_PrivateKey(type, NULL, &p, (long)blen(der));
    if (k != NULL && p != bptr(der) + blen(der)) {
        EVP_PKEY_free(k);
        return NULL;
    }
    return k;
}

/* A SubjectPublicKeyInfo DER public key, with no trailing bytes. */
static EVP_PKEY *load_spki(b_lean_obj_arg der) {
    if (!fits_int(blen(der))) return NULL;
    const unsigned char *p = bptr(der);
    EVP_PKEY *k = d2i_PUBKEY(NULL, &p, (long)blen(der));
    if (k != NULL && p != bptr(der) + blen(der)) {
        EVP_PKEY_free(k);
        return NULL;
    }
    return k;
}

/* The SPKI DER encoding of the public half of `k`. OpenSSL encodes an EC
   point in the form the key came in, and a SEC1 key may carry a
   compressed point. So the EC case sets the uncompressed form first,
   the one form the P-256 verifiers accept. */
static lean_object *spki_of(EVP_PKEY *k) {
    if (EVP_PKEY_is_a(k, "EC")
        && EVP_PKEY_set_utf8_string_param(k, OSSL_PKEY_PARAM_EC_POINT_CONVERSION_FORMAT,
                                          OSSL_PKEY_EC_POINT_CONVERSION_FORMAT_UNCOMPRESSED) != 1)
        return none();
    int n = i2d_PUBKEY(k, NULL);
    if (n <= 0) return none();
    lean_object *out = alloc_bytes((size_t)n);
    unsigned char *p = lean_sarray_cptr(out);
    return some_or_free(i2d_PUBKEY(k, &p) == n, out);
}

/* The type-specific DER of a private key: PKCS#1 for RSA, SEC1 for EC,
   whatever form the key came in. The scratch copy holds key material,
   so `OPENSSL_clear_free` clears it before it frees it. */
static lean_object *private_der_of(EVP_PKEY *k) {
    unsigned char *der = NULL;
    int n = k != NULL ? i2d_PrivateKey(k, &der) : -1;
    lean_object *r = n > 0 ? some(mk_bytes(der, (size_t)n)) : none();
    OPENSSL_clear_free(der, n > 0 ? (size_t)n : 0);
    return r;
}

/* A SHA-256 signature by `k` over `msg`, `none` on failure. For RSA the
   default padding is PKCS#1 v1.5. For EC the output is a DER
   ECDSA-Sig-Value. */
static lean_object *sign_sha256(EVP_PKEY *k, b_lean_obj_arg msg) {
    EVP_MD_CTX *m = EVP_MD_CTX_new();
    size_t n = 0;
    lean_object *out = NULL;
    int ok = m != NULL
        && EVP_DigestSignInit(m, NULL, EVP_sha256(), NULL, k) == 1
        && EVP_DigestSign(m, NULL, &n, bptr(msg), blen(msg)) == 1;
    if (ok) {
        out = alloc_bytes(n);
        ok = EVP_DigestSign(m, lean_sarray_cptr(out), &n, bptr(msg), blen(msg)) == 1;
        if (ok) set_len(out, n);
    }
    EVP_MD_CTX_free(m);
    if (out == NULL) return none();
    return some_or_free(ok, out);
}

static int verify_sha256(EVP_PKEY *k, b_lean_obj_arg msg, b_lean_obj_arg sig) {
    EVP_MD_CTX *m = EVP_MD_CTX_new();
    int ok = m != NULL
        && EVP_DigestVerifyInit(m, NULL, EVP_sha256(), NULL, k) == 1
        && EVP_DigestVerify(m, bptr(sig), blen(sig), bptr(msg), blen(msg)) == 1;
    EVP_MD_CTX_free(m);
    return ok;
}

/* RSA, RSASSA-PKCS1-v1_5 with SHA-256. */

LEAN_EXPORT lean_obj_res leanp2p_rsa_public(b_lean_obj_arg priv) {
    EVP_PKEY *k = load_private_der(EVP_PKEY_RSA, priv);
    lean_object *r = (k != NULL && rsa_size_ok(k)) ? spki_of(k) : none();
    EVP_PKEY_free(k);
    return r;
}

/* The PKCS#1 DER of a DER private key the loader accepts (PKCS#1 or
   PKCS#8), under the same size rule as the other RSA bindings. */
LEAN_EXPORT lean_obj_res leanp2p_rsa_pkcs1(b_lean_obj_arg priv) {
    EVP_PKEY *k = load_private_der(EVP_PKEY_RSA, priv);
    lean_object *r = (k != NULL && rsa_size_ok(k)) ? private_der_of(k) : none();
    EVP_PKEY_free(k);
    return r;
}

/* PKCS#1 v1.5 signing draws no randomness, so the binding is pure. */
LEAN_EXPORT lean_obj_res leanp2p_rsa_sign(b_lean_obj_arg priv, b_lean_obj_arg msg) {
    EVP_PKEY *k = load_private_der(EVP_PKEY_RSA, priv);
    lean_object *r = (k != NULL && rsa_size_ok(k)) ? sign_sha256(k, msg) : none();
    EVP_PKEY_free(k);
    return r;
}

LEAN_EXPORT uint8_t leanp2p_rsa_verify(b_lean_obj_arg spki, b_lean_obj_arg msg,
                                       b_lean_obj_arg sig) {
    EVP_PKEY *k = load_spki(spki);
    int ok = k != NULL && rsa_size_ok(k) && verify_sha256(k, msg, sig);
    EVP_PKEY_free(k);
    return ok;
}

/* ECDSA P-256 with SHA-256. Verification is the interim fallback until
   the facade routes it to the etheorem package. */

LEAN_EXPORT lean_obj_res leanp2p_p256_public(b_lean_obj_arg priv) {
    EVP_PKEY *k = load_private_der(EVP_PKEY_EC, priv);
    lean_object *r = (k != NULL && ec_group_is(k, "prime256v1")) ? spki_of(k) : none();
    EVP_PKEY_free(k);
    return r;
}

/* The SEC1 DER of a DER P-256 private key the loader accepts (SEC1 or
   PKCS#8). */
LEAN_EXPORT lean_obj_res leanp2p_p256_sec1(b_lean_obj_arg priv) {
    EVP_PKEY *k = load_private_der(EVP_PKEY_EC, priv);
    lean_object *r = (k != NULL && ec_group_is(k, "prime256v1")) ? private_der_of(k) : none();
    EVP_PKEY_free(k);
    return r;
}

/* ECDSA draws a random nonce, so the binding takes the world. */
LEAN_EXPORT lean_obj_res leanp2p_p256_sign(b_lean_obj_arg priv, b_lean_obj_arg msg,
                                           lean_obj_arg w) {
    (void)w;
    EVP_PKEY *k = load_private_der(EVP_PKEY_EC, priv);
    lean_object *r = (k != NULL && ec_group_is(k, "prime256v1")) ? sign_sha256(k, msg) : none();
    EVP_PKEY_free(k);
    return lean_io_result_mk_ok(r);
}

/* The Lean wrapper `Backend.p256Verify` admits only the 91-byte SPKI of
   an uncompressed point (Go's form), so the key reaches this function in
   that form. The curve check stays here, on the parsed key. */
LEAN_EXPORT uint8_t leanp2p_p256_verify(b_lean_obj_arg spki, b_lean_obj_arg msg,
                                        b_lean_obj_arg sig) {
    EVP_PKEY *k = load_spki(spki);
    int ok = k != NULL && ec_group_is(k, "prime256v1") && verify_sha256(k, msg, sig);
    EVP_PKEY_free(k);
    return ok;
}

/* secp256k1 ECDSA with SHA-256. The etheorem verifier accepts a high S,
   so all of secp256k1 stays here (root ARCHITECTURE §4.6). */

/* The private key crosses as the raw 32-byte scalar. The shim wraps it
   in a fixed SEC1 ECPrivateKey (RFC 5915) with the secp256k1 OID
   1.3.132.0.10 and no public key. OpenSSL computes the public point
   when it loads the key. */
static const uint8_t SEC1_K1_HEAD[7] = {0x30, 0x2e, 0x02, 0x01, 0x01, 0x04, 0x20};
static const uint8_t SEC1_K1_TAIL[9] = {0xa0, 0x07, 0x06, 0x05, 0x2b, 0x81, 0x04, 0x00, 0x0a};

static EVP_PKEY *k1_private(b_lean_obj_arg scalar) {
    uint8_t der[sizeof SEC1_K1_HEAD + 32 + sizeof SEC1_K1_TAIL];
    memcpy(der, SEC1_K1_HEAD, sizeof SEC1_K1_HEAD);
    memcpy(der + sizeof SEC1_K1_HEAD, bptr(scalar), 32);
    memcpy(der + sizeof SEC1_K1_HEAD + 32, SEC1_K1_TAIL, sizeof SEC1_K1_TAIL);
    const unsigned char *p = der;
    EVP_PKEY *k = d2i_PrivateKey(EVP_PKEY_EC, NULL, &p, (long)sizeof der);
    OPENSSL_cleanse(der, sizeof der);
    return k;
}

/* A secp256k1 public key from its SEC1 point encoding, compressed (33
   bytes) or uncompressed (65). OpenSSL rejects a point off the curve. */
static EVP_PKEY *k1_public(b_lean_obj_arg point) {
    EVP_PKEY_CTX *c = EVP_PKEY_CTX_new_from_name(NULL, "EC", NULL);
    EVP_PKEY *k = NULL;
    OSSL_PARAM params[] = {
        OSSL_PARAM_construct_utf8_string(OSSL_PKEY_PARAM_GROUP_NAME, "secp256k1", 0),
        OSSL_PARAM_construct_octet_string(OSSL_PKEY_PARAM_PUB_KEY, (void *)bptr(point),
                                          blen(point)),
        OSSL_PARAM_construct_end(),
    };
    if (c == NULL || EVP_PKEY_fromdata_init(c) != 1
        || EVP_PKEY_fromdata(c, &k, EVP_PKEY_PUBLIC_KEY, params) != 1)
        k = NULL;
    EVP_PKEY_CTX_free(c);
    return k;
}

/* The DER signature `der` parsed strictly: the bytes re-encode to
   themselves. NULL otherwise. */
static ECDSA_SIG *parse_sig_strict(const uint8_t *der, size_t len) {
    if (!fits_int(len)) return NULL;
    const unsigned char *p = der;
    ECDSA_SIG *s = d2i_ECDSA_SIG(NULL, &p, (long)len);
    if (s == NULL) return NULL;
    unsigned char *re = NULL;
    int n = i2d_ECDSA_SIG(s, &re);
    int same = p == der + len && n == (int)len && memcmp(re, der, len) == 0;
    OPENSSL_free(re);
    if (!same) {
        ECDSA_SIG_free(s);
        return NULL;
    }
    return s;
}

/* The group order of the EC key `k`, half of it in `half`. */
static int ec_half_order(EVP_PKEY *k, BIGNUM **order, BIGNUM **half) {
    *order = NULL;
    *half = BN_new();
    return *half != NULL
        && EVP_PKEY_get_bn_param(k, OSSL_PKEY_PARAM_EC_ORDER, order) == 1
        && BN_rshift1(*half, *order) == 1;
}

/* The compressed SEC1 point (SEC 1 §2.3.3): 0x02 or 0x03 by the parity
   of y, then x. For a key loaded from DER, OpenSSL gives the
   uncompressed form and ignores a conversion-format request. So the
   shim compresses the 65-byte `04 ‖ x ‖ y` form itself. */
LEAN_EXPORT lean_obj_res leanp2p_secp256k1_public(b_lean_obj_arg scalar) {
    EVP_PKEY *k = k1_private(scalar);
    uint8_t full[65];
    size_t n = 0;
    int ok = k != NULL
        && EVP_PKEY_get_octet_string_param(k, OSSL_PKEY_PARAM_ENCODED_PUBLIC_KEY,
                                           full, sizeof full, &n) == 1
        && n == 65 && full[0] == 0x04;
    EVP_PKEY_free(k);
    if (!ok) return none();
    lean_object *out = alloc_bytes(33);
    uint8_t *o = lean_sarray_cptr(out);
    o[0] = 0x02 | (full[64] & 1);
    memcpy(o + 1, full + 1, 32);
    return some(out);
}

/* 1 when `point` is a secp256k1 point that OpenSSL loads: on the curve,
   in a SEC1 form of 33 or 65 bytes. The caller fixes the form. */
LEAN_EXPORT uint8_t leanp2p_secp256k1_check(b_lean_obj_arg point) {
    EVP_PKEY *k = k1_public(point);
    EVP_PKEY_free(k);
    return k != NULL;
}

/* Sign, then normalize S to its low form (S > n/2 becomes n - S), so the
   signature passes the low-S rule of the verifier below. */
LEAN_EXPORT lean_obj_res leanp2p_secp256k1_sign(b_lean_obj_arg scalar, b_lean_obj_arg msg,
                                                lean_obj_arg w) {
    (void)w;
    EVP_PKEY *k = k1_private(scalar);
    lean_object *raw = k != NULL ? sign_sha256(k, msg) : none();
    BIGNUM *order = NULL, *half = NULL, *low = NULL;
    ECDSA_SIG *s = NULL;
    lean_object *r = none();
    if (!lean_is_scalar(raw) && ec_half_order(k, &order, &half)) {
        lean_object *der = lean_ctor_get(raw, 0);
        s = parse_sig_strict(bptr(der), blen(der));
        const BIGNUM *sr = NULL, *ss = NULL;
        if (s != NULL) ECDSA_SIG_get0(s, &sr, &ss);
        if (s != NULL && BN_cmp(ss, half) <= 0) {
            lean_inc(der);
            r = some(der);
        } else if (s != NULL && (low = BN_new()) != NULL && BN_sub(low, order, ss) == 1) {
            BIGNUM *r2 = BN_dup(sr);
            if (r2 != NULL && ECDSA_SIG_set0(s, r2, low) == 1) {
                low = NULL; /* owned by `s` now */
                unsigned char *re = NULL;
                int n = i2d_ECDSA_SIG(s, &re);
                if (n > 0) r = some(mk_bytes(re, (size_t)n));
                OPENSSL_free(re);
            } else {
                BN_free(r2);
            }
        }
    }
    BN_free(low);
    BN_free(half);
    BN_free(order);
    ECDSA_SIG_free(s);
    lean_dec(raw);
    EVP_PKEY_free(k);
    return lean_io_result_mk_ok(r);
}

/* Verify a strict-DER, low-S signature over SHA-256(msg). A high S, a
   non-canonical DER, or a point off the curve gives 0. */
LEAN_EXPORT uint8_t leanp2p_secp256k1_verify(b_lean_obj_arg point, b_lean_obj_arg msg,
                                             b_lean_obj_arg sig) {
    EVP_PKEY *k = k1_public(point);
    BIGNUM *order = NULL, *half = NULL;
    ECDSA_SIG *s = parse_sig_strict(bptr(sig), blen(sig));
    int ok = 0;
    if (k != NULL && s != NULL && ec_half_order(k, &order, &half)) {
        const BIGNUM *ss = NULL;
        ECDSA_SIG_get0(s, NULL, &ss);
        ok = BN_cmp(ss, half) <= 0 && verify_sha256(k, msg, sig);
    }
    ECDSA_SIG_free(s);
    BN_free(half);
    BN_free(order);
    EVP_PKEY_free(k);
    return ok;
}

/* ------------------------------------------------------------------ */
/* Key generation (IO: every function draws from the DRBG)             */
/* ------------------------------------------------------------------ */

/* Each generator gives the private key in the form the matching
   binding above takes, so a fresh key feeds straight into derive,
   sign, and verify. `none` is a library fault. */

static lean_object *raw_private_of(EVP_PKEY *k) {
    lean_object *out = alloc_bytes(32);
    size_t n = 32;
    int ok = k != NULL && EVP_PKEY_get_raw_private_key(k, lean_sarray_cptr(out), &n) == 1
             && n == 32;
    return some_or_free(ok, out);
}

/* A 32-byte seed: any 32 bytes are a valid Ed25519 seed. */
LEAN_EXPORT lean_obj_res leanp2p_ed25519_generate(lean_obj_arg w) {
    (void)w;
    EVP_PKEY *k = EVP_PKEY_Q_keygen(NULL, NULL, "ED25519");
    lean_object *r = raw_private_of(k);
    EVP_PKEY_free(k);
    return lean_io_result_mk_ok(r);
}

LEAN_EXPORT lean_obj_res leanp2p_x25519_generate(lean_obj_arg w) {
    (void)w;
    EVP_PKEY *k = EVP_PKEY_Q_keygen(NULL, NULL, "X25519");
    lean_object *r = raw_private_of(k);
    EVP_PKEY_free(k);
    return lean_io_result_mk_ok(r);
}

/* The raw 32-byte scalar, in [1, n - 1] by construction. */
LEAN_EXPORT lean_obj_res leanp2p_secp256k1_generate(lean_obj_arg w) {
    (void)w;
    EVP_PKEY *k = EVP_PKEY_Q_keygen(NULL, NULL, "EC", "secp256k1");
    BIGNUM *d = NULL;
    lean_object *out = alloc_bytes(32);
    int ok = k != NULL && EVP_PKEY_get_bn_param(k, OSSL_PKEY_PARAM_PRIV_KEY, &d) == 1
             && BN_bn2binpad(d, lean_sarray_cptr(out), 32) == 32;
    BN_clear_free(d);
    EVP_PKEY_free(k);
    return lean_io_result_mk_ok(some_or_free(ok, out));
}

LEAN_EXPORT lean_obj_res leanp2p_p256_generate(lean_obj_arg w) {
    (void)w;
    EVP_PKEY *k = EVP_PKEY_Q_keygen(NULL, NULL, "EC", "P-256");
    lean_object *r = private_der_of(k);
    EVP_PKEY_free(k);
    return lean_io_result_mk_ok(r);
}

/* `bits` is in [2048, 8192], checked on the Lean side. */
LEAN_EXPORT lean_obj_res leanp2p_rsa_generate(size_t bits, lean_obj_arg w) {
    (void)w;
    EVP_PKEY *k = EVP_PKEY_Q_keygen(NULL, NULL, "RSA", bits);
    lean_object *r = private_der_of(k);
    EVP_PKEY_free(k);
    return lean_io_result_mk_ok(r);
}

/* ------------------------------------------------------------------ */
/* X.509 (RFC 5280)                                                    */
/* ------------------------------------------------------------------ */

/* The X.509 rules (root ARCHITECTURE §4.6, see `required_extension`):
   - the extension the caller names must be present,
   - no extension may appear twice,
   - a critical extension must be the named one or one OpenSSL
     understands.
   The shim reports the validity times and does not judge them, so a
   pure binding never reads the clock. The caller compares the times
   with its `Clock`. */

/* A DER certificate with no trailing bytes, or NULL. */
static X509 *load_cert(b_lean_obj_arg der) {
    if (!fits_int(blen(der))) return NULL;
    const unsigned char *p = bptr(der);
    X509 *x = d2i_X509(NULL, &p, (long)blen(der));
    if (x != NULL && p != bptr(der) + blen(der)) {
        X509_free(x);
        return NULL;
    }
    return x;
}

/* An ASN.1 time as seconds since the Unix epoch. */
static int posix_of(const ASN1_TIME *t, int64_t *out) {
    ASN1_TIME *epoch = ASN1_TIME_set(NULL, 0);
    int days = 0, secs = 0;
    int ok = epoch != NULL && t != NULL && ASN1_TIME_diff(&days, &secs, epoch, t) == 1;
    ASN1_TIME_free(epoch);
    if (ok) *out = (int64_t)days * 86400 + secs;
    return ok;
}

/* The extension `oid` (dotted text) of `x`. NULL in three cases:
   - the extension is missing,
   - any extension appears twice (RFC 5280 §4.2, and Go's parser rejects
     it too),
   - a critical extension is neither `oid` nor one that OpenSSL
     understands.
   The TLS spec asks an endpoint to abort only on the critical
   extensions it does not understand. The Go implementation leaves the
   known ones (basicConstraints, keyUsage, ...) to crypto/x509
   (vendor/go-libp2p/p2p/security/tls/crypto.go, lines 171 to 184). */
static X509_EXTENSION *required_extension(X509 *x, const char *oid) {
    ASN1_OBJECT *want = OBJ_txt2obj(oid, 1);
    X509_EXTENSION *found = NULL;
    int count = X509_get_ext_count(x);
    int ok = want != NULL;
    for (int i = 0; ok && i < count; i++) {
        X509_EXTENSION *e = X509_get_ext(x, i);
        const ASN1_OBJECT *id = X509_EXTENSION_get_object(e);
        for (int j = 0; ok && j < i; j++)
            if (OBJ_cmp(X509_EXTENSION_get_object(X509_get_ext(x, j)), id) == 0) ok = 0;
        if (OBJ_cmp(id, want) == 0)
            found = e;
        else if (X509_EXTENSION_get_critical(e) && !X509_supported_extension(e))
            ok = 0;
    }
    ASN1_OBJECT_free(want);
    return ok ? found : NULL;
}

/* Inspect a certificate: the subject key as SPKI DER, the value of the
   required extension `oid`, and the NotBefore and NotAfter times. The
   Lean structure `Backend.CertificateRaw` has two object fields and two
   `UInt64` scalars. Lean lays the scalars out after the objects, in
   declaration order. The times cross as the two's-complement bits of an
   int64_t. */
LEAN_EXPORT lean_obj_res leanp2p_x509_inspect(b_lean_obj_arg der, b_lean_obj_arg oid) {
    X509 *x = load_cert(der);
    X509_EXTENSION *e = x != NULL ? required_extension(x, lean_string_cstr(oid)) : NULL;
    int64_t nb = 0, na = 0;
    unsigned char *spki = NULL;
    int spki_len = -1;
    if (e != NULL && posix_of(X509_get0_notBefore(x), &nb)
        && posix_of(X509_get0_notAfter(x), &na))
        spki_len = i2d_X509_PUBKEY(X509_get_X509_PUBKEY(x), &spki);
    lean_object *r = none();
    if (spki_len > 0) {
        const ASN1_OCTET_STRING *v = X509_EXTENSION_get_data(e);
        lean_object *c = lean_alloc_ctor(0, 2, 16);
        lean_ctor_set(c, 0, mk_bytes(spki, (size_t)spki_len));
        lean_ctor_set(c, 1, mk_bytes(ASN1_STRING_get0_data(v), (size_t)ASN1_STRING_length(v)));
        lean_ctor_set_uint64(c, 2 * sizeof(void *), (uint64_t)nb);
        lean_ctor_set_uint64(c, 2 * sizeof(void *) + 8, (uint64_t)na);
        r = some(c);
    }
    OPENSSL_free(spki);
    X509_free(x);
    return r;
}

/* True when the signature algorithm is one Go's crypto/x509 accepts for a
   certificate: a SHA-2 digest (SHA-256, SHA-384, SHA-512), or Ed25519,
   which signs with no separate digest. MD5 and SHA-1 fail, as Go's
   checkSignature fails them. */
static int signature_algorithm_ok(const X509 *x) {
    int md = NID_undef, pk = NID_undef;
    if (X509_get_signature_info((X509 *)x, &md, &pk, NULL, NULL) != 1) return 0;
    if (pk == NID_ED25519) return 1;
    return md == NID_sha256 || md == NID_sha384 || md == NID_sha512;
}

/* 1 when all three hold (§4.6):
   - the certificate's signature verifies under its own subject key,
   - the algorithm passes `signature_algorithm_ok`,
   - an RSA subject key has 2048 to 8192 bits.
   A parse failure gives 0. */
LEAN_EXPORT uint8_t leanp2p_x509_self_signed(b_lean_obj_arg der) {
    X509 *x = load_cert(der);
    EVP_PKEY *k = x != NULL ? X509_get0_pubkey(x) : NULL;
    int ok = k != NULL && signature_algorithm_ok(x)
        && (!EVP_PKEY_is_a(k, "RSA") || rsa_size_ok(k))
        && X509_verify(x, k) == 1;
    X509_free(x);
    return ok;
}
