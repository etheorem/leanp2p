/*
  OpenSSL-backed crypto shim for LeanP2P (VECTOR_TEST_PLAN.md, phase 2
  step 11). Every function has the `leanp2p_` prefix and is bound in
  LeanP2P/Crypto/OpenSsl.lean with `@[extern]` opaque declarations.

  Conventions:
  - ByteArray in  = borrowed `b_lean_obj_arg` (lean_sarray_cptr / size);
  - ByteArray out = `lean_obj_res` built with `mk_ba`;
  - `IO ...`      = trailing world argument, result wrapped in
                    `lean_io_result_mk_ok`;
  - `Option X` out= `none` as box(0), `some x` as ctor(1) holding x;
  - `Bool` out    = box(0) / box(1);
  - `Nat` in      = uint64_t.

  Key-type marshaling follows the peer-ids spec (vendor/specs/peer-ids):
  - Ed25519     raw 32-byte keys, 64-byte signatures (RFC 8032);
  - secp256k1   33-byte compressed public keys, BIP-62 DER signatures
                (low-S normalized), signing hashes SHA-256(message);
  - ECDSA       SEC1 (RFC 5915) or PKCS#8 DER private (auto-detected),
                SPKI (PKIX) DER public, DER signatures over SHA-256(msg)
                (go-libp2p serializes ECDSA private keys as SEC1);
  - RSA         PKCS#1 DER private, SPKI (PKIX) DER public,
                RSASSA-PKCS1-v1_5 over SHA-256(message).
*/
#include <lean/lean.h>
#include <string.h>
#include <openssl/evp.h>
#include <openssl/core_names.h>
#include <openssl/params.h>
#include <openssl/ec.h>
#include <openssl/rsa.h>
#include <openssl/ecdsa.h>
#include <openssl/bn.h>
#include <openssl/kdf.h>
#include <openssl/rand.h>
#include <openssl/err.h>
#include <openssl/x509.h>

/* ------------------------------------------------------------------ */
/* helpers                                                             */

static lean_obj_res mk_ba(const uint8_t *data, size_t len) {
  lean_obj_res ba = lean_mk_empty_byte_array(lean_box(0));
  for (size_t i = 0; i < len; i++)
    ba = lean_byte_array_push(ba, data[i]);
  return ba;
}

/* Some v, as an IO result. */
static lean_obj_res mk_ok_some(lean_obj_res v) {
  lean_obj_res some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, v);
  return lean_io_result_mk_ok(some);
}

/* none, as an IO result. */
static lean_obj_res mk_ok_none(void) {
  return lean_io_result_mk_ok(lean_box(0));
}

static lean_obj_res mk_ok_bool(uint8_t b) {
  return lean_io_result_mk_ok(lean_box(b ? 1 : 0));
}

static void clear_err(void) { ERR_clear_error(); }

/* ------------------------------------------------------------------ */
/* random, digests, hmac, hkdf                                         */

lean_obj_res leanp2p_random_bytes(uint64_t n, lean_obj_arg w) {
  if (n > (1u << 20)) return mk_ok_none();
  uint8_t buf[64];
  lean_obj_res ba = lean_mk_empty_byte_array(lean_box(0));
  size_t left = (size_t)n;
  while (left > 0) {
    size_t chunk = left < sizeof(buf) ? left : sizeof(buf);
    if (RAND_bytes(buf, (int)chunk) != 1) { clear_err(); lean_dec(ba); return mk_ok_none(); }
    for (size_t i = 0; i < chunk; i++) ba = lean_byte_array_push(ba, buf[i]);
    left -= chunk;
  }
  /* the result type is `Option ByteArray`: wrap the array in `some` */
  return mk_ok_some(ba);
}

/* One-shot digest through EVP; out_len is the digest size. */
static lean_obj_res digest(const EVP_MD *md, b_lean_obj_arg msg) {
  uint8_t out[EVP_MAX_MD_SIZE];
  unsigned int out_len = 0;
  if (EVP_Digest(lean_sarray_cptr(msg), lean_sarray_size(msg),
                 out, &out_len, md, NULL) != 1) { clear_err(); return mk_ok_none(); }
  return mk_ok_some(mk_ba(out, out_len));
}

lean_obj_res leanp2p_sha256(b_lean_obj_arg msg, lean_obj_arg w) {
  return digest(EVP_sha256(), msg);
}

lean_obj_res leanp2p_sha512(b_lean_obj_arg msg, lean_obj_arg w) {
  return digest(EVP_sha512(), msg);
}

lean_obj_res leanp2p_hmac_sha256(b_lean_obj_arg key, b_lean_obj_arg msg,
                                 lean_obj_arg w) {
  uint8_t out[EVP_MAX_MD_SIZE];
  size_t out_len = 0;
  /* EVP_MAC handles any key length, including 0 (RFC 2104 allows it;
     EVP_PKEY_new_raw_private_key rejects it). */
  EVP_MAC *mac = EVP_MAC_fetch(NULL, "HMAC", NULL);
  EVP_MAC_CTX *ctx = mac != NULL ? EVP_MAC_CTX_new(mac) : NULL;
  OSSL_PARAM params[2];
  char digest_name[] = "SHA256";
  params[0] = OSSL_PARAM_construct_utf8_string(OSSL_MAC_PARAM_DIGEST,
                                               digest_name, 0);
  params[1] = OSSL_PARAM_construct_end();
  int ok = ctx != NULL
        && EVP_MAC_init(ctx, lean_sarray_cptr(key), lean_sarray_size(key),
                        params) == 1
        && EVP_MAC_update(ctx, lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1
        && EVP_MAC_final(ctx, out, &out_len, sizeof(out)) == 1;
  EVP_MAC_CTX_free(ctx);
  EVP_MAC_free(mac);
  if (!ok) { clear_err(); return mk_ok_none(); }
  return mk_ok_some(mk_ba(out, out_len));
}

lean_obj_res leanp2p_hkdf_sha256(b_lean_obj_arg salt, b_lean_obj_arg ikm,
                                 b_lean_obj_arg info, uint64_t out_len,
                                 lean_obj_arg w) {
  if (out_len > (1u << 16)) return mk_ok_none();
  EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_HKDF, NULL);
  uint8_t *out = malloc((size_t)out_len);
  size_t len = (size_t)out_len;
  int ok = ctx != NULL && out != NULL
        && EVP_PKEY_derive_init(ctx) == 1
        && EVP_PKEY_CTX_set_hkdf_md(ctx, EVP_sha256()) == 1
        && EVP_PKEY_CTX_set_hkdf_mode(ctx, EVP_PKEY_HKDEF_MODE_EXTRACT_AND_EXPAND) == 1
        && EVP_PKEY_CTX_set1_hkdf_salt(ctx, lean_sarray_cptr(salt),
                                       (int)lean_sarray_size(salt)) == 1
        && EVP_PKEY_CTX_set1_hkdf_key(ctx, lean_sarray_cptr(ikm),
                                      (int)lean_sarray_size(ikm)) == 1
        && EVP_PKEY_CTX_add1_hkdf_info(ctx, lean_sarray_cptr(info),
                                       (int)lean_sarray_size(info)) == 1
        && EVP_PKEY_derive(ctx, out, &len) == 1;
  EVP_PKEY_CTX_free(ctx);
  if (!ok) { free(out); clear_err(); return mk_ok_none(); }
  lean_obj_res ba = mk_ba(out, len);
  free(out);
  return mk_ok_some(ba);
}

/* ------------------------------------------------------------------ */
/* Ed25519 (raw keys per RFC 8032 / peer-ids spec)                     */

lean_obj_res leanp2p_ed25519_pubkey(b_lean_obj_arg seed, lean_obj_arg w) {
  if (lean_sarray_size(seed) != 32) return mk_ok_none();
  EVP_PKEY *pkey = EVP_PKEY_new_raw_private_key(
      EVP_PKEY_ED25519, NULL, lean_sarray_cptr(seed), 32);
  if (pkey == NULL) { clear_err(); return mk_ok_none(); }
  uint8_t pub[32];
  size_t len = sizeof(pub);
  int ok = EVP_PKEY_get_raw_public_key(pkey, pub, &len) == 1;
  EVP_PKEY_free(pkey);
  if (!ok) { clear_err(); return mk_ok_none(); }
  return mk_ok_some(mk_ba(pub, len));
}

lean_obj_res leanp2p_ed25519_sign(b_lean_obj_arg seed, b_lean_obj_arg msg,
                                  lean_obj_arg w) {
  if (lean_sarray_size(seed) != 32) return mk_ok_none();
  EVP_PKEY *pkey = EVP_PKEY_new_raw_private_key(
      EVP_PKEY_ED25519, NULL, lean_sarray_cptr(seed), 32);
  if (pkey == NULL) { clear_err(); return mk_ok_none(); }
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  uint8_t sig[64];
  size_t sig_len = sizeof(sig);
  int ok = ctx != NULL
        && EVP_DigestSignInit(ctx, NULL, NULL, NULL, pkey) == 1
        && EVP_DigestSign(ctx, sig, &sig_len,
                          lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1
        && sig_len == 64;
  EVP_MD_CTX_free(ctx);
  EVP_PKEY_free(pkey);
  if (!ok) { clear_err(); return mk_ok_none(); }
  return mk_ok_some(mk_ba(sig, 64));
}

lean_obj_res leanp2p_ed25519_verify(b_lean_obj_arg pub, b_lean_obj_arg msg,
                                    b_lean_obj_arg sig, lean_obj_arg w) {
  if (lean_sarray_size(pub) != 32 || lean_sarray_size(sig) != 64)
    return mk_ok_bool(0);
  EVP_PKEY *pkey = EVP_PKEY_new_raw_public_key(
      EVP_PKEY_ED25519, NULL, lean_sarray_cptr(pub), 32);
  if (pkey == NULL) { clear_err(); return mk_ok_bool(0); }
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  int ok = ctx != NULL
        && EVP_DigestVerifyInit(ctx, NULL, NULL, NULL, pkey) == 1
        && EVP_DigestVerify(ctx, lean_sarray_cptr(sig), lean_sarray_size(sig),
                            lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1;
  EVP_MD_CTX_free(ctx);
  EVP_PKEY_free(pkey);
  return mk_ok_bool(ok ? 1 : 0);
}

/* ------------------------------------------------------------------ */
/* X25519                                                              */

lean_obj_res leanp2p_x25519_pubkey(b_lean_obj_arg priv, lean_obj_arg w) {
  if (lean_sarray_size(priv) != 32) return mk_ok_none();
  EVP_PKEY *pkey = EVP_PKEY_new_raw_private_key(
      EVP_PKEY_X25519, NULL, lean_sarray_cptr(priv), 32);
  if (pkey == NULL) { clear_err(); return mk_ok_none(); }
  uint8_t pub[32];
  size_t len = sizeof(pub);
  int ok = EVP_PKEY_get_raw_public_key(pkey, pub, &len) == 1;
  EVP_PKEY_free(pkey);
  if (!ok) { clear_err(); return mk_ok_none(); }
  return mk_ok_some(mk_ba(pub, len));
}

lean_obj_res leanp2p_x25519_dh(b_lean_obj_arg priv, b_lean_obj_arg peer_pub,
                               lean_obj_arg w) {
  if (lean_sarray_size(priv) != 32 || lean_sarray_size(peer_pub) != 32)
    return mk_ok_none();
  EVP_PKEY *mine = EVP_PKEY_new_raw_private_key(
      EVP_PKEY_X25519, NULL, lean_sarray_cptr(priv), 32);
  EVP_PKEY *peer = EVP_PKEY_new_raw_public_key(
      EVP_PKEY_X25519, NULL, lean_sarray_cptr(peer_pub), 32);
  EVP_PKEY_CTX *ctx = mine != NULL ? EVP_PKEY_CTX_new(mine, NULL) : NULL;
  uint8_t secret[32];
  size_t len = sizeof(secret);
  int ok = peer != NULL && ctx != NULL
        && EVP_PKEY_derive_init(ctx) == 1
        && EVP_PKEY_derive_set_peer(ctx, peer) == 1
        && EVP_PKEY_derive(ctx, secret, &len) == 1;
  EVP_PKEY_CTX_free(ctx);
  EVP_PKEY_free(mine);
  EVP_PKEY_free(peer);
  if (!ok) { clear_err(); return mk_ok_none(); }
  return mk_ok_some(mk_ba(secret, len));
}

/* ------------------------------------------------------------------ */
/* secp256k1 (Bitcoin EC encoding per peer-ids spec)                   */

/* Derive the compressed public point of a raw private scalar with plain
   point multiplication. */
static int ec_mul_pub(int nid, const uint8_t *priv, size_t priv_len,
                      uint8_t *out, size_t out_len) {
  EC_GROUP *grp = EC_GROUP_new_by_curve_name(nid);
  BIGNUM *d = grp != NULL ? BN_bin2bn(priv, (int)priv_len, NULL) : NULL;
  EC_POINT *pt = (grp != NULL && d != NULL) ? EC_POINT_new(grp) : NULL;
  int ok = pt != NULL
        && EC_POINT_mul(grp, pt, d, NULL, NULL, NULL) == 1
        && EC_POINT_is_at_infinity(grp, pt) == 0
        && EC_POINT_point2oct(grp, pt, POINT_CONVERSION_COMPRESSED, out,
                              out_len, NULL) == (int)out_len;
  EC_POINT_free(pt); BN_free(d); EC_GROUP_free(grp);
  if (!ok) clear_err();
  return ok;
}

/* OSSL_PARAM integers are stored in NATIVE byte order; our scalars are
   big-endian. Convert safely for the current platform. */
static void be_to_native(uint8_t *dst, const uint8_t *be, size_t n) {
  const uint16_t probe = 1;
  const int little = *(const uint8_t *)&probe == 1;
  for (size_t i = 0; i < n; i++)
    dst[i] = little ? be[n - 1 - i] : be[i];
}

/* Build an EVP EC keypair on `curve` from a raw private scalar. OpenSSL 3
   rejects a KEYPAIR import that carries only the private scalar, so the
   public point is derived here and imported alongside it. The private
   scalar must be an integer-type (BN) param for the EC provider. */
static EVP_PKEY *ec_key_from_priv(const char *curve, int nid,
                                  const uint8_t *priv, size_t priv_len) {
  uint8_t pub[33];
  if (!ec_mul_pub(nid, priv, priv_len, pub, sizeof(pub))) return NULL;
  char name[32];
  snprintf(name, sizeof(name), "%s", curve);
  uint8_t priv_native[66];
  if (priv_len > sizeof(priv_native)) return NULL;
  be_to_native(priv_native, priv, priv_len);
  OSSL_PARAM params[4];
  params[0] = OSSL_PARAM_construct_utf8_string(
      OSSL_PKEY_PARAM_GROUP_NAME, name, 0);
  params[1] = OSSL_PARAM_construct_BN(
      OSSL_PKEY_PARAM_PRIV_KEY, priv_native, priv_len);
  params[2] = OSSL_PARAM_construct_octet_string(
      OSSL_PKEY_PARAM_PUB_KEY, pub, 33);
  params[3] = OSSL_PARAM_construct_end();
  EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_name(NULL, "EC", NULL);
  EVP_PKEY *pkey = NULL;
  int ok = ctx != NULL
        && EVP_PKEY_fromdata_init(ctx) == 1
        && EVP_PKEY_fromdata(ctx, &pkey, EVP_PKEY_KEYPAIR, params) == 1
        && pkey != NULL;
  EVP_PKEY_CTX_free(ctx);
  if (!ok) { EVP_PKEY_free(pkey); clear_err(); return NULL; }
  return pkey;
}

/* Build an EVP EC key on `curve` from a compressed/uncompressed point. */
static EVP_PKEY *ec_key_from_pub(const char *curve,
                                 const uint8_t *pub, size_t pub_len) {
  char name[32];
  snprintf(name, sizeof(name), "%s", curve);
  OSSL_PARAM params[3];
  params[0] = OSSL_PARAM_construct_utf8_string(
      OSSL_PKEY_PARAM_GROUP_NAME, name, 0);
  params[1] = OSSL_PARAM_construct_octet_string(
      OSSL_PKEY_PARAM_PUB_KEY, (void *)pub, pub_len);
  params[2] = OSSL_PARAM_construct_end();
  EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_name(NULL, "EC", NULL);
  EVP_PKEY *pkey = NULL;
  int ok = ctx != NULL
        && EVP_PKEY_fromdata_init(ctx) == 1
        && EVP_PKEY_fromdata(ctx, &pkey, EVP_PKEY_PUBLIC_KEY, params) == 1
        && pkey != NULL;
  EVP_PKEY_CTX_free(ctx);
  if (!ok) { EVP_PKEY_free(pkey); clear_err(); return NULL; }
  return pkey;
}

lean_obj_res leanp2p_secp256k1_pubkey(b_lean_obj_arg scalar, lean_obj_arg w) {
  if (lean_sarray_size(scalar) != 32) return mk_ok_none();
  uint8_t pub[33];
  if (!ec_mul_pub(NID_secp256k1, lean_sarray_cptr(scalar), 32, pub, 33))
    return mk_ok_none();
  return mk_ok_some(mk_ba(pub, 33));
}

/* BIP-62: normalize the S half to the low value (s > n/2 -> n - s). */
static uint8_t *der_sig_low_s(const uint8_t *der, size_t der_len,
                              size_t *out_len) {
  const unsigned char *p = der;
  ECDSA_SIG *sig = d2i_ECDSA_SIG(NULL, &p, (long)der_len);
  if (sig == NULL) { clear_err(); return NULL; }
  const BIGNUM *r = ECDSA_SIG_get0_r(sig);
  const BIGNUM *s = ECDSA_SIG_get0_s(sig);
  BIGNUM *order = BN_new(), *half = BN_new();
  EC_GROUP *grp = EC_GROUP_new_by_curve_name(NID_secp256k1);
  int ok = grp != NULL && order != NULL && half != NULL
        && EC_GROUP_get_order(grp, order, NULL) == 1
        && BN_rshift1(half, order);
  if (ok && BN_cmp(s, half) > 0) {
    BIGNUM *s2 = BN_dup(s);
    ok = s2 != NULL && BN_sub(s2, order, s2) == 1
          && ECDSA_SIG_set0(sig, BN_dup(r), s2) == 1;
  }
  uint8_t *buf = NULL;
  if (ok) {
    int n = i2d_ECDSA_SIG(sig, &buf);
    ok = n > 0;
    if (ok) *out_len = (size_t)n;
  }
  EC_GROUP_free(grp); BN_free(order); BN_free(half);
  ECDSA_SIG_free(sig);
  if (!ok) { OPENSSL_free(buf); clear_err(); return NULL; }
  return buf;
}

lean_obj_res leanp2p_secp256k1_sign(b_lean_obj_arg scalar, b_lean_obj_arg msg,
                                    lean_obj_arg w) {
  if (lean_sarray_size(scalar) != 32) return mk_ok_none();
  EVP_PKEY *pkey = ec_key_from_priv("secp256k1", NID_secp256k1,
                                    lean_sarray_cptr(scalar), 32);
  if (pkey == NULL) return mk_ok_none();
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  size_t der_len = 0;
  int ok = ctx != NULL
        && EVP_DigestSignInit(ctx, NULL, EVP_sha256(), NULL, pkey) == 1
        && EVP_DigestSign(ctx, NULL, &der_len,
                          lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1;
  uint8_t *der = ok ? malloc(der_len) : NULL;
  ok = ok && der != NULL
        && EVP_DigestSign(ctx, der, &der_len,
                          lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1;
  EVP_MD_CTX_free(ctx);
  EVP_PKEY_free(pkey);
  if (!ok) { free(der); clear_err(); return mk_ok_none(); }
  size_t low_len = 0;
  uint8_t *low = der_sig_low_s(der, der_len, &low_len);
  free(der);
  if (low == NULL) return mk_ok_none();
  lean_obj_res ba = mk_ba(low, low_len);
  OPENSSL_free(low);
  return mk_ok_some(ba);
}

lean_obj_res leanp2p_secp256k1_verify(b_lean_obj_arg pub, b_lean_obj_arg msg,
                                      b_lean_obj_arg sig, lean_obj_arg w) {
  if (lean_sarray_size(pub) != 33) return mk_ok_bool(0);
  EVP_PKEY *pkey = ec_key_from_pub("secp256k1", lean_sarray_cptr(pub), 33);
  if (pkey == NULL) return mk_ok_bool(0);
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  int ok = ctx != NULL
        && EVP_DigestVerifyInit(ctx, NULL, EVP_sha256(), NULL, pkey) == 1
        && EVP_DigestVerify(ctx, lean_sarray_cptr(sig), lean_sarray_size(sig),
                            lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1;
  EVP_MD_CTX_free(ctx);
  EVP_PKEY_free(pkey);
  return mk_ok_bool(ok ? 1 : 0);
}

/* ------------------------------------------------------------------ */
/* ECDSA P-256 and RSA (DER key forms per peer-ids spec)               */

/* Import a DER private key (PKCS#8 or PKCS#1, auto-detected). */
static EVP_PKEY *priv_from_der(b_lean_obj_arg der) {
  const unsigned char *p = lean_sarray_cptr(der);
  EVP_PKEY *pkey = d2i_AutoPrivateKey(NULL, &p, (long)lean_sarray_size(der));
  if (pkey == NULL) clear_err();
  return pkey;
}

/* Export a key as SPKI (PKIX) DER. */
static uint8_t *pub_to_spki_der(EVP_PKEY *pkey, size_t *der_len) {
  int n = i2d_PUBKEY(pkey, NULL);
  if (n <= 0) { clear_err(); return NULL; }
  uint8_t *der = malloc((size_t)n);
  unsigned char *pp = der;
  if (i2d_PUBKEY(pkey, &pp) != n) { free(der); clear_err(); return NULL; }
  *der_len = (size_t)n;
  return der;
}

static EVP_PKEY *pub_from_spki_der(b_lean_obj_arg der) {
  const unsigned char *p = lean_sarray_cptr(der);
  EVP_PKEY *pkey = d2i_PUBKEY(NULL, &p, (long)lean_sarray_size(der));
  if (pkey == NULL) clear_err();
  return pkey;
}

/* Generic EVP sign/verify helpers (PKCS#1 v1.5 for RSA, DER for EC). */
static lean_obj_res evp_sign(EVP_PKEY *pkey, const EVP_MD *md,
                             b_lean_obj_arg msg) {
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  size_t sig_len = 0;
  int ok = ctx != NULL
        && EVP_DigestSignInit(ctx, NULL, md, NULL, pkey) == 1
        && EVP_DigestSign(ctx, NULL, &sig_len,
                          lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1;
  uint8_t *sig = ok ? malloc(sig_len) : NULL;
  ok = ok && sig != NULL
        && EVP_DigestSign(ctx, sig, &sig_len,
                          lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1;
  EVP_MD_CTX_free(ctx);
  if (!ok) { free(sig); clear_err(); return mk_ok_none(); }
  lean_obj_res ba = mk_ba(sig, sig_len);
  free(sig);
  return mk_ok_some(ba);
}

static int evp_verify(EVP_PKEY *pkey, const EVP_MD *md,
                      b_lean_obj_arg msg, b_lean_obj_arg sig) {
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  int ok = ctx != NULL
        && EVP_DigestVerifyInit(ctx, NULL, md, NULL, pkey) == 1
        && EVP_DigestVerify(ctx, lean_sarray_cptr(sig), lean_sarray_size(sig),
                            lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1;
  EVP_MD_CTX_free(ctx);
  return ok ? 1 : 0;
}

lean_obj_res leanp2p_ecdsa_p256_priv_to_pub(b_lean_obj_arg pkcs8,
                                            lean_obj_arg w) {
  EVP_PKEY *pkey = priv_from_der(pkcs8);
  if (pkey == NULL) return mk_ok_none();
  size_t der_len = 0;
  uint8_t *der = pub_to_spki_der(pkey, &der_len);
  EVP_PKEY_free(pkey);
  if (der == NULL) return mk_ok_none();
  lean_obj_res ba = mk_ba(der, der_len);
  free(der);
  return mk_ok_some(ba);
}

lean_obj_res leanp2p_ecdsa_p256_sign(b_lean_obj_arg pkcs8, b_lean_obj_arg msg,
                                     lean_obj_arg w) {
  EVP_PKEY *pkey = priv_from_der(pkcs8);
  if (pkey == NULL) return mk_ok_none();
  lean_obj_res r = evp_sign(pkey, EVP_sha256(), msg);
  EVP_PKEY_free(pkey);
  return r;
}

lean_obj_res leanp2p_ecdsa_p256_verify(b_lean_obj_arg spki, b_lean_obj_arg msg,
                                       b_lean_obj_arg sig, lean_obj_arg w) {
  EVP_PKEY *pkey = pub_from_spki_der(spki);
  if (pkey == NULL) return mk_ok_bool(0);
  int ok = evp_verify(pkey, EVP_sha256(), msg, sig);
  EVP_PKEY_free(pkey);
  return mk_ok_bool(ok);
}

lean_obj_res leanp2p_rsa_priv_to_pub(b_lean_obj_arg pkcs1, lean_obj_arg w) {
  EVP_PKEY *pkey = priv_from_der(pkcs1);
  if (pkey == NULL) return mk_ok_none();
  size_t der_len = 0;
  uint8_t *der = pub_to_spki_der(pkey, &der_len);
  EVP_PKEY_free(pkey);
  if (der == NULL) return mk_ok_none();
  lean_obj_res ba = mk_ba(der, der_len);
  free(der);
  return mk_ok_some(ba);
}

lean_obj_res leanp2p_rsa_sign(b_lean_obj_arg pkcs1, b_lean_obj_arg msg,
                              lean_obj_arg w) {
  EVP_PKEY *pkey = priv_from_der(pkcs1);
  if (pkey == NULL) return mk_ok_none();
  lean_obj_res r = evp_sign(pkey, EVP_sha256(), msg);
  EVP_PKEY_free(pkey);
  return r;
}

lean_obj_res leanp2p_rsa_verify(b_lean_obj_arg spki, b_lean_obj_arg msg,
                                b_lean_obj_arg sig, lean_obj_arg w) {
  EVP_PKEY *pkey = pub_from_spki_der(spki);
  if (pkey == NULL) return mk_ok_bool(0);
  int ok = evp_verify(pkey, EVP_sha256(), msg, sig);
  EVP_PKEY_free(pkey);
  return mk_ok_bool(ok);
}

/* ------------------------------------------------------------------ */
/* ChaCha20-Poly1305 (VECTOR_TEST_PLAN.md, phase 3 step 16: Noise)     */
/*                                                                     */
/* Noise's CipherState nonce is 64-bit: the AEAD nonce is 4 zero bytes  */
/* followed by the little-endian 64-bit counter (built on the Lean      */
/* side); here it is a plain 12-byte value. Ciphertext layout is        */
/* `plaintext || 16-byte tag` (encrypt) and the same layout expected    */
/* on decrypt, where authentication failure yields `none`.              */

static lean_obj_res chacha(int enc, b_lean_obj_arg key, b_lean_obj_arg nonce,
                           b_lean_obj_arg ad, b_lean_obj_arg in) {
  if (lean_sarray_size(key) != 32 || lean_sarray_size(nonce) != 12)
    return mk_ok_none();
  EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
  int ok = ctx != NULL
        && EVP_CipherInit_ex(ctx, EVP_chacha20_poly1305(), NULL, NULL, NULL,
                             enc) == 1
        && EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_IVLEN, 12, NULL) == 1
        && EVP_CipherInit_ex(ctx, NULL, NULL, lean_sarray_cptr(key),
                             lean_sarray_cptr(nonce), enc) == 1;
  int outlen = 0;
  if (ok && lean_sarray_size(ad) > 0)
    ok = EVP_CipherUpdate(ctx, NULL, &outlen, lean_sarray_cptr(ad),
                          (int)lean_sarray_size(ad)) == 1;
  /* decrypt: the trailing 16 bytes of `in` are the tag */
  size_t body = lean_sarray_size(in);
  if (enc == 0) {
    if (body < 16) { EVP_CIPHER_CTX_free(ctx); return mk_ok_none(); }
    body -= 16;
    ok = ok && EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_TAG, 16,
                                   (void *)((uintptr_t)lean_sarray_cptr(in)
                                            + body)) == 1;
  }
  uint8_t *out = ok ? malloc(body + 16) : NULL;
  size_t total = 0;
  ok = ok && out != NULL
        && EVP_CipherUpdate(ctx, out, &outlen, lean_sarray_cptr(in),
                            (int)body) == 1;
  total = (size_t)outlen;
  ok = ok && EVP_CipherFinal_ex(ctx, out + total, &outlen) == 1;
  total += (size_t)outlen;
  /* encrypt: fetch the tag (the generic interface never appends it) and
     hand back `ciphertext || tag` */
  if (ok && enc == 1) {
    ok = EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_GET_TAG, 16,
                             out + total) == 1;
    total += 16;
  }
  EVP_CIPHER_CTX_free(ctx);
  if (!ok) { free(out); clear_err(); return mk_ok_none(); }
  lean_obj_res ba = mk_ba(out, total);
  free(out);
  return mk_ok_some(ba);
}

lean_obj_res leanp2p_chacha20poly1305_seal(b_lean_obj_arg key,
                                           b_lean_obj_arg nonce,
                                           b_lean_obj_arg ad,
                                           b_lean_obj_arg plaintext,
                                           lean_obj_arg w) {
  return chacha(1, key, nonce, ad, plaintext);
}

lean_obj_res leanp2p_chacha20poly1305_open(b_lean_obj_arg key,
                                           b_lean_obj_arg nonce,
                                           b_lean_obj_arg ad,
                                           b_lean_obj_arg ciphertext,
                                           lean_obj_arg w) {
  return chacha(0, key, nonce, ad, ciphertext);
}

/* ------------------------------------------------------------------ */
/* X.509 libp2p certificate extension (phase 3 step 17, tls.md)        */
/*                                                                     */
/* The extension has OID 1.3.6.1.4.1.53594.1.1 and carries the DER of   */
/* the SignedKey structure. The certs the spec's vectors use are        */
/* self-signed, so validation also needs a check of the certificate     */
/* signature against the certificate's own public key.                  */

#define LIBP2P_TLS_OID "1.3.6.1.4.1.53594.1.1"

/* (spkiDer, extValue) for the libp2p extension of a certificate DER. */
lean_obj_res leanp2p_x509_libp2p_ext(b_lean_obj_arg der, lean_obj_arg w) {
  const unsigned char *p = lean_sarray_cptr(der);
  X509 *x = d2i_X509(NULL, &p, (long)lean_sarray_size(der));
  ASN1_OBJECT *oid = x != NULL ? OBJ_txt2obj(LIBP2P_TLS_OID, 1) : NULL;
  int idx = (x != NULL && oid != NULL) ? X509_get_ext_by_OBJ(x, oid, -1) : -1;
  X509_EXTENSION *ext = (x != NULL && idx >= 0) ? X509_get_ext(x, idx) : NULL;
  ASN1_OCTET_STRING *val = ext != NULL ? X509_EXTENSION_get_data(ext) : NULL;
  EVP_PKEY *pk = (x != NULL) ? X509_get0_pubkey(x) : NULL;
  int spki_len = (pk != NULL) ? i2d_PUBKEY(pk, NULL) : -1;
  if (val == NULL || spki_len <= 0) {
    if (x != NULL) X509_free(x);
    if (oid != NULL) ASN1_OBJECT_free(oid);
    clear_err();
    return mk_ok_none();
  }
  uint8_t *spki = malloc((size_t)spki_len);
  unsigned char *pp = spki;
  int n = spki != NULL ? i2d_PUBKEY(pk, &pp) : -1;
  if (n != spki_len) {
    free(spki); X509_free(x); ASN1_OBJECT_free(oid); clear_err();
    return mk_ok_none();
  }
  lean_obj_res baSpki = mk_ba(spki, (size_t)spki_len);
  lean_obj_res baVal = mk_ba(ASN1_STRING_get0_data(val),
                             (size_t)ASN1_STRING_length(val));
  free(spki);
  ASN1_OBJECT_free(oid);
  X509_free(x);
  /* `Option (ByteArray × ByteArray)`: some (ctor 1) holding a pair
     (structure ctor 0 with two object fields) */
  lean_obj_res pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, baSpki);
  lean_ctor_set(pair, 1, baVal);
  return mk_ok_some(pair);
}

/* Is the certificate DER self-signed (signature valid under its own key)?
   The tls.md vectors are self-signed; full chain validation is out of
   scope for the vector suite. */
lean_obj_res leanp2p_x509_self_signed(b_lean_obj_arg der, lean_obj_arg w) {
  const unsigned char *p = lean_sarray_cptr(der);
  X509 *x = d2i_X509(NULL, &p, (long)lean_sarray_size(der));
  if (x == NULL) { clear_err(); return mk_ok_bool(0); }
  EVP_PKEY *pk = X509_get0_pubkey(x);
  int ok = pk != NULL && X509_verify(x, pk) == 1;
  X509_free(x);
  clear_err();
  return mk_ok_bool(ok ? 1 : 0);
}
