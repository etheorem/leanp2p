# leanp2p backend: plan

This plan refines the root `docs/PLAN.md` for `crypto/backend`. The root
plan owns the order across packages (PLAN.md, "How to read this plan").
Unit 1 below is the root unit W3.2, and W1.2 is its root dependency.
Unit 2 is the backend side of the root unit W3.3, whose other dependency
is W3.1 (`crypto/pure`). The done-when of each unit is the root row
plus the root definition of done: the surface follows ARCHITECTURE §4.6
and §7 row 7, the owned contracts hold, the carried tests pass under
`+RTS -N1`, and the import lint is green. The shim compiles through the
package's `lakefile.lean` target. OpenSSL 3 is the shim's library, and
further C dependencies follow the FFI-first rule (CLAUDE.md,
"Dependencies").

## Units

Unit 1 splits into two sub-units: 1a closes on the fixture suites, and
1b closes on the verifier-strictness regressions and the X.509 suite.
`crypto/pure` set the pattern. Unit 1 also lands the etheorem pins of
§4.6: four primitives route there, and this package's shim is the
interim fallback for a pin that does not build. Keccak-256 is the
exception: no own shim exists for it, so a failed pin blocks W6.1
(§4.6). The per-primitive outcome is recorded under the milestones.

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1a | W1.2 | the shim `c/p2pcrypto.c`, its `lakefile.lean` build target, the pins for `LeanHazmatSecp256k1`, `LeanHazmatP256`, `LeanHazmatSha256`, and `LeanHazmatKeccak` with the v4.34 build checks, `Backend/Error.lean`, and the binding modules `Backend/Sym.lean` and `Backend/Sign.lean`, with every `@&` argument written at the binding | the 1a milestones below pass |
| 1b | W1.2, 1a | the verifier strictness wired to its regressions, `Backend/X509.lean`, and the key-generation bindings of the §3.6 `IO` list | the 1b milestones below pass, and the root W3.2 row holds |
| 2 | W3.1, 1 | the backend side of root W3.3: the facade file at the group root (`packages/crypto/Crypto.lean`) names the production implementations, the `Rng` seam lands beside it, and the cross-check runs at the IO edge | the root W3.3 row holds |

Unit 0 is done. Unit 2 writes no code in this package beyond what the
facade re-exports; its new work is the facade library, the seam, and
the backend side of the cross-check, whose suite lives in the pure
pair (the test split below).

## Consumers

W5.1 (`libp2p/identity`) re-derives public keys and verifies signatures
through the facade, and it owns the key forms this package passes as
opaque bytes. W5.3 (Noise) consumes X25519, ChaCha20-Poly1305,
SHA-256, HMAC, and HKDF through the facade, all through one import of
`Crypto`; it draws its ephemerals through the `Rng` seam.
W5.6 (`libp2p/host`) signs and verifies through the facade. W6.1
(`libp2p/identity` ENR) consumes the keccak-256 digest through the
facade; the digest routes to `LeanHazmatKeccak` (§4.6). The `Rng`
seam is the test-seam home: a seeded value replays a
fixed sequence, so every suite above this package pins its randomness
(§3.1).

## Test milestones

Behavior tests close the units. The suite follows the root test-runner
layout of W0.2, and the `-N1` pass is required. Every case is concrete.
The byte-level known-answer tests for the FFI bindings live in this
package's suites. The FFI-versus-pure comparisons live in the pure
package's cross-check (W3.3), the one place that imports both stories.

Milestones for 1a:

- The etheorem pins: four Lake `require` lines, one per routed
  family, each at a pinned rev with `subDir :=
  packages/hazmat/<Pkg>`, and only single-family packages.
- The build prerequisites: the CI runs the monorepo's `just`
  vendor-fetch recipes for `LeanHazmatSecp256k1`,
  `LeanHazmatKeccak`, and, on x86_64 Linux, the ISA-L unit of
  `LeanHazmatSha256` (which needs `nasm`) before `lake build`. A
  pkg-config check finds the system `libcrypto` for the OpenSSL
  families. An actionable failure hint fires when either check
  fails.
- Ed25519: the RFC 8032 vectors of `keys-rfc8032.json`, the file's four
  entries (TEST 1, empty; TEST 2; TEST 1024; SHA(abc)): the derived
  public key matches `pubHex`, the signature matches `sigHex`, and a
  tampered message fails verification.
- ChaCha20-Poly1305: the RFC 8439 §2.8.2 vector, which the spike pinned
  inline in its Noise suite: the seal matches byte for byte, the open
  returns the plaintext, and a wrong AD and a wrong nonce each fail.
- The three key types of `keys-go-libp2p.json` (raw key material, see
  "Vector stance"): derive, sign, and verify over the fixed message of
  the file. The RSA signature is byte-identical on re-sign
  (`sigDeterministic`). For secp256k1 and ECDSA the verification is the
  contract, because OpenSSL randomizes the nonce; the file's note
  records the go divergence.
- Random bytes: the requested length comes back, two draws differ, and
  the shim's 1 MiB cap rejects more.
- The SHA-1, SHA-512, HMAC, HKDF, and interim SHA-256 bindings get one
  smoke call each; their real
  closure is the unit 2 cross-check.
- SHA-1: the binding reproduces the `sha1` case of the multihash
  spec vectors in `multihash-examples.json`, the family the pure
  pair's plan already anchors. The empty input has no captured SHA-1
  vector, so the suite adds the well-known empty-input digest as one
  named fixed case. The binding enters the unit 2 cross-check, so
  the family is no longer closed by vectors alone.
- Keccak-256: the production path is `LeanHazmatKeccak` (§4.6). The
  pin's build check runs here, and a pin that does not build blocks
  W6.1, because this package carries no keccak fallback shim. The
  suite reproduces the well-known digests of the empty string and of
  `abc`, stated as two named fixed cases; the etheorem package's own
  suite is the family's main anchor. The EIP-778 record fixture of
  the identity package (W6.1) pins the end-to-end path through the
  facade.

Milestones for 1b:

- Verifier strictness, one regression per rule: a P-256 key under the
  RSA entry point fails; an RSA signature under the ECDSA entry point
  fails; a 1024-bit RSA key fails; a 9216-bit RSA key fails; a high-S
  secp256k1 signature fails; an expired certificate fails; a certificate
  with an unknown critical extension fails. The spike carried the
  1024-bit case and the two cross-entry cases. The 9216-bit, high-S,
  expired, and critical-extension cases are new tests over rules the
  spike's shim already enforced in C without a committed regression.
- X.509: `tls-ext.json`. The three valid certificates parse and yield
  their extension values, the self-signed check passes, and the invalid
  certificate is rejected. The returned NotBefore and NotAfter times
  match the expected ones, and the suite compares them against literal
  timestamps through a pure comparison. The wiring against the live
  clock belongs to the production caller, which owns the `Clock` seam.
  The peer-id derivation over these certificates closes in
  `libp2p/security` with the TLS extension, deferred per root §8.
- Pure-binding determinism: Ed25519 sign, RSA sign, and a
  ChaCha20-Poly1305 seal give the same output twice on the same input.
  A randomized sign gives two different outputs across two draws, and
  verification accepts both.
- Key generation: a fresh key of each type, Ed25519, X25519, secp256k1,
  ECDSA P-256, and RSA, derives its public key, signs, and verifies.
- The borrowed-argument regression: a soak test that drives 200,000
  calls through the borrowed path, and the pass condition is that the
  process RSS grows by less than a fixed budget over its start. The
  spike has no committed test of this kind; the 14 MB to 526 MB numbers
  of PRINCIPLES 4.1 were review measurements, and the after-fix
  footprint is the size the budget sits near.

Milestones for unit 2:

- The W3.3 cross-check: only the families both sides implement, so the
  digests, HMAC, and HKDF of `hashes-rfc.json`, the SHA-1 cases of the
  multihash spec vectors, and the key-length and
  size sweeps of the pure plan run through both implementations, and
  the two answers agree at the IO edge. Both directions run: the pure
  copies against the production path and the production path against
  the pure copies. Ed25519,
  ChaCha20-Poly1305, and keccak-256 have no pure copy, so they stay
  vector-pinned, by RFC 8032, RFC 8439, and the keccak fixed cases of
  unit 1a.
- The `Rng` seam: the seeded test value replays its sequence exactly,
  and the production value draws through `randomBytes`.
- The facade check: one import of `Crypto` resolves every name this
  document lists, and no caller module imports `Backend`.

## Vector stance

The spike captured these files, and all of them arrive on `main` through
root W0.3 (ARCHITECTURE §6): `keys-rfc8032.json` (Ed25519, RFC 8032
section 7.1), `keys-go-libp2p.json` (RSA, secp256k1, and ECDSA fixtures
from go-libp2p `core/crypto/test_data`; the `privHex` and `pubHex` of
the file are the protobuf key envelopes of W5.1, and the W0.3 extractor
emits the inner raw key bytes beside them, so this suite consumes the
raw fields without unwrapping anything), `keys-peer-ids.json` (the
peer-ids spec keys; the protobuf framing around them is W5.1's, and
the W0.3 extractor emits the inner raw key bytes beside the framed
ones, so the raw key material feeds these suites without unwrapping
anything), `tls-ext.json` (the four tls.md
certificates), `noise-vectors.json` (the flynn Noise framework entries
for `Noise_XX_25519_ChaChaPoly_SHA256`), and `hashes-rfc.json`, which
the pure pair owns. No Wycheproof suite is captured.

Two families have no captured file of their own. ChaCha20-Poly1305 is
anchored by the RFC 8439 vector inline in the suite, the spike's shape.
X25519 is anchored through the Noise transcripts: a transcript that both
sides complete pins the DH, the AEAD, and the hash together, and
`noise-go-transcript.json` covers the same path against go-libp2p. A
family with no captured vector closes through such a transcript, through
the W3.3 cross-check, or through a generated fixture whose provenance
the file records. The expired-certificate and critical-extension
fixtures are generated that way, since the tls.md set holds none. The
randomized signatures have no RFC 6979 anchor; the fixture suites and
the verifier regressions close them, and a captured hostile-signature
suite would close them harder.

Keccak-256 has no RFC vector file on the spike branch, and the spike
bound none. The production path is `LeanHazmatKeccak` (§4.6); that
package's own test suite and the named fixed
cases of the empty string and `abc` close the family. The ENR record
fixture of W6.1 pins the end-to-end path.

SHA-1 has no RFC vector file on the spike branch either. The multihash
spec vectors of `multihash-examples.json`, the family the pure pair's
plan anchors, pin the binding, and the binding enters the W3.3
cross-check against the pure copy. The family is no longer closed
by vectors alone.
