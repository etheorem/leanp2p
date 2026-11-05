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
§4.6. It runs the build checks for the four families and pins each
family that passes them. For a family that fails, this package's shim
is the interim fallback. Keccak-256 is the exception: no own shim
exists for it, so a failed pin blocks W6.1 (§4.6). The milestones
record the outcome for each primitive.

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1a | W1.2 | the shim `c/p2pcrypto.c`, its `lakefile.lean` build target, the v4.34 build checks for `LeanHazmatSecp256k1`, `LeanHazmatP256`, `LeanHazmatSha256`, and `LeanHazmatKeccak` with a pin for each family that passes them, `Backend/Error.lean`, and the binding modules `Backend/Sym.lean` and `Backend/Sign.lean`, with every `@&` argument written at the binding | the 1a milestones below pass |
| 1b | W1.2, 1a | the verifier strictness wired to its regressions, `Backend/X509.lean`, and the key-generation bindings of the §3.6 `IO` list | the 1b milestones below pass, and the root W3.2 row holds |
| 2 | W3.1, 1 | the backend side of root W3.3: the facade file at the group root (`packages/crypto/Crypto.lean`) names the production implementations, the `Rng` seam lands beside it, and the cross-check runs at the IO edge | the root W3.3 row holds |

Unit 0 is done. Unit 2 writes no code in this package beyond what the
facade re-exports; its new work is the facade library, the seam, and
the backend side of the cross-check. The facade pair
(`packages/crypto/docs/`) records the suites (the test split below).

## Consumers

W5.1 (`libp2p/identity`) re-derives public keys and verifies signatures
through the facade, and it owns the key forms this package passes as
opaque bytes. W5.3 (Noise) consumes X25519, ChaCha20-Poly1305,
SHA-256, HMAC, and HKDF through the facade, all through one import of
`Crypto`; it draws its ephemerals through the `Rng` seam.
W5.6 (`libp2p/host`) signs and verifies through the facade. W6.1
(`libp2p/identity` ENR) consumes the keccak-256 digest through the
facade; the digest routes to `LeanHazmatKeccak` (§4.6). It signs a
record through the secp256k1 compact digest signer, and it recovers a key
through `LeanHazmatSecp256k1`. The `Rng`
seam is the test-seam home: a seeded value replays a
fixed sequence, so every suite above this package pins its randomness
(§3.1).

## Test milestones

Behavior tests close the units. The suite follows the root test-runner
layout of W0.2, and the `-N1` pass is required. Every case is concrete.
The byte-level known-answer tests for the FFI bindings live in this
package's suites. The FFI-versus-pure comparisons live in the W3.3
cross-check, `Tests/CryptoCross.lean`, the one module that imports both
implementations (facade PLAN).

Milestones for 1a:

- The etheorem pins: one Lake `require` line per family that passes
  the build checks, each at a pinned rev with `subDir :=
  packages/hazmat/<Pkg>`, and only single-family packages. Three pass
  at the current rev ("Pin outcomes").
- The build prerequisites: the CI runs the monorepo's `just`
  vendor-fetch recipes for the pinned families that need one,
  `LeanHazmatSecp256k1` and `LeanHazmatKeccak`, before `lake build`.
  When this repo pins `LeanHazmatSha256` again, its ISA-L unit joins
  them on x86_64 Linux (it needs `nasm`). A pkg-config check finds the
  system `libcrypto` for the OpenSSL families. An actionable failure
  hint fires when either check fails.
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
  (`sigDeterministic`), and so is the secp256k1 re-sign, because both
  sides use the RFC 6979 nonce. The compact digest signer gives the
  fixture's `(r, s)`. Sixteen more messages check that the two forms
  agree, are low-S, and verify. ECDSA P-256 draws a random nonce, so
  verification is its contract. A scalar of zero and a scalar equal to
  the group order are `invalidKey` under every secp256k1 binding.
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
  pin's build check runs here. A pin that does not build blocks W6.1,
  because this package carries no keccak fallback shim. The suite
  reproduces the well-known digests of the empty string and of `abc`
  as two named fixed cases. The etheorem package's own suite is the
  family's main anchor. The EIP-778 record fixture of the identity
  package (W6.1) pins the end-to-end path through the facade.

### Pin outcomes

The per-primitive record that unit 1 promises, at etheorem rev
`169cf718` (`main`, Lean v4.34.1). This repo is on v4.34.0.
`Tests/HazmatPins.lean` holds the checks.

- `LeanHazmatKeccak`: pinned. It builds on v4.34.0 and gives the empty
  and `abc` digests.
- `LeanHazmatP256`: pinned. It builds and verifies the go ECDSA fixture
  through its raw interface (a 32-byte hash, `r`, `s`, `qx`, `qy`). A
  facade route must split the DER signature and the SPKI key into those
  parts. Unit 2 owns that adapter. `Backend.p256SpkiHead` is the one
  home of the SPKI layout it reads.
- `LeanHazmatSecp256k1`: pinned. It builds, recovers the go fixture's
  key, and verifies the fixture. Its verifier normalizes a high S
  before it verifies, so it accepts the high-S twin of a valid
  signature. The suite pins that behavior. The low-S rule of §4.6
  rejects the twin, so secp256k1 verification stays on this package's
  verifier. The etheorem verifier also takes a 64-byte uncompressed
  key, and the keys here cross as 33-byte compressed points. The
  normalization is deliberate, because the execution layer has no
  low-S rule. Root §4.6 records the split.
- `LeanHazmatSha256`: not pinned, and the interim fallback is in force.
  - Its archive defines empty `__libc_csu_init` and `__libc_csu_fini`
    stubs. They win over the real ones in the toolchain's
    `libc_nonshared.a`.
  - The toolchain's `Scrt1.o` calls `__libc_csu_init` to run the static
    constructors. With the stub, none run. libc++ never builds
    `std::cerr`, and an executable segfaults on its first
    uncaught-error print.
  - Lake links every required package's archive into every executable
    of the workspace, whether or not a module imports it. So the pin
    cannot stay in the build.
  - The stubs work around a system `-L` that the same lakefile puts
    ahead of the toolchain's libraries.

  SHA-256 routes to the backend binding until etheorem drops the stubs.
  The report is etheorem/etheorem#152, and the fix is
  etheorem/etheorem#153.

Milestones for 1b:

- Verifier strictness, one regression per rule. Each of these fails:
  - a P-256 key under the RSA entry point
  - an RSA signature under the ECDSA entry point
  - a compressed and a hybrid P-256 key, since Go's `crypto/x509`
    accepts the uncompressed point only, and OpenSSL loads all three
    forms
  - a 1024-bit RSA key, and a 9216-bit RSA key
  - a high-S secp256k1 signature
  - an expired certificate
  - a certificate with an unknown critical extension

  The spike carried the 1024-bit case and the two cross-entry cases.
  The 9216-bit, high-S, expired, and critical-extension cases are new
  tests. The spike's shim already enforced those rules in C, with no
  committed regression.
- X.509: `tls-ext.json`. The three valid certificates parse and yield
  their extension values, the self-signed check passes, and the invalid
  certificate is rejected. The returned NotBefore and NotAfter times
  match the expected ones, and the suite compares them against literal
  timestamps through a pure comparison. The wiring against the live
  clock belongs to the production caller, which owns the `Clock` seam.
  The peer-id derivation over these certificates closes in
  `libp2p/security` with the TLS extension, deferred per root §8.
  As met (`Tests/BackendX509.lean`): the file carries no expected
  times, so the suite states the literals its DER fields encode
  (`750101130000Z`, `40960101130000Z`). Certificate 4 is a well-formed
  self-signed certificate, and the host-key signature inside its
  extension does not verify. X.509 cannot see that, and this package
  must not know the `SignedKey` and its prefix. So the suite composes
  the backend helpers and verifiers the way the TLS handshake will.
  Certificates 1 to 3 pass, and certificate 4 fails.
- Pure-binding determinism: Ed25519 sign, RSA sign, secp256k1 sign,
  and a ChaCha20-Poly1305 seal give the same output twice on the same
  input. The P-256 sign gives two different outputs across two draws,
  and verification accepts both.
- Key generation: a fresh key of each type, Ed25519, X25519, secp256k1,
  ECDSA P-256, and RSA, derives its public key, signs, and verifies.
- The borrowed-argument regression: a soak test drives 200,000 calls
  through the borrowed path. It passes when the process RSS grows by
  less than a fixed budget over its start. The spike has no committed
  test of this kind. The 14 MB to 526 MB numbers of PRINCIPLES 4.1 were
  review measurements, and the budget sits near the after-fix
  footprint. As met (`Tests/BackendSoak.lean`): fresh 4 KiB inputs
  through six bindings, under a 32 MiB budget. At that input size, the
  leak of any one binding alone exceeds the budget. With the `inspect`
  argument made owned on purpose, the run grew 167.9 MiB and failed.

`Tests/fixtures/backend-strictness.json` holds the generated fixtures
of 1b, and `scripts/gen-backend-fixtures.py` writes them:
- the out-of-range RSA keys
- a secp256k1 SPKI key
- a P-256 SEC1 key with a compressed public point
- the certificates that each break one rule, among them a critical
  `basicConstraints` that must pass, a duplicated extension, a SHA-1
  self-signature, and a 1024-bit RSA subject key

The keys are random, so a rerun gives new bytes. The fixtures
therefore stay outside the provenance-gated `Tests/vectors/` corpus,
and the file records the tool and the date.

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
- The facade check: one import of `Crypto` resolves every family of
  the package's public surface, and no caller module imports
  `Backend`. The `liftShim` helper and the P-256 SPKI layout helpers
  serve the group itself, and the facade leaves them out.

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
randomized P-256 signature has no known answer; the fixture suites and
the verifier regressions close it, and a captured hostile-signature
suite would close it harder. Both secp256k1 signers have one: the go
fixture, which go-libp2p signs by RFC 6979.

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
