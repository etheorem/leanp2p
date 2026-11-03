# leanp2p backend: architecture

`crypto/backend` binds OpenSSL 3 through a small C shim and `@[extern]`
declarations. It gives the stack Ed25519, X25519, RSA, secp256k1,
ECDSA P-256, SHA-1, SHA-512, HMAC, HKDF, ChaCha20-Poly1305, and X.509,
plus randomness and key generation. Nobody writes constant-time code
in Lean for it (§4 preamble, §4.6). Every shim entry point carries the
`leanp2p_` prefix, so the auditable-in-one-sitting contract holds.

The package is the "FFI first" phase of the dependency strategy. The
pure package `crypto/pure` is the "Lean later" phase. That pair owns
the oracle side: the pure copies are the audited implementations and
the cross-check oracles. The W3.3 cross-check compares the pure copies
with the production path at the IO edge (§4.6). The production path is
the backend bindings and the etheorem packages for the routed
primitives. This pair owns the binding side, and the bindings are the
production path for every primitive they carry. "Public surface"
records which primitives route to the etheorem hazmat packages, and
the constraints of that split.

## Modules

| Module | Holds, and why |
|---|---|
| `c/p2pcrypto.c` | the shim, one C file over the OpenSSL 3 EVP surface. The spike's is about 770 lines, and it stays auditable in one sitting (PRINCIPLES 4.1). |
| `Backend/Error.lean` | `CryptoError`, the one error inductive of the package (§3.5), and `liftShim`, the one lift of a shim `Option` into it |
| `Backend/Sized.lean` | `Key32`, `Digest32`, and `Nonce12`, the proof-carrying newtypes (§3.7) that cross the FFI edge. `Sym` and `Sign` both take them, so they sit below both. |
| `Backend/Sym.lean` | random bytes, the SHA-1 and SHA-512 digest bindings, the interim SHA-256 binding, HMAC, HKDF, and ChaCha20-Poly1305 seal and open |
| `Backend/Sign.lean` | X25519 derivation and DH. Derive, sign, and verify for Ed25519, RSA, secp256k1, and ECDSA P-256 (P-256 verification is the interim fallback until the facade routes it). The secp256k1 compact signer over a caller's digest. The DER re-encode of an RSA or P-256 private key (`rsaPkcs1`, `p256Sec1`). Key generation for all five types. |
| `Backend/X509.lean` | the certificate helpers of the tls.md shape. `inspect` reads the SPKI, the value of one extension the caller names by OID, and the validity times. `selfSigned` checks the signature. The helpers know no protocol, so the caller passes the libp2p OID. |
| `Backend.lean` | the package root, one import line per submodule. Production callers import `Crypto` instead (§3.6). |

The bindings split into three modules because they carry three
contracts. `Sym` owns the ownership rule and the AEAD failure shape.
`Sign` owns the verifier strictness. `X509` owns the validity and
criticality rules. One module would hold three contract sets under one
docstring, and PRINCIPLES 1.2 says to split there. All declarations
live in the `Backend` namespace.

The shim compiles through a Lake target in this package's
`lakefile.lean`. This is the standing example where `lakefile.lean` is
allowed, because the declarative form cannot express a C build
(PRINCIPLES 4.2, and CLAUDE.md, "Configure, don't integrate"). A Lake
configuration is one file per package, so this directory is a nested
Lake package, and the root `lakefile.toml` requires it by path. The
checkout stays one repository at one rev, so the nesting adds no
version skew (§2). The archive `libleanp2p_backend` crosses the
`require`. Link arguments do not cross it.

OpenSSL 3 is the shim's library today, and further C dependencies
follow the same FFI-first path (CLAUDE.md, "Dependencies"). The shim
compiles against the system OpenSSL 3 headers, which pkg-config finds.
The target fails with an install hint when the headers are absent. The
shim links against the static OpenSSL 3 `libcrypto.a` that the Lean
toolchain bundles and links into every executable (3.6.0 on v4.34.0).
So `lean-toolchain` pins the runtime library. The root names no system
`-L`. With one, the toolchain's `lld` finds the system C library ahead
of the toolchain's glibc, and the link fails.

## Public surface

The families are the ones §7 row 7 names. The table below lists the
ones this package binds itself. The paragraphs after it record the
etheorem families. The binding type of each follows §3.6. The Lean
interface lifts the `Option` of a shim failure to `Except CryptoError`,
once, in this package.

| Family | Binding type | Why |
|---|---|---|
| Ed25519 derive, sign, and verify | pure | Ed25519 signs deterministically (§3.6) |
| X25519 public-key derivation and DH | pure | deterministic (§3.6) |
| RSA derive, re-encode, sign, verify | all pure | RSASSA-PKCS1-v1_5 signs deterministically, and the PKCS#1 re-encode depends on the key alone (§3.6) |
| secp256k1 derive and verify | pure | deterministic (§3.6) |
| secp256k1 sign, DER over SHA-256 of a message and compact over a digest | pure | RFC 6979 derives the nonce from the key and the digest (§3.6) |
| ECDSA P-256 derive, re-encode, and verify | pure | deterministic (§3.6). Verification is the interim fallback until the facade routes it. |
| ECDSA P-256 sign | `IO` | ECDSA draws a random nonce (§3.6) |
| SHA-1, SHA-512, the interim SHA-256, HMAC, HKDF | pure | deterministic (§3.6) |
| ChaCha20-Poly1305 seal and open | pure | deterministic (§3.6) |
| X.509 parse and extension helpers | pure | one certificate parses to the same answer every time |
| random bytes, key generation | `IO` | randomness (§3.6) |

Four families have etheorem hazmat packages: secp256k1
(`LeanHazmatSecp256k1`, libsecp256k1), ECDSA P-256 (`LeanHazmatP256`,
OpenSSL), SHA-256 (`LeanHazmatSha256`, OpenSSL and ISA-L), and
keccak-256 (`LeanHazmatKeccak`, keccak-tiny). The facade (§3.6, W3.3)
routes P-256 verification and keccak-256 there. Two families stay on
this package's bindings, and the plan's "Pin outcomes" records both
(§4.6):
- The `LeanHazmatSha256` archive breaks the executables that link it,
  so SHA-256 uses the interim fallback while that pin is out.
- The `LeanHazmatSecp256k1` verifier turns a high S into a low S
  before it verifies, so it accepts what the low-S rule of §4.6
  rejects. secp256k1 verification stays here, and the etheorem
  package serves key recovery.

The integration facts constrain the split. The etheorem monorepo pins
Lean v4.34.1, and this repo pins v4.34.0. The license is LGPL-3.0 with
a contributor agreement. The packages live in the monorepo, and
per-package publication repos are promised but not yet present.

Consumption follows etheorem's own pattern: a Lake `require` of the
single family package from the monorepo, at a pinned rev, with
`subDir := packages/hazmat/<Pkg>`. No mirror repo is needed. The
backend requires single families, never the `LeanHazmat` umbrella, so
the build compiles only the families it uses. The monorepo's
per-family packaging exists for that compile-cost isolation.

The native libraries under the four packages differ by origin:
- `LeanHazmatP256` links the system `libcrypto` through pkg-config.
- `LeanHazmatSecp256k1` and `LeanHazmatKeccak` build from sources that
  the monorepo's own `just` vendor recipes fetch into gitignored
  `vendor/` trees, never git submodules. Each recipe carries its pin:
  a tag for libsecp256k1 and a rev for keccak-tiny.
- `LeanHazmatSha256` uses both: the system `libcrypto` through
  pkg-config, and a vendored ISA-L `sha256_mb` unit. The x86_64 Linux
  build fetches that unit through `just hazmat-sha256-vendor`, and it
  needs `nasm`.

A checkout that skips those recipes fails the build with the packages'
own actionable hints. So the repo's CI runs the fetch steps of the
pinned families before `lake build` (`scripts/hazmat-vendor.sh`).
After the fetch, the build needs no network.

Root unit W3.2 owns the pins and the toolchain-compat checks, and W3.3
lands the facade routes (§4.6). A primitive falls back to this
package's own shim for the interim when its pin does not build or its
archive breaks the executables that link it. The plan records the
fallback. Keccak-256 is the exception. It has no own shim here, so a
failed pin blocks W6.1 (§4.6).

The shim binds SHA-512, SHA-1, HMAC-SHA-256, and HKDF-SHA-256. It also
keeps the OpenSSL SHA-256 binding as the interim fallback.
Production SHA-256 routes to `LeanHazmatSha256` while that pin holds,
and to this binding while it is out, as it is today. The own-bound
bindings are the production path for their primitives (§4.6). The
primitives are deterministic, so the bindings are pure. The pure
copies of `crypto/pure`, the package behind the `CryptoPure`
namespace, are the audited implementations. The W3.3 cross-check
compares them with the production path at the IO edge.

Boundary contracts sit on the surface. A verifier accepts only the key
type and size it claims (§4.6):
- P-256 keys only, as the SPKI of an uncompressed point, the one form
  Go accepts.
- RSA keys of 2048 to 8192 bits only.
- secp256k1 low-S signatures only.

The X.509 helpers reject a certificate with an unknown critical
extension (tls.md, "the endpoint does not understand"). A critical
extension passes when it is the libp2p extension or one OpenSSL
understands (`X509_supported_extension`). go-libp2p does the same: it
leaves the known ones to Go's `crypto/x509`
(`vendor/go-libp2p/p2p/security/tls/crypto.go`, lines 171 to 184). The
helpers reject any extension that appears twice (RFC 5280 §4.2). The
self-signature check accepts SHA-256, SHA-384, SHA-512, and Ed25519
signatures, the set Go accepts, and it applies the RSA range to an RSA
subject key.

The helpers return the NotBefore and NotAfter times and do not judge
them. The caller compares them against the `Clock` seam (§3.1), so the
pure binding never reads the clock. A failed ChaCha20-Poly1305 open is
an authentication failure, and `CryptoError` gives it its own arm. So
the Noise layer maps it to a protocol error and keeps a backend fault
apart (§3.5, §4.9).

**Trust boundary.** The docstrings carry the empirical trust
assumption of every `@[extern]` declaration: the library, its pin, and
the vector suite that checks it. A public declaration states it in its
own docstring. The private raw declarations share the docstring of
their module. For the own-bound bindings the library is the
toolchain's bundled OpenSSL 3, which `lean-toolchain` pins. The
etheorem packages' own suites check the routed primitives, and the RFC
and fixture suites check the own-bound ones.

The declarations are `opaque` constants. The kernel cannot unfold them,
and `#print axioms` does not list them, so the docstrings are the one
record of the assumption.

A verifier binding folds every malformed input and every shim fault
into `false`, fail-closed, and its docstring states the fold. The
`Bool` return has no fault channel (§3.6). The etheorem verifiers state
the same fold.

The bridge to the pure package stays empirical. The W3.3 cross-check
compares the two sides at the IO edge. This package records no
equivalence axiom, because no proof in this repo consumes a hash.
etheorem records named equivalence axioms for SHA-256, because its SSZ
proofs consume the hash. This repo's SSZ stays client-side, so a reader
adds that axiom pattern only when a proof here starts to consume a
digest.

## Owned contracts

1. **Every `ByteArray` argument is borrowed (`@&`).** The binding
   states the ownership. The `@[extern]` declaration carries `@&` on
   each argument. The shim declares each one `b_lean_obj_arg` and never
   takes a reference. Each binding module states the rule in its
   docstring. An owned parameter leaks one reference per call
   (PRINCIPLES 4.1).
2. **Sizes are checked before the call.** The Lean side checks each
   fixed size into a proof-carrying newtype (`Key32`, `Nonce12`, a
   32-byte seed) and passes the `ByteArray` with its proof (§3.7). It
   checks a range bound, such as the `int` limit of the AEAD lengths,
   before the call too. The shim checks what only the parse knows: the
   DER-derived lengths of a parsed key, and that a DER input fits the
   `int` length of its OpenSSL parser. Every other length arrives
   checked, and the shim validates nothing twice. The DER-content
   strictness of the verifiers is a different check. It reads the
   parsed key, so it stays in the C verifier (§4.6, PRINCIPLES 2.4).
   The range of a secp256k1 scalar, `[1, n - 1]` (SEC 1 §3.2.1), is
   a check of the same kind. The group order is a curve fact that the
   loader reads, and OpenSSL signs with a scalar outside the range. So
   the shim's loader checks it, once, for every secp256k1 binding.
3. **The shim stays auditable in one sitting.** It is one C file of our
   own, with the spike's conventions at the top. Every entry point
   carries the `leanp2p_` prefix. Any further C file needs a reason in
   this document first (PRINCIPLES 4.1).
4. **Verifier strictness is a contract, with a regression per rule.**
   Each rule of §4.6 but one closes a divergence from go-libp2p. The
   low-S rule follows the spec where go-libp2p accepts a high S, and
   "Decisions" records it (PRINCIPLES 2.1, 2.4). §6 keeps every rule
   pinned by test, and the package plan names the cases.
5. **FFI behavior is pinned by vectors, never by the kernel.** No `decide`
   over an `@[extern]` result (CLAUDE.md, "Proofs and tests"). A finite
   goal over compiled data may close with `native_decide`, and the
   docstring cites the compiler axiom when it does (§6).

## The facade

`packages/crypto/Crypto.lean` is one `lean_lib` of `export` and `abbrev`
lines at the group root (§2, §3.6). Callers import only it, except this
package's own suites. The facade names the production implementation of
each primitive: this package for every primitive it binds, and the
etheorem packages for the routed primitives. The pure copies of
`crypto/pure` are the audited copies and the oracles. The W3.3
cross-check compares them with the production path at the IO edge. The
facade also carries the `Rng` seam (§3.6), whose test value is a seeded
`Rng` (§3.1). To move one primitive to pure Lean or to another native
library, one line of the facade changes, and no call site changes
(§3.6).

The W3.3 cross-check is the standing relation between this package and
`crypto/pure`. It compares the pure copies with the production path,
property-wise at the IO edge (PLAN W3.3):
- over the RFC vectors and over generated inputs,
- in both directions.

The relation runs through the facade and the cross-check, and never
through an import. The pure pair states the same rule from its side.
This pair's plan carries the unit.

## Decisions

- **The EVP surface stays here, and the key marshalings go to
  `libp2p/identity`** (§2, §4.6, §10 row 7). The bindings take key bytes
  in and give key bytes out, because OpenSSL needs the DER forms to load
  a key. The choice of which form a key type uses, and the key-type
  protobuf, are libp2p facts, so they live above (W5.1). The shim exposes
  no marshal API of its own.
- **The borrowed argument is a contract, written at every binding.** The
  review found the leak by measurement: 200,000 SHA-256 calls grew RSS
  from 14 MB to 526 MB, and to 9.5 MB after the fix (PRINCIPLES 4.1).
  The compiler checks the type-level `@&`. Review checks the shim-side
  `b_lean_obj_arg` discipline.
- **Deterministic signing stays pure.** §3.6 fixes the split, and it
  matches the schemes. Ed25519 (RFC 8032) and RSASSA-PKCS1-v1_5 derive
  the signature from the key and the message alone. The ECDSA P-256
  signer draws a nonce, so its binding takes the world.
- **secp256k1 has one signing core, RFC 6979, behind two entry
  points.** The core signs a 32-byte digest with the RFC 6979 nonce
  (OpenSSL 3.2 and later) and sets S low, so both bindings are pure.
  The entry points differ only in what the protocol fixes:
  - `secp256k1Sign` hashes the message with SHA-256 and gives DER,
    the peer-ids form that `secp256k1Verify` takes.
  - `secp256k1SignDigest` takes the caller's digest and gives the
    compact `r ‖ s`. The `v4` ENR identity scheme signs a keccak-256
    digest in that form (EIP-778).

  go-libp2p signs secp256k1 by RFC 6979 over SHA-256 (decred), and
  geth signs by RFC 6979 through libsecp256k1. The shared nonce rule
  makes the three agree byte for byte. So the go fixture pins the
  re-sign, as it pins RSA.
- **The spike's binding types refine into the §3.6 split.** The spike
  declared every binding in `IO`, because it predates §3.6. The
  implementation keeps the spike's primitives and shim, and moves the
  deterministic bindings to pure `opaque` declarations with the
  `Except CryptoError` lift.
- **The spike's DNS helper stays out.** The spike's shim also bound
  `resolveV4` for the interop harness. It serves no crypto purpose, so
  the harness of `cli/` owns it (W5.9), and the shim here keeps to
  crypto.
- **keccak-256 routes to `LeanHazmatKeccak`.** The keccak path is the
  etheorem package, which binds keccak-tiny (§4.6). The package's own
  suite and the fixed cases of the empty string and `abc` pin the
  bytes. The W6.1 record fixture pins the end-to-end path through the
  facade. The cross-check covers only the families both sides
  implement, so vectors alone pin keccak-256.
- **No `decide` over an FFI result.** An `@[extern]` value is opaque to
  the kernel, so the vector suites and the cross-check are the evidence
  (CLAUDE.md, "Proofs and tests", and PRINCIPLES 5.1).
- **secp256k1 verification requires a low S, and go-libp2p accepts a
  high S** (PRINCIPLES 2.1). The spec signs "using the standard Bitcoin
  EC signature algorithm (BIP0062)" (`vendor/specs/peer-ids/peer-ids.md`,
  lines 172 to 176), and BIP-62 requires a low S. go-libp2p verifies
  through decred `secp256k1/v4` v4.4.1
  (`vendor/go-libp2p/core/crypto/secp256k1.go`, lines 120 to 126). In
  decred's
  [`signature.go` at `76c0dc4f`](https://github.com/decred/dcrd/blob/76c0dc4f362b89331ff3bd46a3527f904181b8e0/dcrec/secp256k1/ecdsa/signature.go):
  - `ParseDERSignature` (lines 315 to 545) rejects only an S of zero
    or past the order.
  - `Verify` (line 233) checks only for zero.
  - `Serialize` (lines 98 to 105) turns a high S low, so a go peer
    signs low-S.

  The spec wins, and the rule costs no interop with a go signer.
  `Tests/BackendStrict.lean` checks that the high-S twin of a valid
  signature fails.

## What the package must not depend on

- No `crypto/pure` import, and no etheorem package import. The relation
  between the packages is the
  W3.3 cross-check, run through the facade. The pure pair states the
  same rule from its side.
- From `base`, `base/bytes` only, for the conversions the newtypes and
  the suites sit on. W1.2 is the root dependency of the implementation
  unit.
- No codec, no net, no libp2p. The package knows no wire format and no
  connection.
- No key-marshal knowledge. The key forms are opaque bytes here. The
  choices belong to `libp2p/identity` (§4.6).
