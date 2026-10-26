# leanp2p backend: architecture

`crypto/backend` binds OpenSSL 3 through a small C shim and `@[extern]`
declarations. It gives the stack Ed25519, X25519, RSA, SHA-1, SHA-512,
HMAC, HKDF, ChaCha20-Poly1305, and X.509, plus randomness and key
generation. Nobody writes
constant-time code in Lean for it (§4 preamble, §4.6). The bindings
reach the shim through one `leanp2p_`-prefixed entry point, so the
auditable-in-one-sitting contract holds. The package is the "FFI
first" phase of the dependency strategy. The pure package `crypto/pure`
is the "Lean later" phase. That pair owns the oracle side: the pure
copies are the audited implementations and the cross-check oracles,
and the W3.3 cross-check compares the pure copies with the production
path, the backend bindings, and the etheorem packages for the four
routed primitives, at the IO edge (§4.6 as amended). This pair owns
the binding side, and the bindings are the production path for every
primitive they carry. Four primitives route to the etheorem hazmat
packages instead; the "Public surface" section records the split and
its constraints.

## Modules

| Module | Holds, and why |
|---|---|
| `c/p2pcrypto.c` | the shim, one C file over the OpenSSL 3 EVP surface; the spike's is about 770 lines, and it stays auditable in one sitting (PRINCIPLES 4.1) |
| `Backend/Error.lean` | `CryptoError`, the one error inductive of the package (§3.5) |
| `Backend/Sym.lean` | random bytes, the SHA-1 and SHA-512 digest bindings, the interim SHA-256 binding, HMAC, HKDF, and ChaCha20-Poly1305 seal and open |
| `Backend/Sign.lean` | X25519 derivation and DH, plus derive, sign, and verify of the own-bound key types, Ed25519 and RSA, and the interim fallback bindings for secp256k1 and ECDSA P-256 |
| `Backend/X509.lean` | the libp2p certificate extension helpers of the tls.md shape |
| `Backend.lean` | the package root, one import line per submodule; production callers import `Crypto` instead (§3.6) |

The bindings split into three modules because they carry three
contracts. `Sym` owns the ownership rule and the AEAD failure shape,
`Sign` owns the verifier strictness, and `X509` owns the validity and
criticality rules. One module would hold three contract sets under one
docstring, and PRINCIPLES 1.2 says to split there. All declarations live
in the `Backend` namespace.

The shim compiles through a Lake target in this package's `lakefile.lean`.
This is the standing example where `lakefile.lean` is permitted, because
the declarative form cannot express a C build (PRINCIPLES 4.2; CLAUDE.md,
"Configure, don't integrate"). OpenSSL 3 is the shim's library today,
and further C dependencies follow the same FFI-first path (CLAUDE.md,
"Dependencies").

## Public surface

The families are the ones §7 row 7 names. The table below lists the
ones this package binds itself; the paragraph after it records the
routed four. The binding type of each follows
§3.6. The Lean interface lifts the `Option` of a shim failure to
`Except CryptoError`, once, in this package.

| Family | Binding type | Why |
|---|---|---|
| Ed25519 derive, sign, and verify | pure | Ed25519 signs deterministically (§3.6) |
| X25519 public-key derivation and DH | pure | deterministic (§3.6) |
| RSA derive, sign, verify | all pure | RSASSA-PKCS1-v1_5 signs deterministically (§3.6) |
| ChaCha20-Poly1305 seal and open | pure | deterministic (§3.6) |
| X.509 parse and extension helpers | pure | one certificate parses to the same answer every time |
| random bytes, key generation | `IO` | randomness (§3.6) |

Four families route to the etheorem hazmat packages, and this package
writes no second shim for them. The facade does the routing (§3.6):
secp256k1 goes to `LeanHazmatSecp256k1` (libsecp256k1), ECDSA P-256 to
`LeanHazmatP256` (OpenSSL), SHA-256 to `LeanHazmatSha256` (OpenSSL and
ISA-L), and keccak-256 to `LeanHazmatKeccak` (keccak-tiny). The
libsecp256k1 default already rejects high-S, so the etheorem binding
and the low-S rule of §4.6 agree. The integration facts constrain the
split: the etheorem monorepo pins Lean v4.29.1 against this repo's
v4.34, the license is LGPL-3.0 with a contributor agreement, and the
packages are monorepo-resident, with per-package publication repos
promised but not yet present.

Consumption follows etheorem's own pattern: a Lake `require` of the
single family package from the monorepo, at a pinned rev, with
`subDir := packages/hazmat/<Pkg>`. No mirror repo is needed. The
backend requires single families, never the `LeanHazmat` umbrella, so
the build compiles only the families it uses. The monorepo's
per-family packaging exists for that compile-cost isolation.

The native libraries under the four packages split by origin.
`LeanHazmatP256` links the system `libcrypto` through pkg-config.
`LeanHazmatSecp256k1` and `LeanHazmatKeccak` fetch their libraries
shallow into gitignored `vendor/` trees at the recipes' pins, a tag
for libsecp256k1 and a rev for keccak-tiny, through the monorepo's
own `just` vendor recipes, never git submodules. `LeanHazmatSha256`
is mixed: the system `libcrypto` through pkg-config, plus a vendored
ISA-L `sha256_mb` unit that the x86_64 Linux build fetches through
`just hazmat-sha256-vendor` and needs `nasm` for. A checkout that
skips those recipes fails the build with
the packages' own actionable hints, so the repo's CI runs the vendor
fetch steps before `lake build`. The build itself stays offline after
the fetch.

Root unit W3.2 owns the pins, the
toolchain-compat checks, and the facade routes. A primitive whose pin
does not build falls back to this package's own shim for the interim,
and the plan records the fallback. Keccak-256 is the exception: it
has no own shim here, so a failed pin blocks W6.1 (§4.6).

The shim also binds SHA-512, SHA-1, HMAC-SHA-256, and
HKDF-SHA-256, and it keeps the OpenSSL SHA-256 binding as the interim
fallback: production SHA-256 routes to `LeanHazmatSha256`, and the
binding takes over only if that pin does not build, under the same
fallback rule as secp256k1 and ECDSA P-256. The own-bound bindings are the
production path for their primitives, per §4.6 as amended, and the
primitives are deterministic, so the bindings are pure. The pure
copies of `crypto/pure`, the package behind the `CryptoPure`
namespace, are the audited implementations, and the W3.3 cross-check
compares the pure copies with the production path at the IO edge.

Boundary contracts sit on the surface. A verifier accepts only the key
type and size it claims: P-256 SPKI only, RSA of 2048 to 8192 bits only,
secp256k1 low-S signatures only (§4.6). The X.509 helpers reject a
certificate with an unknown critical extension, and only the libp2p
extension may be critical. The helpers return the NotBefore and NotAfter
times instead of judging them, and the caller compares them against the
`Clock` seam (§3.1), so the pure binding never reads the clock. A failed
ChaCha20-Poly1305 open is an authentication failure, and `CryptoError`
gives it its own arm, so the Noise layer maps it to a protocol error and
keeps a backend fault separate (§3.5, §4.9).

**Trust boundary.** Every `@[extern]` declaration's docstring names its
empirical trust assumption: which library, at which pin, and which
vector suite validates it. The etheorem packages' own suites validate
the four routed primitives, and the RFC and fixture suites validate the
own-bound ones. The declarations are `opaque`, and the assumptions are
visible under `#axioms`. A verifier binding folds every malformed
input and every shim fault into `false`, fail-closed, and its
docstring states the fold; no fault channel exists on the `Bool`
return (§3.6; the etheorem verifiers state the same fold). The bridge
to the pure package stays
empirical: the W3.3 cross-check compares the two sides at the IO edge,
and this package records no equivalence axiom, because nothing in this
repo consumes a hash inside a proof. etheorem records named equivalence
axioms for SHA-256, because its SSZ proofs consume the hash. This
repo's SSZ stays client-side, so a reader imports that axiom pattern
only when a proof here starts to consume a digest.

## Owned contracts

1. **Every `ByteArray` argument is borrowed (`@&`).** The ownership is
   written at the binding: the `@[extern]` declaration carries `@&` on
   each argument, the shim declares each one `b_lean_obj_arg` and never
   takes a reference, and each binding module states the rule in its
   docstring. An owned parameter leaks one reference per call
   (PRINCIPLES 4.1).
2. **Sizes are checked before the call.** The Lean side checks a fixed
   size into a proof-carrying newtype (`Key32`, `Nonce12`, a 32-byte
   seed) and passes the `ByteArray` with its proof (§3.7). The shim
   checks the DER-derived lengths of a parsed key once, because the
   newtype cannot know them; every other length crosses as a proved
   size, and the shim validates nothing twice. The DER-content
   strictness of the verifiers is a different check: it reads the parsed
   key, so it stays in the C verifier (§4.6; PRINCIPLES 2.4).
3. **The shim stays auditable in one sitting.** One C file of our own,
   reached through one `leanp2p_`-prefixed entry point, with the
   spike's conventions at the top. Any further C file needs a reason
   in this document first (PRINCIPLES 4.1).
4. **Verifier strictness is a contract, with a regression per rule.**
   The rules of §4.6 each close a divergence from go-libp2p, and §6
   keeps them pinned by test. The package plan names the cases.
5. **FFI behavior is pinned by vectors, never by the kernel.** No `decide`
   over an `@[extern]` result (CLAUDE.md, "Proofs and tests"). A finite
   goal over compiled data may close with `native_decide`, and the
   docstring cites the compiler axiom when it does (§6).

## The facade

`packages/crypto/Crypto.lean` is one `lean_lib` of `export` and `abbrev`
lines at the group root (§2, §3.6). Callers import only it, except this
package's own suites. The facade names the production implementation of
each primitive: this package for every primitive it binds, and the
etheorem packages for the four routed primitives. The pure copies of
`crypto/pure` are the audited copies and the oracles, and the W3.3
cross-check compares the pure copies with the production path at the
IO edge. The facade also carries the
`Rng` seam (§3.6), whose test value is a seeded `Rng` (§3.1). To move
one primitive to pure Lean or to another native library, one line of
the facade changes, and no call site changes (§3.6).

The W3.3 cross-check is the standing relation between this package and
`crypto/pure`. The cross-check compares the pure copies with the
production path, the backend bindings, and the etheorem packages for
the four routed primitives, property-wise at the IO
edge, over the RFC vectors and over generated inputs, in both directions
(PLAN W3.3). The relation runs through the facade and the cross-check.
It never runs through an import, and the pure pair states the same rule
from its side. This pair's plan carries the unit.

## Decisions

- **The EVP surface stays here, and the key marshalings go to
  `libp2p/identity`** (§2, §4.6, §10 row 7). The bindings take key bytes
  in and give key bytes out, because OpenSSL needs the DER forms to load
  a key. The choice of which form a key type uses, and the key-type
  protobuf, are libp2p facts, so they live above (W5.1). The shim exposes
  no marshal API of its own.
- **The borrowed argument is a contract, written at every binding.** The
  review found the leak by measurement: 200,000 SHA-256 calls grew RSS
  from 14 MB to 526 MB, and 9.5 MB after the fix (PRINCIPLES 4.1). The
  type-level `@&` is the part the compiler keeps honest, and the
  shim-side `b_lean_obj_arg` discipline is the part review keeps honest.
- **Deterministic signing stays pure.** §3.6 fixes the split, and it
  matches the schemes: Ed25519 (RFC 8032) and RSASSA-PKCS1-v1_5 derive
  the signature from the key and the message alone. secp256k1 and ECDSA
  P-256 draw a nonce, so their sign bindings take the world. go-libp2p
  signs secp256k1 with RFC 6979 and OpenSSL randomizes the nonce, so the
  note in `keys-go-libp2p.json` records that verification is the
  contract for those two types.
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
  suite plus the fixed cases of the empty
  string and `abc` pin the bytes, and the W6.1 record fixture pins the
  end-to-end path through the facade. The cross-check contract covers
  only the families both sides implement, so keccak-256 stays
  vector-pinned.
- **No `decide` over an FFI result.** An `@[extern]` value is opaque to
  the kernel, so the vector suites and the cross-check are the evidence
  (CLAUDE.md, "Proofs and tests"; PRINCIPLES 5.1).

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
- No key-marshal knowledge. The key forms are opaque bytes here; the
  choices belong to `libp2p/identity` (§4.6).
