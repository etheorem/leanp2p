# leanp2p pure: architecture

`crypto/pure` holds the pure Lean implementations of SHA-256, SHA-512,
SHA-1, HMAC, and HKDF, with theorems (ARCHITECTURE §4.6). It is the
"Lean later" phase of the dependency strategy (§4 preamble), and it
plays two roles. It is the audited copy, and it states each algorithm
in the language of the stack. It is the oracle that the cross-check
(PLAN W3.3) compares with the production path, the backend bindings,
and the etheorem packages for the four routed primitives, at the IO
edge. §4.6 as amended fixes which side produces: the backend is the
production path for every primitive it binds, the digests included,
and production SHA-256 routes to `LeanHazmatSha256`. The facade names
the production implementation of every primitive in the surface. A
pure copy moves to production only by a one-line facade change, and
none does today. The constant-time code stays in the C shim of
`crypto/backend`, and this package claims no constant-time behavior
(§4.6).

## Modules

| Module | Holds, and why |
|---|---|
| `CryptoPure.lean` | the root module; one import line per public submodule |
| `CryptoPure/Constants.lean` | the block, length-field, and digest sizes, the round constants, and the initial states (the `K` and `H0` tables of FIPS 180-4), the HMAC pads, and the HKDF block cap; one canonical home per fact (§3.8; PRINCIPLES 1.5) |
| `CryptoPure/Preprocess.lean` | the padding and the block split of FIPS 180-4 §5, stated once over the block size and the length-field width, and the big-endian word conversions of §3.1, with their theorems |
| `CryptoPure/Sha256.lean` | the round functions, the message schedule, the compression, and the digest, over the model and over `ByteArray` |
| `CryptoPure/Sha512.lean` | the same shape over `UInt64` words and 128-byte blocks |
| `CryptoPure/Sha1.lean` | the 160-bit digest in the shape of SHA-256, for the multihash framing (see "Decisions") |
| `CryptoPure/Hmac.lean` | key normalization and `hmac` over the hash and block size given as arguments, and the SHA-256 and SHA-512 instances, with the reduction and length theorems |
| `CryptoPure/Hkdf.lean` | `extract` and `expand` over HMAC, and the SHA-256 instances, with the reduction, length, and prefix theorems |
| `CryptoPure/Mock/Bytes.lean` | temporary: the four `base/bytes` conversions this package and its suite use, until W1.2 merges (see "Working ahead of W1.2") |

The package keeps the spike's one-module-per-primitive shape
(`Crypto/{Sha256,Sha512,Sha1,Hmac,Hkdf}.lean`; ARCHITECTURE §10,
row 6). Each primitive reads on its own, and that is the point of an
audit copy. The theorems live beside the constructions they state: the
padding theorems in `CryptoPure/Preprocess.lean`, the HMAC theorems in
`CryptoPure/Hmac.lean`, the HKDF theorems in `CryptoPure/Hkdf.lean`. A
separate theorem module would import the constructions and state
nothing of its own. The constants move into
`CryptoPure/Constants.lean`, and the padding moves into
`CryptoPure/Preprocess.lean`, so the padding rule and the three block
sizes each have one home.

All declarations live in the `CryptoPure` namespace. The name avoids
the collision with Lean's standard `Pure` typeclass, which a bare
`Pure` namespace would create. The root module
re-exports the public submodules.

## Public surface

The names are the root names (§7, row 6): digests, HMAC, HKDF.

- `Sha256.digest`, `Sha512.digest`, and `Sha1.digest` over the `List
  Nat` model, and `digestB` over `ByteArray`. The digest sizes are 32,
  64, and 20 bytes. The spike carries `digestB` for SHA-256, and the
  same one-line composition over the conversions of `base/bytes` gives
  it to the rest (`base/bytes` docs). The spike exposes one-shot
  digests only, and the surface keeps that form; the block loop that
  compresses 64-byte or 128-byte chunks is internal.
- `Hmac.normKey` and `Hmac.hmac`. RFC 2104 fixes the construction: a
  key longer than the block is hashed first, then zero-padded to the
  block size. The core takes the hash and its block size as explicit
  arguments, so HMAC over the 64-byte block of SHA-256 and HMAC over
  the 128-byte block of SHA-512 are one function at two arguments.
- `Hkdf.extract` and `Hkdf.expand` over HMAC (RFC 5869). An empty salt
  becomes a zero key of the hash length, as RFC 5869 and the spike
  specify.
- `Hkdf.expand` returns `Option (List Nat)`. It returns `none` exactly
  when the requested length is above `255 × HashLen`, the cap of RFC
  5869 §2.3, and the docstring states that one meaning (§3.5). The
  package cannot name `CryptoError`, which lives in `crypto/backend`.
  The backend lifts its raw `Option` binding to `Except CryptoError`
  once, in its own package, and W3.3 maps the pure `none` to the error
  the backend reports for the same request.
- `Hmac.sha256`, `Hmac.sha512`, `Hkdf.extractSha256`, and
  `Hkdf.expandSha256` fix the hash for the callers that need one. The
  current HMAC and HKDF vector families use SHA-256.
- Each hash holds its state as a `Vector` of words, so the state size
  is part of the type.

Callers do not import this package. They import the `Crypto` facade
(§3.6), which names the production implementation of every primitive
in the surface. This package is where a reader audits the code. The
facade gets no documentation pair of its own.
Its story is split across the two crypto packages, and this pair
owns the pure side: the pure copies as the oracles of the W3.3
cross-check, and the properties the facade must preserve. Purity is
the first property: the named functions keep the §3.6 promise of
same input, same output, and no side effect. Totality is the second:
the cross-check compares two implementations at the IO edge, and the
comparison needs a total function on this side.

## Owned contracts

1. **The reduction theorems.** HMAC reduces to the hash core, and HKDF
   reduces to HMAC. The definitions are the constructions, so the
   theorems close by `rfl`, and the build re-checks the RFC formulas
   at every rebuild. The length theorems carry the hashes:
   `(Sha256.digest m).length = 32`, and the 64 and 20 cases for
   SHA-512 and SHA-1. With the reductions, all five primitives carry a
   theorem. The spike carried no Lean theorem over these pure
   implementations; it validated them through the vector suites and the
   OpenSSL cross-check. §4.6 demands theorems behind the code, and these are
   the ones the constructions carry (§4 preamble; PRINCIPLES 5.1).
   The spike proved no streaming or chunking theorem either; its
   digests have one form, and the size sweep covers the padding
   boundaries as behavior, so that check stays a test.
   The padding carries theorems as well, for every message length: the
   padded length is a whole number of blocks, no shorter zero run
   reaches a block boundary, the message is a prefix, `0x80` follows
   it, and the last field reads back as the bit length modulo
   `2 ^ (8 × width)`. Every block the compression reads is full. HMAC
   has its key-block and output lengths. HKDF-Expand returns exactly
   `L` bytes under the cap, `none` past it, and a prefix of every
   longer output.
2. **The model pin.** `digestB b` is `ofNatList (digest (toNatList
   b))` by construction, and the suite checks the agreement on every
   run, in the spike's shape (§4.2, §6).
3. **The vector suites pin the bytes.** The RFC families run through
   the W0.3 infrastructure (§6, §7 row 6). The package plan names the
   files.
4. **The cross-check contract.** The cross-check compares the pure
   copies with the production path, the backend bindings, and the
   etheorem packages for the four routed primitives, property-wise at
   the IO edge (§4.6; PLAN W3.3). The cross-check runs in this
   package's suites, the one place that imports both stories through
   the facade, following
   the test-split rule of the backend pair. This package's side
   is to stay pure and total, so the comparison is well-defined. Every
   loop names its measure. The block split of `Preprocess` terminates
   on the remaining input length, where the spike's block loops were
   `partial` (§3.3), and each hash folds its compression over the
   finished block list. The HKDF block loop is structural recursion on
   the block count. HMAC is the fixed two-call form over the hash, and
   its termination follows from that structure.

## Decisions

- **Pure Lean digests exist although production routes elsewhere.** They
  serve the two roles of the opening paragraph (PRINCIPLES 4.1 and 5.1).
  §4 preamble fixes the shape for phase 2: re-implement behind the
  same interface, back the code with theorems, and cross-check it
  against the FFI. Deleting the pure copies deletes the oracle, so the
  cross-check would compare the production path with itself. SHA-256
  keeps its pure copy even though production routes to
  `LeanHazmatSha256`: the copy is the oracle for that cross-check.
- **The production path is the backend and the etheorem bindings; the
  pure copies are the audited copies and the oracles.** §4.6 as amended
  names the backend the
  production path for every primitive it binds, the digests included,
  and routes production SHA-256 to `LeanHazmatSha256`. The facade
  names the production implementation for everything in the surface. A
  pure copy moves to production only by a one-line facade change, and
  none does today. The facade exports the `ByteArray` forms, because
  callers above the facade work on bytes; the spike's Noise consumes
  `Sha256.digestB`. One move goes against the spike: the spike
  hard-codes SHA-256 and the 64-byte block in HMAC, and this package
  takes the hash and block size as arguments, so SHA-512's HMAC is
  one function at two arguments.
- **SHA-1 is in, for the multihash framing.** The multihash function
  table names it, code 0x11, and a peer may send a sha1 multihash.
  This package computes the digest bytes. `codec/multiformats` frames
  digest bytes into a multihash (§4.4), and the group chain of §2
  keeps it from importing crypto, so the caller composes the two
  through the facade. Root W3.2 adds the SHA-1 binding to the
  backend, so SHA-1 joins the W3.3 cross-check like the other
  digests, and the pure copy stays as the audited implementation and
  oracle.
  The spike's rule carries over: SHA-1 serves the multihash framing
  and nothing security-relevant.
- **No constant-time claims.** §4.6 states the rule: nobody writes
  constant-time primitives in Lean. The constant-time code stays in
  the C shim. The Lean copy serves the audit and the cross-check, and
  each digest docstring states the limit.
- **HKDF-Expand refuses an over-long request.** The spike does not
  enforce the cap of RFC 5869 §2.3. It returns a list for every length,
  and past `255 × HashLen` its counter no longer fits in one byte, so
  the output leaves RFC 5869 with no error. The spec wins (PRINCIPLES
  2.1), so `expand` returns `none` for such a request. §3.5 allows the
  `Option`, because `none` has one meaning, and the function stays
  total, as owned contract 4 requires. No production caller reaches
  this copy: Noise takes HKDF through the facade.
- **SHA-1 takes the shape of SHA-256.** The spike's SHA-1 works on
  `Nat` with masks. Here it uses `UInt32` words, the shared padding,
  and the shared block split, so one proof covers the padding of both.
- **What the proofs do not cover.** The theorems prove the structure:
  the padding, the block split, the output lengths, and the HMAC and
  HKDF formulas. The vectors pin the compression functions on the
  tested inputs, and the W3.3 cross-check compares them with the
  production path. No theorem relates a compression function to the
  text of FIPS 180-4 for every input, and none claims a security
  property.

## Working ahead of W1.2

W1.2 (#2) is open. The package uses `CryptoPure/Mock/Bytes.lean`
under the `CryptoPure.Mock.Bytes` namespace, as `RULES.md` permits.
The mock imports no real dependency. Its four `opaque` functions,
`ofNatList`, `toNatList`, `ofString`, and `ofHex?`, have executable
bodies, so the suite runs. No proof unfolds them, so the mock adds no
axiom.

Integration replaces the mock module with `import Bytes`, renames
`Mock.Bytes.` to `Bytes.` at each use, and reruns the build, both test
modes, the import lint, and the axiom audit. `RULES.md` gives the
integration a twelve-hour window after W1.2 merges.

## What the package must not depend on

- No `crypto/backend` import, and no etheorem package import. A pure
  copy never calls the FFI. The facade resolves which implementation a
  caller sees (§3.6), and the relation between the packages runs
  through the W3.3 cross-check, never through an import.
- No `base/conc`. The package is pure: no task, no channel, no
  deadline, no clock.
- From `base`, `base/bytes` only: the model conversions that the
  `digestB` forms and the pins sit on. W1.2 is the root dependency
  behind both sub-units of the plan.
- No codec group. The package knows no wire format: no varint, no
  protobuf, no multicodec. A digest is a fixed-width byte string, and
  the multihash framing of one belongs to `codec/multiformats`.
