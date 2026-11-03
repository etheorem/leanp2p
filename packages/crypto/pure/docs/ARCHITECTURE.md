# leanp2p pure: architecture

`crypto/pure` holds the pure Lean implementations of SHA-256, SHA-512,
SHA-1, HMAC, and HKDF, with theorems (ARCHITECTURE §4.6). It is the
"Lean later" phase of the dependency strategy (§4 preamble), and it
plays two roles. It is the audited copy, and it states each algorithm
in the language of the stack. It is the oracle that the cross-check
(PLAN W3.3) compares with the production path at the IO edge. The
production path is the backend bindings and the etheorem packages for
the routed primitives. §4.6 fixes which side produces. The backend is
the production path for every primitive it binds, the digests
included. Production SHA-256 routes to `LeanHazmatSha256` while that
pin holds, and to the backend binding while it is out, as it is today
(§4.6). The facade names
the production implementation of every primitive in the surface. A
pure copy moves to production only by a one-line facade change, and
none does today. The constant-time code stays in the C shim of
`crypto/backend`, and this package claims no constant-time behavior
(§4.6).

## Modules

| Module | Holds, and why |
|---|---|
| `CryptoPure.lean` | the root module; one import line per public submodule |
| `CryptoPure/Constants.lean` | the FIPS 180-4 tables (`K` and `H0`) and byte sizes, the HMAC pads, and the HKDF block cap (§3.8; PRINCIPLES 1.5) |
| `CryptoPure/Preprocess.lean` | shared padding and block splitting (FIPS 180-4 §5), word parsing and big-endian conversions (§3.1), and their theorems |
| `CryptoPure/Sha256.lean` | the round functions, the message schedule, the compression, and the digest, over the model and over `ByteArray` |
| `CryptoPure/Sha512.lean` | the same shape over `UInt64` words and 128-byte blocks |
| `CryptoPure/Sha1.lean` | the 160-bit digest for multihash framing, using `UInt32` words and shared preprocessing (see "Decisions") |
| `CryptoPure/Hmac.lean` | generic HMAC and SHA-256/SHA-512 functions, with reduction, long-key, and length theorems |
| `CryptoPure/Hkdf.lean` | generic `extract` and `expand` and SHA-256 functions, with reduction, length, and prefix theorems |

The package keeps the spike's one-module-per-primitive shape
(`Crypto/{Sha256,Sha512,Sha1,Hmac,Hkdf}.lean`; ARCHITECTURE §10,
row 6). Each primitive reads on its own, and that is the point of an
audit copy. The theorems live with the code they describe: padding in
`Preprocess.lean`, HMAC in `Hmac.lean`, and HKDF in `Hkdf.lean`. All
constants live in `Constants.lean`, and all hashes use the padding in
`Preprocess.lean`, so each fact has one home.

The three hashes share `Preprocess.words32` and `words64` to read their
input words. Each hash holds its state as a `Vector` of words, so the
state size is part of the type.

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
- `Hkdf.expand` returns `Option (List Nat)`. Its docstring gives `none`
  one meaning: the requested length exceeds `255 × HashLen`, the cap
  in RFC 5869 §2.3 (§3.5). `CryptoError` belongs to `crypto/backend`,
  which converts its raw `Option` binding to `Except CryptoError`.
  W3.3 maps the pure `none` to the backend error for the same request.
- `Hmac.sha256`, `Hmac.sha512`, `Hkdf.extractSha256`, and
  `Hkdf.expandSha256` fix the hash for the callers that need one.
  The HMAC vectors cover SHA-256 and SHA-512. The HKDF vectors use
  SHA-256.

Callers do not import this package. They import the `Crypto` facade
(§3.6), which names the production implementation of every primitive
in the surface. This package is where a reader audits the code. The
facade pair (`packages/crypto/docs/`) records the routes and the W3.3
cross-check. This pair owns the pure side: the pure copies as the
oracles of the cross-check, and the properties the comparison needs.
Purity is
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

   The padding theorems hold for every message length. The padded
   length is a multiple of the block size, using the fewest zero bytes
   needed. The message is a prefix, followed by
   `0x80` and zero bytes. The last field reads back as the bit length
   modulo `2 ^ (8 × width)`. `Preprocess.lengthOfMemBlocksPad` proves
   that every block of a padded message is full. Each hash also proves
   that every digest entry is below 256, so conversion to bytes
   preserves its value.

   HMAC proves the normalized key length and the output length.
   `Hmac.hmacLongKey` proves that a long key gives the same MAC as its
   hash when the hash output fits in a block. RFC 4231 TC6 and TC7
   check the expected MAC bytes independently of that structural
   property. HKDF-Expand returns exactly `L` bytes under the cap and
   `none` past it. For the same inputs, a successful shorter output
   is a prefix of a successful longer output.
2. **The model pin.** `digestB b` is `ofNatList (digest (toNatList
   b))` by construction, and the suite checks the agreement on every
   run, in the spike's shape (§4.2, §6).
3. **The vector suites pin the bytes.** The RFC families run through
   the W0.3 infrastructure (§6, §7 row 6). The package plan names the
   files.
4. **The cross-check contract.** The cross-check compares the pure
   copies with the production path, property-wise at the IO edge
   (§4.6, PLAN W3.3). The production path is the backend bindings and
   the etheorem packages for the routed primitives. The cross-check
   suite, `Tests/CryptoCross.lean`, is the one module that imports both
   implementations, and the facade pair records it. This package's side
   is to stay pure and total, so the comparison is well-defined. Every
   loop names its measure. The two SHA-2 block loops terminate on the
   remaining input length, where the spike marked `partial` (§3.3).
   The HKDF expand loop terminates on the remaining output length.
   HMAC is the fixed two-call form over the hash, and its termination
   follows from that structure.
## Decisions

- **Pure Lean digests exist although production routes elsewhere.** They
  serve the two roles of the opening paragraph (PRINCIPLES 4.1 and 5.1).
  §4 preamble fixes the shape for phase 2: re-implement behind the
  same interface, back the code with theorems, and cross-check it
  against the FFI. Deleting the pure copies deletes the oracle, so the
  cross-check would compare the production path with itself. SHA-256
  keeps its pure copy, because the copy is the oracle for the SHA-256
  cross-check, whichever binding is in production.
- **The production path is the backend and the etheorem bindings. The
  pure copies are the audited copies and the oracles.** §4.6 names the
  backend the production path for every primitive it binds, the
  digests included. It routes production SHA-256 to
  `LeanHazmatSha256` while that pin holds, and to the backend binding
  while it is out. The facade
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
  and nothing security-relevant. The module docstring records the
  cryptanalysis behind the rule.
- **No constant-time claims.** §4.6 states the rule: nobody writes
  constant-time primitives in Lean. The constant-time code stays in
  the C shim. The Lean copy serves the audit and the cross-check, and
  each digest docstring states the limit.
- **HKDF-Expand refuses an over-long request.** The spike does not
  enforce the cap of RFC 5869 §2.3. Above `255 × HashLen`, its counter
  exceeds one byte and it returns output outside the RFC's limit.
  Here, `expand` checks the cap and returns `none` above it (PRINCIPLES
  2.1). The single meaning of `none` meets §3.5, and the function stays
  total, as owned contract 4 requires. Noise uses production HKDF
  through the facade.
- **SHA-1 takes the shape of SHA-256.** The spike's SHA-1 works on
  `Nat` with masks. Here it uses `UInt32` words, the shared padding,
  and the shared block split, so one proof covers the padding of both.
- **Proof scope.** The theorems cover padding, block splitting, digest
  lengths and byte bounds, and the HMAC and HKDF formulas. Vectors
  check the compression functions on their inputs. W3.3 adds the
  comparison with the production path. Compression correctness for
  every input and cryptographic security remain outside these proofs.

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
