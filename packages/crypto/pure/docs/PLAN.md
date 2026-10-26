# leanp2p pure: plan

This plan refines the root `docs/PLAN.md` for `crypto/pure`. The root
plan owns the order across packages (PLAN.md, "How to read this
plan"). Sub-units 1a and 1b below close the root unit W3.1, and W1.2
is the root dependency. The done-when is the root row plus the root
definition of done: the surface follows ARCHITECTURE §7 row 6, the
owned contracts hold, the carried tests pass under `+RTS -N1`, and the
import lint is green.

## Units

Unit 1 splits into two sub-units. HMAC and HKDF are defined over the
hash core, so unit 1b needs unit 1a's digests before it can state its
reduction theorems. Each sub-unit also closes against its own vector
family. One unit for five primitives is too large to close at once,
and `codec/multiformats` set the pattern.

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1a | W1.2 | `CryptoPure/Constants.lean` and the three hashes: SHA-256, SHA-512, SHA-1, with the model functions, the `ByteArray` forms, and the model pins | the 1a milestones below pass |
| 1b | W1.2, 1a | HMAC over the hashes and HKDF over HMAC, with the reduction theorems | the 1b milestones below pass, and the root W3.1 row holds |

Unit 0 is done. Sub-units 1a and 1b close root W3.1 together.

## Consumers

W3.3 builds the `Crypto` facade and names the production
implementation of the surface (§3.6, §4.6 as amended): the backend for
SHA-512, SHA-1, HMAC, and HKDF, and `LeanHazmatSha256` for SHA-256.
The package architecture records that choice under
"Decisions". The pure copies are the audited implementations and the
oracles.
The same unit runs the cross-check: it compares the pure copies with
the production path, the backend bindings, and the etheorem packages
for the four routed primitives, at the IO edge (§4.6). The cross-check
covers SHA-1
too, through the SHA-1 binding that W3.2 lands. This package's suite
feeds that check and stays the oracle's own conformance suite.
The RFC and multihash vectors pin the pure side on every run, and
the production comparisons inside it close at W3.3, after W3.2 lands
the backend bindings and the etheorem pins.
W5.3 (Noise) consumes SHA-256, HKDF, and ChaCha20-Poly1305 through the
facade, and it reaches HMAC only inside HKDF. ChaCha20-Poly1305 is
backend-only, so it comes from the facade, and this package does not
implement it.

## Test milestones

Behavior tests close the units. The suite follows the root test-runner
layout of W0.2, and the `-N1` pass is required. Every listed case is
concrete, so no milestone is vacuous.

Milestones for 1a:

- SHA-512: the four FIPS 180-4 examples of `hashes-rfc.json`: the
  empty input, `abc`, `a`, and the 896-bit two-block message.
- SHA-256: the three NIST examples the spike carried inline in its
  multihash suite: the empty input, `abc`, and the 448-bit two-block
  message.
- SHA-256 and SHA-1: the multihash spec vectors of
  `multihash-examples.json`, the `sha2-256` and `sha1` cases over the
  input "multihash". The digest bytes inside the framing are the
  anchors; `hashes-rfc.json` holds no RFC entries for these two
  digests.
- The model pin: each `digestB` agrees with its model digest on the
  vector inputs and on the boundary lengths below.
- Empty input and block boundaries: the spike's sweep lengths, 0, 1,
  55, 56, 63, 64, 65, 119, 120, 128, and 1000 for SHA-256, and 0 to
  300 plus 511, 512, 513, 1000, and 4096 for SHA-512. The pure side
  closes here, and the production side closes at W3.3.

Milestones for 1b:

- HMAC-SHA-256: RFC 4231 TC1 and TC2 from `hashes-rfc.json`. Both keys
  sit under the block size, so the long-key rule has no vector
  anchor; the key-length sweep closes it against the production path
  at W3.3.
- HKDF-SHA-256: RFC 5869 TC1 and TC3 from the same file. `extract` and
  `expand` are checked apart and together, the spike's one-shot check,
  and TC3 exercises the empty salt and info.
- The reduction theorems as `example` assertions the build enforces,
  closed by `rfl` (CLAUDE.md, "Proofs and tests").
- Empty-input and block-boundary HMAC: the spike's key lengths 0, 1,
  63, 64, 65, 128, and 200. The pure side closes here, and the
  production side closes at W3.3.

## Vector stance

The captured crypto vectors sit in one file,
`Tests/vectors/hashes-rfc.json`. It holds three families: `sha512`
(four entries), `hmacSha256` (RFC 4231 TC1 and TC2), and `hkdfSha256`
(RFC 5869 TC1 and TC3, with the `prk` and `okm` fields). The
provenance field names the sources, RFC 4231, RFC 5869, and the FIPS
180-4 examples, and records that every primitive is cross-checked
against the production path at runtime. SHA-256 and SHA-1 have no RFC
file of their own in `Tests/vectors/`. SHA-256 is anchored through the
inline NIST examples, the multihash spec vectors in
`multihash-examples.json`, and the W3.3 cross-check, whose production
side routes to `LeanHazmatSha256`. SHA-1 is
anchored through the multihash spec vectors, and the backend SHA-1
binding that root W3.2 lands brings it into the W3.3 cross-check;
the family is no longer closed by vectors alone. All files arrive
on `main` through root W0.3.

The sweep lengths above are the package's own tests, in the spike's
shape. The production comparisons inside them are W3.3's to run.
