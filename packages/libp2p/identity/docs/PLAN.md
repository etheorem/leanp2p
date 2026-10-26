# leanp2p identity: plan

This plan refines the root `docs/PLAN.md` for `libp2p/identity`. The
root plan owns the order across packages (PLAN.md, "How to read this
plan"). The package carries two root units: unit 1 below is the root
unit W5.1, with deps W2.2, W2.3, and W3.3, and unit 2 is the root
unit W6.1, with deps W5.1 and W3.2. The done-when of each unit is
the root row plus the root definition of done: the surface follows
ARCHITECTURE §4.9, shaped by §3, the owned contracts hold, the
carried tests pass, the suite passes under `+RTS -N1`, and the
import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W2.2, W2.3, W3.3 | root W5.1: `KeyType`, `PubKey`/`PrivKey` with the `ProtoMessage` instances, the per-type marshalings, the strict unmarshal, and `PeerId` | the unit 1 milestones below pass, and the root W5.1 row holds |
| 2 | W5.1, W3.2 | root W6.1: the RLP wrapper over the etheorem monorepo's RLP package behind the package's `Codec` surface, the ENR record with its `v4` signature over the keccak-256 digest, and the peer-id/multiaddr mapping | the unit 2 milestones below pass, and the root W6.1 row holds |

Unit 0 is done.

## Consumers

`libp2p/core` (W5.2) holds `PeerId`-typed seams, so its structures
name this package's type. `libp2p/security` (W5.3) checks the static
key of the Noise handshake payload against the peer id it claims.
`libp2p/host` (W5.6) keys the dedup table and the peerstore by
`PeerId`; W5.1 is a root dependency of its row. W6.3 (req/resp) and
W6.4 (gossipsub) carry peer ids through their messages. The keys suite
of §7 row 10 is the suite this plan's milestones define.

## Test milestones

Behavior tests close the units. The suite follows the root test-runner
layout of W0.2, and the `-N1` pass is required. Each listed rejection
is a concrete case in the suite, so no milestone is vacuous.

Milestones for unit 1:

- Marshal and unmarshal: the eight key protobufs of
  `keys-peer-ids.json` (private and public for all four types) decode
  byte-exact and re-encode to the same bytes. The go fixtures of
  `keys-go-libp2p.json` marshal round-trip and derive the public key
  from the private one; the marshalings side of that file is unit 1's,
  as the backend pair's vector stance says.
- Sign and verify: each key type signs a fixed message and verifies
  the signature through the facade. The RSA signature is
  byte-identical on re-sign, and the secp256k1 and ECDSA cases
  contract on verification (the backend pair records the reason).
- Strict rejections, each concrete: a 31-byte Ed25519 public `Data`
  fails; a 34-byte secp256k1 public `Data` fails; a key-type code of
  4 fails in `ofCode?`; an RSA `Data` of 4 bytes fails the DER shell.
  The RSA 2048 to 8192 bit range sits at the backend verifier, and
  the backend plan carries its regressions.
- Peer id: the three string examples in `keys-peer-ids.json` decode
  and re-encode, the CIDv1 `bafz...` form, the base58 `Qm...` form,
  and the identity-inlined `12D3KooW...` form. The inlining boundary:
  a marshaled key of exactly 42 bytes inlines, and one byte over
  hashes with sha2-256. The print-form round-trip: parse a string,
  print it back, and get the same string (PRINCIPLES 2.1).
- Marshal determinism: two marshals of one key are byte-identical,
  for every type.

Milestones for unit 2:

- The upstream track is the first step: the RLP package lives in the
  etheorem monorepo (`etheorem/etheorem`, LGPL-3.0, toolchain
  v4.29.1) and is not yet on its `main`. Unit 2 tracks its landing
  or its per-package publication, adds the require block with a
  pinned git rev, runs `lake update`, commits `lake-manifest.json`,
  and checks that the pin builds under the v4.34 toolchain. The
  recorded fallback is the package's own small RLP if the upstream
  does not land in time or the skew does not close. When the suite
  cites upstream proofs, each citation records whether the proof
  closes in the kernel or through `native_decide` (CLAUDE.md,
  "Proofs and tests").
- RLP: the upstream vector suite runs through
  the package's `Codec` surface, and that is the acceptance test. The
  round-trip, injectivity, and canonicality proofs are upstream's;
  the suite cites them and re-proves none. The wrapper's error
  mapping rejects malformed input with the package's own error.
- ENR: the EIP-778 record example, vendored with the text, signs and
  verifies. The digest is the keccak-256 of the RLP content, through
  the facade, and the signature verifies over the recovery path, so
  the pairs read back. The recovery path is the tested strategy of
  the two contract 5 allows, so an implementer who picks
  S-normalization changes the milestone with it. A record with one
  tampered pair fails the signature, and no pair is readable. The
  record round-trips through encode and decode.
- The mappings: the `secp256k1` entry derives the peer id the record
  belongs to, and the `ip`, `tcp`, and `udp` entries build the
  `Multiaddr`. Mapping a record to an address and back returns the
  same entries.

## Vector stance

The spike captured three key files, and all of them arrive on `main`
through root W0.3 (ARCHITECTURE §6). `VECTORS.lock` pins their
sources:

- `keys-peer-ids.json`: the key protobufs of the peer-ids spec, from
  `vendor/specs` at commit `78e75c6`, plus the peer-id string
  examples in its `peerIdExamples` field. It pins the marshalings and
  the peer id together.
- `keys-go-libp2p.json`: the fixtures from go-libp2p
  `core/crypto/test_data` at commit `3c2c902`. The file's envelopes
  are the W5.1 marshalings, and the raw fields feed the backend
  suites; the two plans split it that way.
- `keys-rfc8032.json`: the RFC 8032 Ed25519 vectors. The backend pair
  owns them for its bindings; unit 1 uses the same fixed-message
  scheme through the facade.

Nothing in `VECTORS.lock` pins ENR or RLP. Root §8 expects this: it
calls the ENR codec new work. EIP-778 and the discv5 specification's
ENR section govern the surface, and the spike branch vendors neither
text under `vendor/specs`. Landing unit 2 starts by vendoring both
texts and committing the EIP-778 record fixture with recorded
provenance, the way the backend plan handles its generated
certificates. The keccak-256 digest is vector-pinned by the
`LeanHazmatKeccak` suite and the fixed cases of the empty
string and `abc` (the backend pair's plan), and the record fixture
pins the end-to-end path. The RLP family closes through the upstream
vector suite of the etheorem RLP package, run through the package's
`Codec` surface. The round-trip, injectivity, and canonicality proofs
are upstream's, and the suite records that provenance (§6).
