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
| 2 | W5.1, W3.2 | root W6.1: the package's own RLP behind its `Codec` surface (ARCHITECTURE, "The RLP is the package's own"), the ENR record with its `v4` signature over the keccak-256 digest, and the peer-id/multiaddr mapping | the unit 2 milestones below pass, and the root W6.1 row holds |

Units 0 and 1 are done. The unit 1 suite is `Tests/Identity.lean`, and
the theorems live in `Libp2p/Identity/KeyType.lean` (the table),
`Libp2p/Identity/Keys.lean` (the `Keys` round trip), and
`Libp2p/Identity/PeerId.lean` (inlining at the threshold).

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

- RLP: the package's own codec (ARCHITECTURE, "The RLP is the
  package's own"). `LawfulCodec Rlp.Value` proves the round trip and
  the canonical-form law in the kernel, with no `native_decide`. The
  ethereum/tests `RLPTests` vectors are the acceptance test: every
  valid case encodes to its bytes and decodes back on both the model
  and the `ByteArray` path, and every invalid case is refused on
  both. The package's own cases pin the error kind of each rule,
  `truncated` or `malformed`. The harness of `base/bytes` pins the
  `ByteArray` decoder to the model.
- ENR: the EIP-778 record example, vendored with the text, signs and
  verifies. The digest is the keccak-256 of the RLP content, through
  the facade, and the signature verifies over the recovery path, so
  the pairs read back, and the node id matches the text's. The
  high-S twin of the signature fails (ARCHITECTURE, contract 5). A
  record with one tampered pair fails the signature, and no pair is
  readable. Each decode rule has one rejection: the 300-byte cap,
  trailing bytes, the list shape, a non-canonical `seq`, unsorted and
  repeated keys, a missing or unknown scheme, a key that is not 33
  bytes, and a signature that is not 64 bytes. The record
  round-trips through encode and decode.
- The signer: the example's private key, `seq`, and pairs re-sign to
  the record's own bytes, since the backend signer and go-ethereum
  both take the RFC 6979 nonce. A stale `id` or `secp256k1` pair is
  replaced. The signer refuses a repeated key, the zero scalar, a
  `seq` past 64 bits, and a record over 300 bytes.
- The text form (ARCHITECTURE, contract 7): the record prints to the
  example's text, and the text reads back to the record. A text
  without the `enr:` prefix is refused, and so is each case of
  `enr-text-sigp.json`.
- The mappings: the `secp256k1` entry derives the peer id the record
  belongs to, and go-libp2p derives the same id from the same key.
  The `ip`, `tcp`, and `udp` entries build the `Multiaddr`. Mapping
  a record to an address and back returns the same entries. A
  dual-stack record maps its IPv6 address with `tcp6`, or with `tcp`
  when it has no `tcp6`. In the reverse map, an IPv6 port equal to
  the `tcp` port stays in `tcp`, and a different one becomes `tcp6`.

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

Root §8 calls the ENR codec new work, so the spike captured nothing
for it. Unit 2 pins three sources in `VECTORS.lock`, and
`scripts/extract-vectors.py` extracts four files from them:

- `enr-eip778.json`: the example record of EIP-778
  (`vendor/eips/EIPS/eip-778.md`, "Test Vectors", CC0): its bytes,
  the text form, the private key, the node id, and the RLP structure
  the text lists.
- `rlp-valid.json` and `rlp-invalid.json`: ethereum/tests
  `RLPTests/rlptest.json` (28 cases) and `invalidRLPTest.json` (26
  cases), MIT. The extractor writes each valid input as an item tree,
  under the RLPTests conventions: a string is its UTF-8 bytes, an
  integer or a `#`-prefixed big integer is its minimal big-endian
  bytes.
- `enr-text-sigp.json`: the two text forms that sigp/enr refuses, from
  its test `test_read_enr_base64url_decoding_enforce_no_pad_no_extra_trailingbits`
  (`vendor/sigp-enr/src/lib.rs`, MIT). Each case records sigp's error
  and go-ethereum's answer (ARCHITECTURE, contract 7).

The keccak-256 digest is vector-pinned by the `LeanHazmatKeccak`
suite and the fixed cases of the empty string and `abc` (the backend
pair's plan), and the record fixture pins the end-to-end path. The
peer id of the example key has no captured vector; go-libp2p at the
vendored commit derives it, and the suite states the string.

Three more pins hold the sources that contracts 5 and 7 cite, with no
extracted file: `vendor/go-ethereum`,
`vendor/rustcrypto-elliptic-curves`, and `vendor/rustcrypto-signatures`.
`vendor/sigp-enr` serves both contracts, and the text file comes from
it.
