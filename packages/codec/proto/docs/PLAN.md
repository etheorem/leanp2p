# leanp2p proto: plan

This plan refines the root `docs/PLAN.md` for `codec/proto`. The root
plan owns the order across packages (PLAN.md, "How to read this plan").
Unit 1 below is the root unit W2.2, and it depends on W1.2 and W2.1.
Its done-when is the root row plus the root definition of done: the
surface follows ARCHITECTURE §4.5, the owned contracts hold, the
carried tests pass, the suite passes under `+RTS -N1`, and the import
lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W1.2, W2.1 | the modules of the package architecture (root W2.2): the wire model, the core with its theorem and instances, the lookups, the `ProtoMessage` class with the generic encoder, and the `ByteArray` path | the root W2.2 row holds: `Fields`, encode/decode, last-wins singular lookups, the round-trip theorem, and the `ProtoMessage` class exist |

Unit 0 is done. Unit 1 is the only implementation unit of the
package.

## Consumers

Root W2.2 feeds everything above that carries a protobuf message (root
PLAN). The first consumer is W5.1 (`libp2p/identity`): the `Keys`
messages over a hand-written field table. W5.3 adds
`NoiseHandshakePayload`, and W5.7 adds `Identify`. The class and the
generic encoder let those packages write tables without a codec each
(§3.2, §4.5). The field tables live in the libp2p packages; none comes
down here (§4.5).

## Test milestones (unit 1)

Behavior tests close unit 1. The suite follows the root test-runner
layout of W0.2, and the `-N1` pass is required.

- A fixed wire table: a small message encoded to named bytes, checked
  in the model form and in the `ByteArray` form. The sample covers the
  four wire types, an empty `bytes` payload, and a field number near
  the top of the tag range.
- Round-trip over generated `Fields`, through the generic harness of
  `base/bytes`. The generator produces well-formed fields, with field
  numbers inside the budget, and constructs the proof field; the
  package writes no round-trip loop of its own (`base/bytes` docs,
  owned contract 2).
- Determinism: two encodes of one `Fields` give identical output. At
  the message layer, the field table fixes the emit order, so encoding
  a message is deterministic by construction (ARCHITECTURE §4.5).
- Byte-exact cycle: a decode-encode cycle over a generated `Fields`
  returns the same bytes.
- Last-wins: a `Fields` with two occurrences of one singular tag, where
  the lookup returns the second value.
- Unknown fields: append an unknown tag, decode, re-encode. The unknown
  tag is still present, and its payload survives byte-exactly.
- A cut payload or a cut length prefix reports through the
  `codec/varint` boundary: `truncated` while a byte could still
  complete the varint, `malformed` past the budget (`codec/varint`
  docs).
- A field number past the budget reports as `Pb.Error.badField` through
  the core, and as `.malformed` through the `Codec Fields` instance.
- An impossible wire type reports as `Pb.Error.badWireType` through the
  core, and as `.malformed` through the `Codec Fields` instance.
- Rejected garbage from the spike suite carries over: a truncated
  `fixed64`, a length prefix that promises more bytes than the input
  holds, a lone tag.

## Vector stance

The spike captured protobuf message vectors. `Tests/vectors/protobuf-messages.json`
holds four message cases in hex: Identify, NoiseHandshakePayload,
PeerRecord, and Envelope. The provenance field records the source: the
field tables come from the vendored spec sources, and the extraction
script's mini-encoder produced the bytes, because go-libp2p was not
available in the build environment. `VECTORS.lock` also pins the
go-libp2p key protobuf fixtures (`core/crypto/test_data`), which
arrive as `keys-go-libp2p.json`. The vector infrastructure lands on
`main` with root W0.3, and this package reaches both files through it.

The wire layer preserves the input order, so this package checks the
captured cases byte-exactly in the `Fields` view: decode each case to
`Fields`, re-encode, and compare with the captured hex. The typed
checks, decode into `Identify` and compare the message fields, need
the field tables of the libp2p packages. The spike ran them from
`Crypto/Messages.lean`, and they land with the root W5 units.
