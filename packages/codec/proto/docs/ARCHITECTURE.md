# leanp2p proto: architecture

`codec/proto` implements the protobuf wire codec over the `List Nat`
byte model, with lengths framed by `codec/varint` (ARCHITECTURE §4.5).
It carries the `ProtoMessage` class (§3.2) that every libp2p protobuf
message implements above this package. The field tables of `Keys`,
`Identify`, `NoiseHandshakePayload`, and the rest live in the packages
above (§4.5).

## Modules

| Module | Holds, and why |
|---|---|
| `Proto.lean` | the root module; one import line per public submodule |
| `Proto/Wire.lean` | the wire model: the proof-carrying `Fields` of §3.7, `Value`, the closed inductive with one constructor per wire type, and `Pb.Error`, the package-owned error inductive (§3.5) |
| `Proto/Core.lean` | the codec core `encodeFields` and `decodeFields?`, the round-trip theorem, and the `Codec Fields` / `LawfulCodec Fields` instances, proved from the theorem |
| `Proto/Lookup.lean` | the field lookups: `getVarint?`, `getBytes?`, `getSub?`, `getStr?`, `getAllVarints`, `getAllBytes`, `getAllStrs`, `hasField` |
| `Proto/Message.lean` | the `ProtoMessage` class with its two methods, and the one generic encoder over the class (§3.2) |
| `Proto/Bytes.lean` | the production `ByteArray` path, `encodeFieldsB` and `decodeFieldsB?` |

All declarations live in the `Pb` namespace. The root docs name the
types that way (§3.2, §3.7), so the root names stand verbatim:
`Pb.Fields`, `Pb.Error`. The class keeps the root name `ProtoMessage`,
and the root module re-exports the public submodules. The instances sit
in `Proto/Core.lean`, beside the theorem they are proved from; the type
sits one module over, in `Proto/Wire.lean`.

The spike module `Crypto/Pb.lean` is the reference (§10, row 5). Its
wire model and its message-structure helpers split across the table
above.

## Public surface

The names are the root names (§7, row 4), shaped by the mechanisms of
§3:

- `Fields` is a proof-carrying structure in the shape of §3.7: it
  carries `entries : List Entry` and `valid : ∀ e ∈ entries, e.Valid`.
  `Fields.ofList?` checks a raw table. `Fields.empty` constructs the
  empty message. `Value` has one constructor
  per wire type: `varint`, `fixed64`, `bytes` (length-delimited),
  `fixed32`. The group markers, wire types 3 and 4, have no
  constructor, so a closed match rejects them (§3.4).
- `encodeFields : Fields → List Nat` and `decodeFields? : List Nat →
  Except Pb.Error (Fields × List Nat)` are the model core.
  `encodeFieldsB : Fields → ByteArray` and `decodeFieldsB? : ByteArray
  → Except Pb.Error (Fields × Nat)` are the production forms. The `Nat`
  counts the consumed bytes, as in `codec/varint`.
- The singular lookups return the last occurrence of the field:
  `getVarint?`, `getBytes?`, `getSub?`, `getStr?` (§7, row 4). `getSub?`
  decodes the payload through the core, and `getStr?` over UTF-8
  through `base/bytes`. The repeated lookups return every occurrence in
  wire order: `getAllVarints`, `getAllBytes`, `getAllStrs`. `hasField`
  reports presence.
  A last occurrence with another wire type gives a lookup miss.
  `getSub? : Nat → Fields → Except Error (Option Fields)` separates
  an absent payload from a nested decoding error. `getStr?` returns
  `none` for invalid UTF-8. `getAllStrs` skips invalid UTF-8 payloads.
- `Codec Fields` and `LawfulCodec Fields` are the instances of §3.2.
  They use the merged `Bytes` classes. `Fields` derives `DecidableEq`
  for the shared `checkRoundTrips` and `checkModelPins` harness.
- `ProtoMessage α` carries `toFields : α → Pb.Fields` and `ofFields? :
  Pb.Fields → Except Pb.Error α` (§3.2). The instance holds the field
  table as data. Over the class, `encodeMessage : α → List Nat` and
  `encodeMessageB : α → ByteArray` are the one generic encoder that
  serves every message: they apply `encodeFields` to `toFields`.
  `decodeMessage?` and `decodeMessageB?` are the generic counterparts:
  decode to `Fields`, then hand the result to `ofFields?`.

## Owned contracts

1. **Deterministic encoding by construction.** The encoder emits the
   fields in the order of its input, and every integer it writes goes
   through `codec/varint`, so each varint is minimal and within the
   9-byte budget (`codec/varint` docs). Two encodes of one `Fields`
   value give the same bytes. At the message layer, the field table of
   a `ProtoMessage` instance is a fixed emit order, so encoding a
   message is deterministic by construction (§4.5).
2. **Unknown fields survive a decode-encode cycle, byte-exactly.** The
   decoder returns every field, known and unknown, in wire order
   (§4.5). A consumer above must be able to re-emit what it did not
   understand, in the bytes it received.
3. **Last-wins for singular lookups.** A field that appears twice on
   the wire keeps both occurrences in `Fields`, and the singular lookup
   scans the wire order and returns the last one (§4.5). The repeated
   lookups return both.
4. **The round-trip theorem on the pure core.** The theorem states
   `decodeFields? (encodeFields fs)` returns `(fs, [])` for every
   `fs : Fields`, over the model, closed by `rfl`, `simp`, and `omega`
   (§6; PRINCIPLES 5.1). The law needs no hypothesis, because the type
   itself carries the budget fact; that is what makes `LawfulCodec
   Fields` provable. The decoder checks the budget at the boundary and
   constructs the proof field (§3.7). The message layer's field table
   constructs well-formed entries by construction, and the generic
   encoder goes through `toFields`.
5. **The model pin.** The independent `ByteArray` decoder is pinned to the model
   through the generic harness of `base/bytes`, in the
   `decodeFieldsB? b = decodeFields? (toNatList b)` shape (§4.2, §6;
   `base/bytes` docs, owned contracts 1 and 2).
   The harness adapter rejects a successful decode that does not consume
   the complete buffer. `encodeFieldsBModel` proves the encoder's byte
   conversion is lossless through the real `Bytes` implementation.

## The error boundary

`Pb.Error` is the package-owned error inductive (§3.5). It has the
arms of this package:

- `framing : DecodeError → Pb.Error` carries the framing errors of the
  `codec/varint` boundary verbatim. A cut tag or a cut length prefix
  reports `truncated`. A prefix that runs past the budget reports
  `malformed` (`codec/varint` docs; §3.2).
- `badField` reports an invalid field number. Field zero and numbers
  at least `2^29` fail this check. `Fields.ofList?` also uses this
  error for invalid values in a raw field table.
- `badWireType` reports a tag whose wire type has no constructor: a
  group marker, wire type 3 or 4, or the invalid wire type 6 or 7.

The two entry points differ in what a caller sees. The core
`decodeFields?` reports `Pb.Error`, so a caller can match the wire
case. The `Codec Fields` instance reports through `DecodeError`, the
shared vocabulary of every codec (§3.2; `base/bytes` docs, owned
contract 4). It maps `framing e` to `e`, and `badField` and
`badWireType` to `.malformed`, because a wire violation is a protocol
error and the reader stops waiting. The layer above keeps waiting on
`truncated` and tears the connection down on `malformed` (§5.2).

`ofFields?` returns `Except Pb.Error` too (§3.2). The message
instances above report their validation failures through the same
type, and each maps it into `Core.Error` once, at its own seam (§3.5).

## Decisions

- **`Fields` is a proof-carrying structure.** §3.7, as amended, lists
  it among the proof-carrying types. The fact is constructed at the
  boundary check and by the message layer's field tables, and a core
  that takes `Fields` never re-checks a size. The fact is what makes
  the `LawfulCodec Fields` law hold with no hypothesis, the same
  pattern the varint package set; §3.2 lists `Pb.Fields` among the
  instances (`codec/varint` docs).
- **Wire types are a closed inductive.** §3.4 bans a bare `Nat` for a
  member of a spec set. The inductive has the four constructors the
  wire format allows here, and the decoder reports the absent ones
  through `Pb.Error.badWireType`.
- **`Pb.Error` is distinct from `DecodeError`.** §3.5 gives each
  package one owned inductive, and §3.2 fixes `DecodeError` as the
  shared vocabulary of the `Codec` surface. The mapping between them
  happens once, in the instance ("The error boundary").
- **Wire order in the wire layer.** The encoder emits the fields in
  the order of its input, and the decoder returns them in wire order.
  The captured vector bytes follow the emit order of their message
  (the spike's Identify case runs 5, 6, 1, 2, 2, 4, 3, 3), so a
  re-encode stays byte-exact at every layer. The earlier root wording,
  "tag order", was amended at the root, and this document follows it.

## Wire bounds and message boundaries

`Entry.Valid` requires `0 < fieldNumber < 2^29`. This follows the
[protobuf field-number range](https://protobuf.dev/programming-guides/proto3/#assigning-field-numbers)
and the uint32 tag in the
[wire encoding reference](https://protobuf.dev/programming-guides/encoding/#condensed-reference-card).
The spike's broader arithmetic bound also allowed field zero. These
checks reject those invalid tags. The raw wire codec preserves unknown
numbers, including numbers reserved by a particular message schema.
Schema validation belongs to the message table.

`Value.Valid` requires a varint below `2^63`, a fixed64 below `2^64`,
and a fixed32 below `2^32`. Length-delimited values carry a length below
`2^63` and payload entries below 256. The minimal, nine-byte varint
policy comes from root §4.3. This package does not implement the full
ten-byte protobuf uint64 range or signed scalar conversions.

`fixed64Bytes` and `fixed32Bytes` in `Proto/Wire.lean` own the fixed
widths. The validity check, model codec, production decoder and proofs
all use these constants.

The caller supplies one externally framed message. The decoder consumes
the complete buffer, so a successful model result has an empty suffix.
The production result reports the full buffer size. Concatenated field
encodings form one message; this codec cannot infer a boundary between
two messages.

The production decoder walks the `ByteArray` with a cursor. It gives
the varint dependency a window bounded by that dependency's byte budget.
It checks payload lengths against the available bytes before extraction.
A peer cannot cause an allocation from a promised length alone.

`getSub?` returns the last payload as specified by this package's
singular-lookup contract. It does not merge embedded messages. A typed
consumer that needs protobuf message-merge behavior can use
`getAllBytes` and apply its schema rules.

## Proof boundary

The package imports the merged W1.2 (`Bytes`) and W2.1 (`Varint`)
implementations. The proofs use `Varint.decodeEncodeSuffix`,
`Varint.encodeDecode`, `Varint.encodeNonempty` and `Varint.encodeBytes`
directly. No dependency mock or package-specific axiom remains.

The public theorems are `decodeEncode`, `encodeDecode`,
`encodeInjective`, `encodeFieldsBytes`, `lookupLastAppend` and
`encodeFieldsBModel`. The `Bytes.LawfulCodec Fields` instance proves
both shared laws from the core theorems. Its inverse states
`encode fs ++ rest = input`, the direction used by the real class.

The axiom audit lists only Lean's standard `propext`, `Classical.choice`
and `Quot.sound`. The proofs cover the list model and the encoder's
byte conversion. Tests pin the independent production decoder to that
model; decoder agreement remains a test claim.

## What the package must not depend on

- No import from a group above `codec`: no crypto, no net, no libp2p
  (ARCHITECTURE §2).
- Within the codec group, `codec/varint` only (§2, downward only). No
  `codec/multiformats`; the two packages are siblings in the graph.
- From `base`, `base/bytes` only: the `Codec` classes, `DecodeError`,
  and the harness. The package is pure; it spawns no task and holds no
  channel, so it has no use for `base/conc`.
- No libp2p knowledge: no message definition, no field table, no
  protocol id (§4.5).
- No framing cap of its own. §5.1 puts the caps at the framing layers,
  and this package bounds what `codec/varint` bounds.
