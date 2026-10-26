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
  carries the entry list and a proof field stating that every entry
  fits the varint budget of `codec/varint`. `Value` has one constructor
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
- `Codec Fields` and `LawfulCodec Fields` are the instances of §3.2.
  The generic harness of `base/bytes` runs once for them.
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
   `decodeFields (encodeFields fs)` returns `fs` for every
   `fs : Fields`, over the model, closed by `rfl`, `simp`, and `omega`
   (§6; PRINCIPLES 5.1). The law needs no hypothesis, because the type
   itself carries the budget fact; that is what makes `LawfulCodec
   Fields` provable. The decoder checks the budget at the boundary and
   constructs the proof field (§3.7). The message layer's field table
   constructs well-formed entries by construction, and the generic
   encoder goes through `toFields`.
5. **The model pin.** The `ByteArray` path is pinned to the model
   through the generic harness of `base/bytes`, in the
   `decodeFieldsB? b = decodeFields? (toNatList b)` shape (§4.2, §6;
   `base/bytes` docs, owned contracts 1 and 2).

## The error boundary

`Pb.Error` is the package-owned error inductive (§3.5). It has the
arms of this package:

- `framing : DecodeError → Pb.Error` carries the framing errors of the
  `codec/varint` boundary verbatim. A cut tag or a cut length prefix
  reports `truncated`. A prefix that runs past the budget reports
  `malformed` (`codec/varint` docs; §3.2).
- `badField` reports a tag whose field number cannot fit the budget.
  This is the rule the varint layer enforces at its boundary
  (ARCHITECTURE §4.3): a value that cannot complete within the budget
  is a protocol error, and the reader stops waiting.
- `badWireType` reports a tag whose wire type has no constructor: a
  group marker, wire type 3 or 4.

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
