# leanp2p bytes: architecture

`base/bytes` is the byte floor of the stack. It holds the conversions
between the `List Nat` byte model and `ByteArray`, `String`, and hex.
It also holds the `Codec` and `LawfulCodec` classes (§3.2), the shared
`DecodeError`, and the generic round-trip harness that every later
codec package runs. The `List Nat` model is a deliberate choice:
arithmetic proofs close on it with `omega`, and the verified codec
cores state their theorems over it (§4.2; PRINCIPLES 5.1). The package
knows no wire format, and it imports no other group (ARCHITECTURE §2).

## Modules

| Module | Holds, and why |
|---|---|
| `Bytes.lean` | the root module; one import line per public submodule |
| `Bytes/Model.lean` | the conversions between the model and `ByteArray`: `ofNatList`, `toNatList`; the repeating-key `xorWith` sits beside them |
| `Bytes/Text.lean` | the `String` forms: `ofString` and `toString?` over UTF-8, `toHex` and `ofHex?` over hex |
| `Bytes/Error.lean` | the shared `DecodeError` inductive (ARCHITECTURE §3.2) |
| `Bytes/Codec.lean` | the `Codec` and `LawfulCodec` classes (ARCHITECTURE §3.2) |
| `Bytes/Harness.lean` | the generic round-trip harness; it runs once per `Codec`/`LawfulCodec` instance pair (ARCHITECTURE §3.2, §6) |

All declarations live in the `Bytes` namespace. The root module
re-exports the public submodules.

The spike module `Crypto/Bytes.lean` is the reference (ARCHITECTURE
§10, row 2). Its conversions and `xorWith` move here with their types.

## Public surface

The names are the root names (ARCHITECTURE §7, row 2). The types
follow the spike.

- `ofNatList : List Nat → ByteArray` builds one byte per model value,
  taken mod 256. `toNatList : ByteArray → List Nat` is its inverse:
  `ofNatList (toNatList b) = b` holds for every `b`.
- `ofString : String → ByteArray` and `toString? : ByteArray → Option
  String` convert over UTF-8. `toString?` returns `none` only for
  bytes with no UTF-8 reading, and the docstring states that single
  meaning (§3.5).
- `toHex : ByteArray → String` prints two lowercase digits per byte.
  `ofHex? : String → Option ByteArray` returns `none` for an odd
  length and for a non-hex digit.
- `xorWith (key : ByteArray) (data : ByteArray) : ByteArray` XORs each
  byte of the data with the repeating key. An empty key returns the
  data unchanged.
- `Codec α` carries the two methods over the model:
  `encode : α → List Nat` and
  `decode? : List Nat → Except DecodeError (α × List Nat)`
  (ARCHITECTURE §3.2).
- `LawfulCodec α` is a `Prop` class stating the round-trip law:
  `decode? (encode a)` returns `(a, [])`, and a decode result
  re-encodes to its input. Each instance proves it (§3.2, §6).
- `DecodeError` has the constructors `truncated` (more bytes may
  complete the value) and `malformed` (a protocol error, and the
  reader stops waiting).

The split lives at this floor because every codec shares the type
(ARCHITECTURE §3.2): the vocabulary must exist before the first codec
lands, and §5.2 needs the distinction at every layer. A model decoder
sees a finite list, so it cannot report an end of stream. §3.5 keeps
the end of stream on `Option` and failure on `Except`. The layer above
acts on the result: it keeps waiting on `truncated`, and it tears the
connection down on `malformed` (§3.2, §5.2). §3.2 fixes the two meanings:
`truncated` reports an input that ended while more bytes could still
complete the value, and `malformed` reports a spec violation.
PRINCIPLES 2.3 fixes one rule inside `malformed`: a length that cannot
complete within its budget is a protocol error, never a wait for more
bytes. §4.3 shows the varint case, and a violation that stays within
the budget, such as a non-minimal varint, is `malformed` too.

## Owned contracts

1. **The model pin.** Every production `ByteArray` path is pinned to
   the model by fuzz property tests, in the
   `decodeBinB b = decodeBin (toNatList b)` shape (ARCHITECTURE §4.2,
   §6; PRINCIPLES 5.1). The package pins its own conversions first,
   and the harness applies the pin to every codec above.
2. **One harness for all codecs.** The generic harness, over
   `∀ [Codec α] [LawfulCodec α]`, runs the round-trip fuzz and the
   model pin once per instance. A codec package writes no round-trip
   loop of its own (ARCHITECTURE §3.2, §6).
3. **The instance rules start here.** Every wire codec implements
   `Codec`, so the §3.2 rules bind from this floor up: one instance
   per type, no instance on `Nat`, `String`, `ByteArray`, `List`, or
   `Option` (wrap the type first), the instance lives with the type,
   no method in `IO`, and instance search stays one step deep.
4. **The shared error vocabulary.** Every codec above reports through
   `DecodeError`: a short input as `truncated`, a spec violation as
   `malformed` (ARCHITECTURE §3.2, §5.2). The caps of §5.1 live at the
   framing layers, and an over-long read reports `malformed` through
   this type.

## Decisions

- **The `List Nat` model exists for the proofs.** The verified cores
  prove their round-trip and inverse theorems over it, closed by
  `rfl`, `simp`, and `omega` (§6; PRINCIPLES 5.1). §7, row 2 records
  the point: the package exists for the proof-facing model.
- **The wire path gets `ByteArray` decoders anyway.** The wire runs on
  bytes, so the production decoders take `ByteArray`. Each fuzz pin
  ties a production decoder to its model decoder, so the proof view
  and the wire view cannot drift (§4.2, §6; PRINCIPLES 5.1).
- **`decode?` returns `Except DecodeError`.** An `Option` decoder
  cannot tell `truncated` from `malformed`, and §3.5 and §5.2 need the
  distinction. The two `Option` returns here, `toString?` and
  `ofHex?`, have one `none` meaning each, stated in the docstring, as
  §3.5 allows.
- **The spike's `fnv1a` placeholder stays out.** ARCHITECTURE §10,
  row 2 maps the whole spike module here, and the placeholder is toy
  crypto. The real digests come from the `Crypto` facade (§3.6), so
  the placeholder has no work to do in this package.

## What the package must not depend on

- No import from a group above `base`: no codec, no crypto, no net, no
  libp2p (ARCHITECTURE §2).
- No wire-format knowledge: no multicodec, no framing, no protocol id,
  and no length cap of its own (§5.1 puts the caps at the framing
  layers).
- No import of `base/conc`: the package is pure. It spawns no task,
  holds no channel, and needs no deadline.
