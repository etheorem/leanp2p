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
| `Bytes/Take.lean` | `take?`, the split of a length-prefixed payload off the model input, with its three lemmas, and `sliceAt?`, the same step on `ByteArray`; every codec that reads a length reads the bytes through it, so the `truncated`/`malformed` split has one home |
| `Bytes/Blob.lean` | `Blob`, the wrapper that puts bytes inside core data with a `Repr` (ARCHITECTURE §3.2, §3.3), so the instance has one home |

All declarations live in the `Bytes` namespace. The root module
re-exports the public submodules.

The spike module `Crypto/Bytes.lean` is the reference (ARCHITECTURE
§10, row 2). Its conversions and `xorWith` move here with their types.

## Public surface

The names are the root names (ARCHITECTURE §7, row 2). The types
follow the spike.

- `ofNatList : List Nat → ByteArray` builds one byte per model value,
  taken mod 256. `toNatList : ByteArray → List Nat` is its inverse:
  `ofNatList (toNatList b) = b` holds for every `b`. Its length is the
  array's size (`lengthToNatList`), and each entry is below 256
  (`ltOfMemToNatList`): the two facts a codec over the model needs to
  bound a payload it carries.
- `ofString : String → ByteArray` and `toString? : ByteArray → Option
  String` convert over UTF-8. `toString?` returns `none` only for
  bytes with no UTF-8 reading, and the docstring states that single
  meaning (§3.5).
- `toHex : ByteArray → String` prints two lowercase digits per byte.
  `ofHex? : String → Option ByteArray` accepts lowercase ASCII hex
  only: the digits `0` to `9` and the letters `a` to `f`. It returns
  `none` for an odd length, and for every other character, uppercase
  included. This matches the spike.
- `xorWith (key : ByteArray) (data : ByteArray) : ByteArray` XORs each
  byte of the data with the repeating key. An empty key returns the
  data unchanged.
- `take? (k : Nat) (l : List Nat) : Except DecodeError (List Nat ×
  List Nat)` splits the first `k` bytes off the model input. A non-byte
  among the bytes present is `malformed`, and fewer than `k` bytes is
  `truncated`. The caller checks its length cap before the take (§5.1).
  `sliceAt? (b : ByteArray) (pos k : Nat)` is the same step on
  `ByteArray`, by offset.
- `Blob` wraps a `ByteArray` for core data. It derives
  `DecidableEq`, and its `Repr` prints hex.
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
5. **The harness shape is fixed by contract, and its value is scoped.**
   The shape `∀ [Codec α] [LawfulCodec α]` comes from root
   ARCHITECTURE §3.2 and from owned contract 2 above.
   `checkRoundTrips` runs the codec on samples, and
   `checkRoundTripsEqTrue` states that it always answers true. On a purely
   logical codec the check repeats what the kernel already proved. It
   matters only where the runtime implementation of a `Codec` method can
   differ from its model definition, through `@[implemented_by]` or
   `@[extern]`. No codec in this package has one. Production byte paths
   are the job of `checkModelPins`, and the suite also asserts that the
   pin reports a wrong decoder.
6. **`xorWith` carries two theorems.** `xorWithEmpty` and
   `xorWithInvolution` hold. The byte-level index law is pinned by the
   behavior suite. Proving that law as a theorem is follow-up work, and the
   package records it here.

## Decisions

- **The `List Nat` model exists for the proofs.** The verified cores
  prove their round-trip and inverse theorems over it, closed by
  `rfl`, `simp`, and `omega` (§6; PRINCIPLES 5.1). §7, row 2 records
  the point: the package exists for the proof-facing model.
- **The wire path gets `ByteArray` decoders anyway.** The wire runs on
  bytes, so the production decoders take `ByteArray`. Each fuzz pin
  ties a production decoder to its model decoder, so the proof view
  and the wire view cannot drift (§4.2, §6; PRINCIPLES 5.1).
- **The model read goes through `ByteArray.data.toList`.** At that
  layer `List.toArray` is `fun xs => { toList := xs }` and
  `Array.toList` is `fun self => self.1`, and both are `reducible`. The
  round trip therefore closes on `Array.toList_inj` with no induction,
  and `ofNatListData` holds by `rfl`. So `toNatList` reads
  `ByteArray.data.toList`, and `ofNatList` builds through
  `ByteArray.mk`.
- **The public accessor is bridged by a theorem.** `ByteArray.toList`
  runs a loop that carries `@[irreducible]`, so `unfold` stalls. Lean
  generates the equation lemma `ByteArray.toList.loop.eq_1`, and
  `toListLoopSpec` inducts on it. `toListEqDataToList` and
  `toNatListEqToListMap` then prove that `toNatList` reads the same
  bytes as `ByteArray.toList`, for every `ByteArray`. The behavior suite
  additionally pins the runtime path over arrays that `ofNatList` did not
  build.
- **`decode?` returns `Except DecodeError`.** An `Option` decoder
  cannot tell `truncated` from `malformed`, and §3.5 and §5.2 need the
  distinction. The two `Option` returns here, `toString?` and
  `ofHex?`, have one `none` meaning each, stated in the docstring, as
  §3.5 allows.
- **`take?` lives here, with its lemmas.** `net/streams` framing and
  the yamux core both split a payload off the model input at a length,
  with the same two failures. §3.8 asks for one home per fact, and this
  package owns `DecodeError` and the model. The step knows no prefix
  shape and no cap: the caller reads its length and checks its cap
  first (§5.1).
- **One `Blob` for the bytes inside core data.** A pure core's state,
  events, and actions derive `Repr` and `DecidableEq` so a test compares
  and prints them by value (§3.3). Core Lean gives `ByteArray` no
  `Repr`, and §3.2 rules out an instance on a type the package does not
  own, so a core holds its bytes in `Blob`. The yamux core does; every
  later core uses the same wrapper, so the instance has one home
  (§3.8). The `Repr` prints hex, which keeps a frame short in a failed
  test.
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
