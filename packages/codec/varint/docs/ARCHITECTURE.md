# leanp2p varint: architecture

`codec/varint` implements the unsigned varint (LEB128) of the
multiformats spec. Protobuf and the multiformats encodings both frame
lengths with it, and neither of them owns it (ARCHITECTURE §2). It is
the first codec on the stack, and the first consumer of the `Codec`
classes and the `DecodeError` boundary that `base/bytes` defines
(ARCHITECTURE §3.2). The over-long rule and its reason sit in "The
error boundary" below.

## Modules

| Module | Holds, and why |
|---|---|
| `Varint.lean` | the root module; one import line per public submodule |
| `Varint/UVarint.lean` | the newtype `structure UVarint where val : Nat` with its proof field, the model core `encode` and `decode?`, and the `Codec UVarint` / `LawfulCodec UVarint` instances; the instances live with the type (ARCHITECTURE §3.2), and the 9-byte budget constant lives here, its one home (PRINCIPLES 1.5) |
| `Varint/Theorems.lean` | the theorems over the model beyond the instance law: the suffix form, the accepted-input split, and the budget lemma (ARCHITECTURE §6); the instance-law proof lives with the instance, in `Varint/UVarint.lean` |
| `Varint/Bytes.lean` | the production `ByteArray` path, `encodeB` and `decodeB?`; it imports the 9-byte budget constant from `Varint/UVarint.lean` |

All declarations live in the `Varint` namespace. The root module
re-exports the public submodules.

The `Codec` instance sits on the wrapped type. §3.2 keeps instances
off the core types, and its wrap example is this package's newtype.
The newtype is a proof-carrying newtype of §3.7:
`structure UVarint where val : Nat` with a proof field `val < 2^63`.
The decoder checks the budget once at the boundary and constructs the
field. A core that takes `UVarint` never checks the size again.

The spike module `Net/Varint.lean` is the reference (ARCHITECTURE
§10, row 3); its one module splits across the table above.

## Public surface

The names are the root names (ARCHITECTURE §7, row 3), shaped by the
mechanisms of §3:

- `encode : UVarint → List Nat` writes the encoding over the byte
  model. `decode? : List Nat → Except DecodeError (UVarint × List
  Nat)` returns the value and the rest.
- `encodeB : UVarint → ByteArray` and `decodeB? : ByteArray → Except
  DecodeError (UVarint × Nat)` are the production forms. The `Nat`
  counts the consumed bytes, so a framing layer knows where its
  payload starts.
- `Codec UVarint` and `LawfulCodec UVarint` are the instances of
  §3.2. One instance per type, on the wrapped type alone.

Both decoders check the budget at the boundary and construct the
proof field of `UVarint` after it (§3.7).

The encoding rule is the multiformats rule. Each byte carries 7 bits,
the high bit marks a continuation, and the first byte holds the least
significant group. Encodings are minimal, and the decoder accepts at
most 9 bytes, so every value stays inside 63 bits (ARCHITECTURE
§4.3).

## The error boundary

`DecodeError` is the shared inductive of `base/bytes`. This package
reports through it in the terms of the `base/bytes` docs, "Public
surface" and owned contract 4:

- An input that ends while more bytes could still complete a
  within-budget varint reports `truncated`. The reader may keep
  waiting (ARCHITECTURE §3.2).
- A prefix that reaches the 9-byte budget without a terminator reports
  `malformed`. Nine continuation bytes spend the budget, and no byte
  after it completes the value.
- A non-minimal encoding reports `malformed`. A final group of zero
  after a continuation byte is the non-minimal case. `0x80 0x00` for
  zero is the example.

The layer above acts on the split: it keeps waiting on `truncated`,
and it tears the connection down on `malformed` (ARCHITECTURE §5.2;
`base/bytes` docs).

The budget case is the rule this package exists to state (ARCHITECTURE
§4.3): a varint that cannot complete within the byte budget is a
protocol error, and the decoder reports it as `malformed`. PRINCIPLES
2.3 gives the reason: a hostile peer must not turn its length field
into our unbounded wait. The decoder ends the wait at the source, so
every framing layer above inherits the bound and never re-derives it
(PRINCIPLES 1.5).

## Decisions

- **Minimal forms only, against the go decoder.** Go accepts the
  non-minimal `0x81 0x00` and returns 1. The multiformats spec
  requires minimal encodings, and the spec wins (PRINCIPLES 2.1). The
  spike enforced the same rule.
- **`decode?` returns `Except DecodeError`.** The spike decoder
  returns `Option`. An `Option` cannot tell `truncated` from
  `malformed` (ARCHITECTURE §3.5), and §7 ports every `Option` result
  to the error channels.
- **The newtype carries the budget fact.** Per §3.7, the decoder
  checks a size that the spec fixes at the boundary and carries the
  fact to every use. The proof field keeps the `LawfulCodec` law of
  `base/bytes` unconditional. The alternative, a hypothesis on the
  class law, is a `base/bytes` contract change, and a contract change
  starts at the root.

## Theorems

The theorems live on the pure core, over the `List Nat` model, closed
by `rfl`, `simp`, and `omega` (ARCHITECTURE §6; PRINCIPLES 5.1):

- The round-trip law of `LawfulCodec`: `decode? (encode v)` returns
  `(v, [])` for every `v : UVarint`, and a decode result re-encodes
  to its input. The law needs no hypothesis, because the type itself
  carries the budget fact; that is what makes `LawfulCodec UVarint`
  provable.
- The suffix form: for every `v : UVarint`, `decode?
  (encode v ++ rest)` returns `(v, rest)`. A framing layer decodes a
  length off the front of a buffer and trusts the split.
- The accepted-input split: a successful decode consumed exactly the
  encoding of its value, and the rest comes back untouched.
- The budget lemma: the encoding of a `UVarint` is at most 9 bytes.
  The proof field makes this true at the type level, and the encoder
  preserves it (ARCHITECTURE §4.3).

A `List Nat` input can hold 256 or more in a byte position.
`decode?` reports `malformed` for it, so the ported accepted-input
theorem drops the spike's side condition on the input bytes.

The `ByteArray` decoder carries no theorem of its own. The generic
harness of `base/bytes` pins it to the model over generated inputs, in
the `decodeB? b = decode? (toNatList b)` shape (ARCHITECTURE §4.2,
§6; `base/bytes` docs, owned contracts 1 and 2).

## What the package must not depend on

- No import from a group above `codec`: no crypto, no net, no libp2p
  (ARCHITECTURE §2).
- No import from the codec group above it: no `codec/proto`, no
  `codec/multiformats` (ARCHITECTURE §2, downward only).
- Within `base`, `base/bytes` only. The package is pure; it spawns no
  task and holds no channel, so it has no use for `base/conc`.
- No framing or cap knowledge beyond its own 9-byte budget. §5.1 puts
  the framing caps at the framing layers, and each layer sizes its own
  reads.
