import Bytes
import Proto
import Libp2p.Protocols.Constants

/-!
# The snappy framing format: chunks

The `ssz_snappy` encoding compresses with snappy **frames**, the
streaming format of `framing_format.txt` (google/snappy); a compressed
chunk holds one raw block (phase0 `p2p-interface.md`, "SSZ-snappy
encoding strategy": "snappy-framing is used"). A framed stream is a run of
chunks with no padding between them and no end marker (section 1):

```
chunk ::= <type: 1 byte> <length: 3 bytes, little-endian> <body: length bytes>
```

This module is the chunk layer, and nothing above it:

* `Kind`, the closed set of chunk types (ARCHITECTURE §3.4). Every byte
  value names exactly one kind, so `ofCode?` and `toCode` are total
  inverses.
* `Chunk`, one chunk, with a `Codec` and a `LawfulCodec` instance over
  the byte model (§3.2). One chunk has exactly one spelling, so the
  round-trip law holds in both directions.
* `decodeHeaderB?`, the `ByteArray` read of the 4-byte header that the
  response core runs. The suite pins it to the model.

What a chunk body means, the checksum and the block inside it, belongs
to `ReqResp/Payload.lean`. A framed *stream* has many spellings of one
payload (the writer picks compressed or uncompressed chunks, and may add
padding), so the stream layer has no `LawfulCodec`. The reader core
reads it, and the suite pins it with the go fixtures and one rejection
per rule.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.ReqResp.SnappyFrame

open Libp2p.Protocols
open Bytes

/-! ## Chunk kinds -/

/-- The chunk types of section 4. The two reserved ranges keep their
code, since a reader must tell an unskippable chunk from a skippable
one. -/
inductive Kind where
  /-- `0x00`: a snappy block, after the checksum of its output (4.2). -/
  | compressed
  /-- `0x01`: raw bytes, after their checksum (4.3). -/
  | uncompressed
  /-- `0x02` to `0x7f`: a reader must stop with an error (4.5). -/
  | unskippable (code : Nat) (h : 0x02 ≤ code ∧ code ≤ 0x7f)
  /-- `0x80` to `0xfd`: a reader skips the chunk (4.6). -/
  | skippable (code : Nat) (h : 0x80 ≤ code ∧ code ≤ 0xfd)
  /-- `0xfe`: padding, which a reader skips unread (4.4). -/
  | padding
  /-- `0xff`: the stream identifier, `sNaPpY` (4.1). -/
  | streamId
  deriving DecidableEq, Repr

/-- The type byte of a kind. -/
def Kind.toCode : Kind → Nat
  | .compressed => Constants.snappyCompressed
  | .uncompressed => Constants.snappyUncompressed
  | .unskippable c _ => c
  | .skippable c _ => c
  | .padding => Constants.snappyPadding
  | .streamId => Constants.snappyStreamId

/-- The kind of a type byte. `none` for a value that is no byte. -/
def Kind.ofCode? (c : Nat) : Option Kind :=
  if c = Constants.snappyCompressed then some .compressed
  else if c = Constants.snappyUncompressed then some .uncompressed
  else if h : 0x02 ≤ c ∧ c ≤ 0x7f then some (.unskippable c h)
  else if h : 0x80 ≤ c ∧ c ≤ 0xfd then some (.skippable c h)
  else if c = Constants.snappyPadding then some .padding
  else if c = Constants.snappyStreamId then some .streamId
  else none

/-- The table is a bijection on the byte values (§3.4). -/
theorem Kind.ofCode?_toCode (k : Kind) : Kind.ofCode? k.toCode = some k := by
  cases k with
  | unskippable c h =>
    simp only [toCode, ofCode?, Constants.snappyCompressed, Constants.snappyUncompressed]
    simp [show c ≠ 0 by omega, show c ≠ 1 by omega, h]
  | skippable c h =>
    simp only [toCode, ofCode?, Constants.snappyCompressed, Constants.snappyUncompressed]
    simp [show c ≠ 0 by omega, show c ≠ 1 by omega, show ¬(2 ≤ c ∧ c ≤ 127) by omega, h]
  | _ => decide

/-- Every code the table accepts is a byte. -/
theorem Kind.toCodeLt (k : Kind) : k.toCode < 256 := by
  cases k with
  | unskippable c h => simp only [toCode]; omega
  | skippable c h => simp only [toCode]; omega
  | _ => decide

/-- A decoded code reads back as the same code. -/
theorem Kind.toCodeOfCode? {c : Nat} {k : Kind} (h : Kind.ofCode? c = some k) :
    k.toCode = c := by
  unfold ofCode? at h
  split at h
  · cases h; simp_all [toCode]
  split at h
  · cases h; simp_all [toCode]
  split at h
  · cases h; rfl
  split at h
  · cases h; rfl
  split at h
  · cases h; simp_all [toCode]
  split at h
  · cases h; simp_all [toCode]
  · cases h

/-! ## One chunk -/

/-- One chunk of a framed stream. The body fits the 3-byte length, and
every entry is a byte, so each value has exactly one spelling. -/
structure Chunk where
  /-- The chunk type. -/
  kind : Kind
  /-- The chunk data after the header. -/
  body : List Nat
  /-- The body fits the length field, section 1. -/
  hlen : body.length ≤ Constants.snappyMaxChunkLen
  /-- Every entry is a byte. -/
  hbytes : ∀ b ∈ body, b < 256

instance : DecidableEq Chunk := fun a b =>
  if h : a.kind = b.kind ∧ a.body = b.body then
    .isTrue (by cases a; cases b; simp_all)
  else .isFalse (by intro e; cases e; simp_all)

/-- The bytes of one chunk: the type, the 3-byte length, the body. -/
def encode (c : Chunk) : List Nat :=
  c.kind.toCode :: Pb.leBytes c.body.length 3 ++ c.body

/-- Read one chunk and the bytes after it.

* Fewer than 4 header bytes, or fewer body bytes than the length says:
  `truncated`, since more bytes can complete the chunk.
* A header or body entry that is no byte: `malformed`. -/
def decode? (bs : List Nat) : Except DecodeError (Chunk × List Nat) :=
  match bs with
  | t :: l0 :: l1 :: l2 :: rest =>
    match Kind.ofCode? t with
    | none => .error .malformed
    | some k =>
      if l0 < 256 ∧ l1 < 256 ∧ l2 < 256 then
        let len := Pb.leOf [l0, l1, l2]
        if rest.length < len then .error .truncated
        else
          let body := rest.take len
          -- Three digits hold less than 2^24, so the first conjunct always
          -- holds; the check states it for the structure field.
          if hb : body.length ≤ Constants.snappyMaxChunkLen ∧ ∀ b ∈ body, b < 256 then
            .ok (⟨k, body, hb.1, hb.2⟩, rest.drop len)
          else .error .malformed
      else .error .malformed
  | _ => .error .truncated

instance : Codec Chunk where
  encode := encode
  decode? := decode?

/-- The 3-byte length of a chunk reads back as its body length. -/
theorem leOfLength (c : Chunk) :
    Pb.leOf (Pb.leBytes c.body.length 3) = c.body.length :=
  Pb.leOfLeBytes _ 3 (by have := c.hlen; simp only [Constants.snappyMaxChunkLen] at this; omega)

/-- A chunk decodes from its own bytes, whatever follows them. -/
theorem decodeEncodeAppend (c : Chunk) (rest : List Nat) :
    decode? (encode c ++ rest) = .ok (c, rest) := by
  obtain ⟨k, body, hlen, hbytes⟩ := c
  have hle : body.length < 256 ^ 3 := by
    simp only [Constants.snappyMaxChunkLen] at hlen; omega
  have hval := Pb.leBytesValid body.length 3
  have hlenEq := Pb.leOfLeBytes body.length 3 hle
  -- The three length digits, named so the match below can see them.
  obtain ⟨l0, l1, l2, hdig⟩ : ∃ l0 l1 l2, Pb.leBytes body.length 3 = [l0, l1, l2] :=
    ⟨_, _, _, rfl⟩
  rw [hdig] at hval hlenEq
  simp only [encode, hdig, decode?, List.cons_append, List.nil_append, Kind.ofCode?_toCode]
  have h0 := hval l0 (by simp)
  have h1 := hval l1 (by simp)
  have h2 := hval l2 (by simp)
  have hn : ¬(body.length + rest.length < body.length) := by omega
  simp only [h0, h1, h2, hlenEq, hlen, true_and, and_self, ↓reduceIte, List.length_append,
    List.take_left', List.drop_left', hn]
  rw [dite_eq_left_of_eq_true (eq_true hbytes)]

instance : LawfulCodec Chunk where
  decodeEncode c := by
    show decode? (encode c) = .ok (c, [])
    simpa using decodeEncodeAppend c []
  encodeDecode bs c rest h := by
    show encode c ++ rest = bs
    match bs, h with
    | t :: l0 :: l1 :: l2 :: tail, h =>
      simp only [Codec.decode?, decode?] at h
      split at h
      · cases h
      next k hk =>
        split at h
        next hl =>
          split at h
          · cases h
          next hlong =>
            split at h
            next hb =>
              cases h
              simp only [encode, Kind.toCodeOfCode? hk, List.cons_append]
              have hlenTake : (tail.take (Pb.leOf [l0, l1, l2])).length =
                  Pb.leOf [l0, l1, l2] := by
                simp only [List.length_take]; omega
              rw [hlenTake, Pb.leBytesLeOf [l0, l1, l2] 3 rfl (by
                intro b hb; simp at hb; omega)]
              simp [List.take_append_drop]
            · cases h
        · cases h

/-! ## The `ByteArray` header read -/

/-- The kind and the body length at `pos`, or `none` when fewer than 4
bytes remain. The response core reads the header before it decides
whether the body fits its byte budget, so it never buffers a body it
would refuse. -/
def decodeHeaderB? (b : ByteArray) (pos : Nat) : Option (Except DecodeError (Kind × Nat)) :=
  if b.size < pos + Constants.snappyHeaderLen then none
  else
    let byte (i : Nat) : Nat := (b.get! (pos + i)).toNat
    match Kind.ofCode? (byte 0) with
    | none => some (.error .malformed)
    | some k => some (.ok (k, byte 1 + 256 * (byte 2 + 256 * byte 3)))

/-- One whole chunk on the `ByteArray` path, and the bytes it took. It
reads the header with `decodeHeaderB?`, the read the response core runs,
so the suite's pin of this function to `decode?` covers that read too. -/
def decodeB? (b : ByteArray) : Except DecodeError (Chunk × Nat) :=
  match decodeHeaderB? b 0 with
  | none => .error .truncated
  | some (.error e) => .error e
  | some (.ok (k, len)) =>
    if b.size < Constants.snappyHeaderLen + len then .error .truncated
    else
      let body := (b.extract Constants.snappyHeaderLen (Constants.snappyHeaderLen + len)).toList.map
        (·.toNat)
      if h : body.length ≤ Constants.snappyMaxChunkLen ∧ ∀ x ∈ body, x < 256 then
        .ok (⟨k, body, h.1, h.2⟩, Constants.snappyHeaderLen + len)
      else .error .malformed

/-- The header bytes of one chunk with a body of `len` bytes, on the
`ByteArray` path of the writer. -/
def headerB (k : Kind) (len : Nat) : ByteArray :=
  ByteArray.mk #[k.toCode.toUInt8, len.toUInt8, (len / 256).toUInt8, (len / 65536).toUInt8]

end Libp2p.Protocols.ReqResp.SnappyFrame
