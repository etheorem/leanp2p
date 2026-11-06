import Yamux.Constants
import Yamux.Sets

/-!
# The frame header

Every yamux frame starts with a 12-byte header (spec, "Framing"):

| Bytes | Field | Width |
|---|---|---|
| 0 | version, always 0 | 8 bits |
| 1 | type (`FrameType`) | 8 bits |
| 2-3 | flags (`Flags`) | 16 bits |
| 4-7 | stream id | 32 bits |
| 8-11 | length | 32 bits |

"All fields are encoded in network order (big endian)." No field is a
varint, so the codec is plain byte arithmetic.

The meaning of the length depends on the type: the payload size of a
data frame, the window delta of a window update, the opaque value of a
ping, and the code of a go-away. The header knows none of this; the core
reads the length by the type.

## The three views

* **The model.** `Header` is the proof-carrying form of §3.7: the two
  32-bit fields carry their bound. `Codec Header` works over the byte
  model, and `LawfulCodec Header` proves the round trip (§6, layer 1).
* **The production path.** `encodeB` writes the 12 bytes, and
  `decodeAt?` reads them at an offset of a `ByteArray` without a copy.
  The generic harness of `base/bytes` pins both to the model (§6,
  layer 3).
* **The failures.** A prefix shorter than 12 bytes is `truncated`. A
  version other than 0 or an unknown type is `malformed`, as go-yamux
  and rust-yamux answer (the package ARCHITECTURE, "Checked against the
  implementations"). A flag bit outside the four passes through
  (`Yamux.Sets`, `Flags`).
-/

set_option autoImplicit false

namespace Yamux

open Bytes

/-! ## 32-bit fields -/

/-- A 32-bit field, big-endian. -/
def be32 (n : Nat) : List Nat :=
  [n / 16777216 % 256, n / 65536 % 256, n / 256 % 256, n % 256]

/-- The value of four big-endian bytes. -/
def ofBe32 (a b c d : Nat) : Nat :=
  a * 16777216 + b * 65536 + c * 256 + d

private theorem ofBe32Lt {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    ofBe32 a b c d < 2 ^ 32 := by
  simp only [ofBe32, Nat.reducePow]
  omega

private theorem be32OfBe32 {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    be32 (ofBe32 a b c d) = [a, b, c, d] := by
  simp only [be32, ofBe32, List.cons.injEq, and_true]
  omega

private theorem be32Bytes (n : Nat) : ∀ x ∈ be32 n, x < 256 := by
  simp only [be32, List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem ofBe32Be32 {n : Nat} (h : n < 2 ^ 32) :
    ofBe32 (n / 16777216 % 256) (n / 65536 % 256) (n / 256 % 256) (n % 256) = n := by
  simp only [ofBe32]
  simp only [Nat.reducePow] at h
  omega

/-! ## The model -/

/-- A frame header. The version is not a field: the spec defines one
version, and the codec writes and checks it. -/
structure Header where
  /-- What the frame carries. -/
  type : FrameType
  /-- The flags. -/
  flags : Flags
  /-- The stream the frame addresses; 0 is the session. -/
  streamId : Nat
  /-- The payload size, the window delta, the ping value, or the go-away
  code, by `type`. -/
  length : Nat
  /-- The stream id fits its 32 bits. -/
  streamIdLt : streamId < 2 ^ 32
  /-- The length fits its 32 bits. -/
  lengthLt : length < 2 ^ 32
  deriving DecidableEq, Repr

namespace Header

/-- Two headers with equal fields are one header: the other fields are
proofs. -/
theorem ext' {h g : Header} (ht : h.type = g.type) (hf : h.flags = g.flags)
    (hs : h.streamId = g.streamId) (hl : h.length = g.length) : h = g := by
  cases h; cases g; simp_all

/-- The header of these fields. The caller passes a stream id and a
length below `2 ^ 32`; the reduction modulo `2 ^ 32` only gives the
proof fields, and changes no value in range. -/
def make (type : FrameType) (flags : Flags) (streamId length : Nat) : Header :=
  ⟨type, flags, streamId % 2 ^ 32, length % 2 ^ 32, Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide)⟩

/-- The wire bytes of a header. -/
def encode (h : Header) : List Nat :=
  [version, h.type.toCode] ++ Codec.encode h.flags ++ be32 h.streamId ++ be32 h.length

/-- One header from the front of the input, and the rest. -/
def decode? : List Nat → Except DecodeError (Header × List Nat)
  | v :: t :: f1 :: f0 :: i3 :: i2 :: i1 :: i0 :: l3 :: l2 :: l1 :: l0 :: rest =>
    if hb : i3 < 256 ∧ i2 < 256 ∧ i1 < 256 ∧ i0 < 256 ∧
        l3 < 256 ∧ l2 < 256 ∧ l1 < 256 ∧ l0 < 256 then
      if v ≠ version then .error .malformed
      else
        match FrameType.ofCode? t, (Codec.decode? [f1, f0] : Except DecodeError (Flags × List Nat)) with
        | some ty, .ok (fl, []) =>
          .ok (⟨ty, fl, ofBe32 i3 i2 i1 i0, ofBe32 l3 l2 l1 l0,
            ofBe32Lt hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1,
            ofBe32Lt hb.2.2.2.2.1 hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2⟩, rest)
        | _, _ => .error .malformed
    else .error .malformed
  -- Fewer than 12 entries: more bytes may complete the header, unless a
  -- non-byte is already present.
  | short => if ∀ x ∈ short, x < 256 then .error .truncated else .error .malformed

/-- The encoding is 12 bytes, and every entry is a byte. -/
theorem encodeEq (h : Header) :
    encode h = [0, h.type.toCode, h.flags.toBits / 256, h.flags.toBits % 256] ++
      be32 h.streamId ++ be32 h.length := by
  rfl

/-- A header decodes back off its 12 bytes, and the bytes after it stay
for the payload: the round trip that the `LawfulCodec` instance takes. -/
theorem decode?EncodeAppend (h : Header) (rest : List Nat) :
    decode? (encode h ++ rest) = .ok (h, rest) := by
  have hs := be32Bytes h.streamId
  have hl := be32Bytes h.length
  have hflags : (Codec.decode? [h.flags.toBits / 256, h.flags.toBits % 256] :
      Except DecodeError (Flags × List Nat)) = .ok (h.flags, []) :=
    LawfulCodec.decodeEncode h.flags
  rw [encodeEq]
  simp only [be32, List.cons_append, List.nil_append] at hs hl ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs hl
  simp only [decode?, hs, hl, and_self, ↓reduceDIte, version, ne_eq, not_true_eq_false,
    ↓reduceIte, FrameType.ofCode?ToCode, hflags, Except.ok.injEq, Prod.mk.injEq, and_true]
  exact ext' rfl rfl (ofBe32Be32 h.streamIdLt) (ofBe32Be32 h.lengthLt)

instance : Codec Header where
  encode := encode
  decode? := decode?

instance : LawfulCodec Header where
  decodeEncode h := by
    show decode? (encode h) = _
    simpa using decode?EncodeAppend h []
  encodeDecode l h rest hd := by
    show encode h ++ rest = l
    simp only [Codec.decode?] at hd
    unfold decode? at hd
    split at hd
    · next v t f1 f0 i3 i2 i1 i0 l3 l2 l1 l0 r =>
      split at hd
      · next hb =>
        split at hd
        · cases hd
        · next hv =>
          split at hd
          · next ty fl hty hfl =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hd
            obtain ⟨rfl, rfl⟩ := hd
            have hv' : v = 0 := by simpa [version] using hv
            have ht := FrameType.toCodeOfCode? hty
            have hf : Codec.encode fl ++ [] = [f1, f0] := LawfulCodec.encodeDecode _ _ _ hfl
            simp only [List.append_nil] at hf
            obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb
            simp only [encode, version, ht, hf, be32OfBe32 h1 h2 h3 h4, be32OfBe32 h5 h6 h7 h8,
              hv', List.cons_append, List.nil_append]
          · cases hd
      · cases hd
    · split at hd <;> cases hd

example : decode? [0, 0, 0, 0] = .error .truncated := rfl
example : decode? [1, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 3] = .error .malformed := rfl

end Header

/-! ## The production path -/

namespace Header

/-- The 12 wire bytes of a header, as `encode` gives them. -/
def encodeB (h : Header) : ByteArray :=
  let u (n : Nat) : UInt8 := UInt8.ofNat n
  ⟨#[u version, u h.type.toCode, u (h.flags.toBits / 256), u h.flags.toBits,
    u (h.streamId / 16777216), u (h.streamId / 65536), u (h.streamId / 256), u h.streamId,
    u (h.length / 16777216), u (h.length / 65536), u (h.length / 256), u h.length]⟩

/-- The header at offset `pos` of `b`. The bytes are read in place, with
no copy. -/
def decodeAt? (b : ByteArray) (pos : Nat) : Except DecodeError Header :=
  if hsz : pos + headerSize ≤ b.size then
    -- `byte i` reads the field byte `i`; the size check above proves the
    -- index in range.
    let byte (i : Nat) (hi : i < headerSize) : Nat :=
      (b[pos + i]'(by simp only [headerSize] at hsz hi; omega)).toNat
    let lt (i : Nat) (hi : i < headerSize) : byte i hi < 256 := UInt8.toNat_lt _
    if byte 0 (by decide) ≠ version then .error .malformed
    else
      match FrameType.ofCode? (byte 1 (by decide)),
          Flags.ofBits? (byte 2 (by decide) * 256 + byte 3 (by decide)) with
      | some ty, some fl =>
        .ok ⟨ty, fl,
          ofBe32 (byte 4 (by decide)) (byte 5 (by decide)) (byte 6 (by decide)) (byte 7 (by decide)),
          ofBe32 (byte 8 (by decide)) (byte 9 (by decide)) (byte 10 (by decide)) (byte 11 (by decide)),
          ofBe32Lt (lt 4 _) (lt 5 _) (lt 6 _) (lt 7 _), ofBe32Lt (lt 8 _) (lt 9 _) (lt 10 _) (lt 11 _)⟩
      | _, _ => .error .malformed
  else .error .truncated

/-- One header from the front of `b`, and the bytes after it. The
harness pins it to `decode?`. -/
def decodeB? (b : ByteArray) : Except DecodeError (Header × ByteArray) := do
  let h ← decodeAt? b 0
  return (h, b.extract headerSize b.size)

end Header

end Yamux
