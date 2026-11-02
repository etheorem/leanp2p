import Yamux.Mock.Bytes
import Yamux.Constants
import Yamux.Sets

/-!
# Yamux frame header

The 12-byte header of the hashicorp yamux specification, as a
`Yamux.Mock.Bytes.Codec` with a proved round trip (ARCHITECTURE §3.2, §4.8).

The layout is fixed and big-endian:

```
version (8) | type (8) | flags (16) | stream id (32) | length (32)
```

No field is a varint, so the codec is plain byte arithmetic over the
`List Nat` model, and `omega` closes the proofs. The decoder accepts
only the version this implementation speaks and only bytes below 256,
so an input that decodes is spelled the way the encoder spells it. That
spelling rule is what makes the second law, `encodeDecode`, true.
-/

set_option autoImplicit false


namespace Yamux

/-! ## 32-bit words -/

/-- A 32-bit unsigned word, the width of the stream id and length
fields. The type carries the bound, so no consumer checks it again
(ARCHITECTURE §3.7). -/
structure Word32 where
  /-- The value of the word. -/
  val : Nat
  /-- The proof that the value fits the field. -/
  isLt : val < 4294967296
  deriving Repr, DecidableEq, BEq, Hashable

namespace Word32

/-- The zero word. -/
def zero : Word32 := ⟨0, by decide⟩

/-- A word from any number: the low 32 bits. A wire value is always a
word, so a frame builder never needs a side condition. -/
def ofNat (n : Nat) : Word32 := ⟨n % 4294967296, Nat.mod_lt _ (by decide)⟩

/-- Two words are equal when their values are. The proof field is
irrelevant, and the kernel knows it (ARCHITECTURE §3.7). -/
@[ext]
theorem ext {a b : Word32} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  simp_all

end Word32

/-- A stream identifier. Stream 0 is the session, a client opens odd ids,
and a server opens even ones. The parity is a property of the value and
of the role, so it stays with the core that assigns ids, not in the
type. -/
abbrev StreamId := Word32

/-! ## Big-endian byte decomposition -/

/-- The four big-endian bytes of a 32-bit value, high byte first. Each
byte is below 256 by construction, so the encoder needs no side
condition. -/
def be4 (n : Nat) : List Nat :=
  [n / 16777216 % 256, n / 65536 % 256, n / 256 % 256, n % 256]

/-- Four big-endian bytes read as a 32-bit value, in Horner form so the
division lemmas apply one step at a time. -/
def ofBe4 (a b c d : Nat) : Nat :=
  d + 256 * (c + 256 * (b + 256 * a))

/-- Every byte of a `be4` decomposition is below 256. -/
theorem be4_lt (n : Nat) : ∀ b ∈ be4 n, b < 256 := by
  intro b hb
  simp [be4] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact Nat.mod_lt _ (by decide)

/-- The four bytes of a 32-bit value read back as that value. -/
theorem ofBe4_be4 {n : Nat} (h : n < 4294967296) :
    ofBe4 (n / 16777216 % 256) (n / 65536 % 256) (n / 256 % 256) (n % 256) = n := by
  have h1 := Nat.div_add_mod n 256
  have h2 := Nat.div_add_mod (n / 256) 256
  have h3 := Nat.div_add_mod (n / 65536) 256
  have e1 : n / 256 / 256 = n / 65536 := by rw [Nat.div_div_eq_div_mul]
  have e2 : n / 65536 / 256 = n / 16777216 := by rw [Nat.div_div_eq_div_mul]
  rw [e1] at h2
  rw [e2] at h3
  unfold ofBe4
  omega

/-- The value as its top byte and the three bytes below it. -/
theorem ofBe4_split (a b c d : Nat) :
    ofBe4 a b c d = (d + 256 * (c + 256 * b)) + 16777216 * a := by
  unfold ofBe4
  omega

/-- The low three bytes as one number. -/
theorem ofBe4_split2 (a b c d : Nat) :
    ofBe4 a b c d = (d + 256 * c) + 65536 * (b + 256 * a) := by
  unfold ofBe4
  omega

/-- The top byte of a value read back from four bytes. -/
theorem ofBe4_div_top {a b c d : Nat} (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    ofBe4 a b c d / 16777216 % 256 = a % 256 := by
  have hR : d + 256 * (c + 256 * b) < 16777216 := by omega
  rw [ofBe4_split,
    Nat.add_mul_div_left _ _ (by decide : 0 < 16777216),
    Nat.div_eq_of_lt hR, Nat.zero_add]

/-- The second byte of a value read back from four bytes. -/
theorem ofBe4_div_third {a b c d : Nat} (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    ofBe4 a b c d / 65536 % 256 = b := by
  have hR : d + 256 * c < 65536 := by omega
  rw [ofBe4_split2,
    Nat.add_mul_div_left _ _ (by decide : 0 < 65536),
    Nat.div_eq_of_lt hR, Nat.zero_add]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

/-- The third byte of a value read back from four bytes. -/
theorem ofBe4_div_second {a b c d : Nat} (hc : c < 256) (hd : d < 256) :
    ofBe4 a b c d / 256 % 256 = c := by
  have h : ofBe4 a b c d / 256 = c + 256 * (b + 256 * a) := by
    unfold ofBe4
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 256), Nat.div_eq_of_lt hd,
      Nat.zero_add]
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

/-- The low byte of a value read back from four bytes. -/
theorem ofBe4_mod_low {a b c d : Nat} (hd : d < 256) : ofBe4 a b c d % 256 = d := by
  unfold ofBe4
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

/-- Reading four bytes back and splitting them returns the bytes. This
is the direction that makes `encodeDecode` true: a decoder that accepts
an input must spell it the way the encoder does. -/
theorem be4_ofBe4 {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (hd : d < 256) : be4 (ofBe4 a b c d) = [a, b, c, d] := by
  have h1 := ofBe4_div_top (a := a) hb hc hd
  have h2 := ofBe4_div_third (a := a) hb hc hd
  have h3 := ofBe4_div_second (a := a) (b := b) hc hd
  have h4 := ofBe4_mod_low (a := a) (b := b) (c := c) hd
  rw [Nat.mod_eq_of_lt ha] at h1
  unfold be4
  rw [h1, h2, h3, h4]

/-! ## The header -/

/-- A yamux frame header. The version is not a field: the codec accepts
one version, and a field that can hold only one value would be a trap
for the reader. -/
structure Header where
  /-- The frame type. -/
  frameType : FrameType
  /-- The flag bits. -/
  flags : Flags
  /-- The stream the frame belongs to. Stream 0 carries session frames. -/
  streamId : StreamId
  /-- The payload length, the credit delta, the ping value, or the
  `GoAway` code, according to the type. -/
  length : Word32
  deriving Repr, DecidableEq, BEq, Hashable

namespace Header

/-- A header from its parts. The codec is the only place that writes the
layout, so the constructor stays trivial. -/
def ofParts (t : FrameType) (fl : Flags) (sid : StreamId) (len : Word32) : Header :=
  { frameType := t, flags := fl, streamId := sid, length := len }

/-- The bytes of a header: version, type, the two flag bytes, then the
stream id and the length, both big-endian. -/
def encode (h : Header) : List Nat :=
  [wireVersion, h.frameType.toCode] ++ h.flags.encode ++ be4 h.streamId.val ++
    be4 h.length.val

/-- The header laid out as its twelve bytes. The layout is written down
once, here; `encode` composes the same bytes from the field codecs, and
this theorem is the bridge the proofs use. -/
theorem encode_eq (h : Header) :
    encode h =
      [wireVersion, h.frameType.toCode,
       Flags.toCode h.flags / 256 % 256, Flags.toCode h.flags % 256,
       h.streamId.val / 16777216 % 256, h.streamId.val / 65536 % 256,
       h.streamId.val / 256 % 256, h.streamId.val % 256,
       h.length.val / 16777216 % 256, h.length.val / 65536 % 256,
       h.length.val / 256 % 256, h.length.val % 256] := by
  simp [encode, Flags.encode, be4]

/-- The header carried by twelve accepted bytes, if the bytes name one.
The version must be the one this implementation speaks, and every byte
must be below 256, because the model is wider than the wire. -/
def decode? : List Nat → Except Yamux.Mock.Bytes.DecodeError (Header × List Nat)
  | v :: t :: f0 :: f1 :: s0 :: s1 :: s2 :: s3 :: l0 :: l1 :: l2 :: l3 :: rest =>
      if hb : ∀ b ∈ [v, t, f0, f1, s0, s1, s2, s3, l0, l1, l2, l3], b < 256 then
        if hv : v = wireVersion then
          match FrameType.ofCode? t with
          | some ft =>
              match Flags.decode? [f0, f1] with
              | .ok (fl, []) =>
                  have hs0 : s0 < 256 := hb s0 (by simp)
                  have hs1 : s1 < 256 := hb s1 (by simp)
                  have hs2 : s2 < 256 := hb s2 (by simp)
                  have hs3 : s3 < 256 := hb s3 (by simp)
                  have hl0 : l0 < 256 := hb l0 (by simp)
                  have hl1 : l1 < 256 := hb l1 (by simp)
                  have hl2 : l2 < 256 := hb l2 (by simp)
                  have hl3 : l3 < 256 := hb l3 (by simp)
                  let sid : StreamId := ⟨ofBe4 s0 s1 s2 s3, by unfold ofBe4; omega⟩
                  let len : Word32 := ⟨ofBe4 l0 l1 l2 l3, by unfold ofBe4; omega⟩
                  .ok ({ frameType := ft, flags := fl, streamId := sid, length := len },
                    rest)
              | _ => .error .malformed
          | none => .error .malformed
        else .error .malformed
      else .error .malformed
  | _ => .error .truncated

/-! ## The codec laws -/

/-- A list of wire bytes: every element is below 256. The model is wider
than the wire, so a decoder narrows, and an encoder proves the
narrowing (ARCHITECTURE §5.2). -/
def AllBytes (l : List Nat) : Prop := ∀ b ∈ l, b < 256

namespace AllBytes

/-- The empty list is a byte list. -/
theorem nil : AllBytes [] := by
  intro b hb
  cases hb

/-- A byte in front of a byte list keeps it a byte list. -/
theorem cons {x : Nat} {l : List Nat} (hx : x < 256) (hl : AllBytes l) : AllBytes (x :: l) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hx
  · exact hl b hb

/-- Two byte lists appended are a byte list. -/
theorem append {l1 l2 : List Nat} (h1 : AllBytes l1) (h2 : AllBytes l2) :
    AllBytes (l1 ++ l2) := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact h1 b hb
  · exact h2 b hb

end AllBytes

/-- Every byte of an encoded header is below 256. -/
theorem encode_lt (h : Header) : AllBytes (encode h) := by
  rw [encode_eq]
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · exact Nat.lt_of_lt_of_le (FrameType.toCode_lt_four h.frameType) (by decide)
  all_goals exact Nat.mod_lt _ (by decide)

/-- Decoding an encoded header returns it, consumes exactly its twelve
bytes, and leaves the bytes after it untouched. The suffix is what a
streaming reader needs: the next frame starts where this one ends. -/
theorem decode?_encode_append (h : Header) (rest : List Nat) :
    decode? (encode h ++ rest) = .ok (h, rest) := by
  have hmem : AllBytes
      [wireVersion, h.frameType.toCode,
       Flags.toCode h.flags / 256 % 256, Flags.toCode h.flags % 256,
       h.streamId.val / 16777216 % 256, h.streamId.val / 65536 % 256,
       h.streamId.val / 256 % 256, h.streamId.val % 256,
       h.length.val / 16777216 % 256, h.length.val / 65536 % 256,
       h.length.val / 256 % 256, h.length.val % 256] := by
    rw [← encode_eq]
    exact encode_lt h
  have hmem' : ∀ b ∈
      [wireVersion, h.frameType.toCode,
       Flags.toCode h.flags / 256 % 256, Flags.toCode h.flags % 256,
       h.streamId.val / 16777216 % 256, h.streamId.val / 65536 % 256,
       h.streamId.val / 256 % 256, h.streamId.val % 256,
       h.length.val / 16777216 % 256, h.length.val / 65536 % 256,
       h.length.val / 256 % 256, h.length.val % 256], b < 256 := hmem
  have hft : FrameType.ofCode? h.frameType.toCode = some h.frameType :=
    FrameType.ofCode?_toCode _
  have hfl : Flags.decode? (Flags.encode h.flags) = .ok (h.flags, []) :=
    Flags.decode?_encode h.flags
  have hs : (⟨ofBe4 (h.streamId.val / 16777216 % 256) (h.streamId.val / 65536 % 256)
      (h.streamId.val / 256 % 256) (h.streamId.val % 256),
      by unfold ofBe4; omega⟩ : Word32) = h.streamId := by
    apply Word32.ext
    exact ofBe4_be4 h.streamId.isLt
  have hl : (⟨ofBe4 (h.length.val / 16777216 % 256) (h.length.val / 65536 % 256)
      (h.length.val / 256 % 256) (h.length.val % 256),
      by unfold ofBe4; omega⟩ : Word32) = h.length := by
    apply Word32.ext
    exact ofBe4_be4 h.length.isLt
  rw [encode_eq]
  simp only [List.cons_append, List.nil_append, decode?]
  rw [dite_eq_left hmem']
  rw [dite_eq_left trivial]
  simp only [hft, Flags.encode] at hfl ⊢
  rw [hfl]
  rw [hs, hl]

/-- The first codec law: decoding an encoded header returns it and eats
every byte (ARCHITECTURE §6). -/
theorem decode?_encode (h : Header) : decode? (encode h) = .ok (h, []) := by
  have := decode?_encode_append h []
  simpa using this

/-- Every accepted input re-encodes to itself: the decoder accepts only
the canonical spelling, so the encoder reproduces the input byte for
byte (the second law of `LawfulCodec`, ARCHITECTURE §6). -/
theorem encode_decode? : ∀ {bs : List Nat} {h : Header} {rest : List Nat},
    decode? bs = .ok (h, rest) → encode h ++ rest = bs
  | v :: t :: f0 :: f1 :: s0 :: s1 :: s2 :: s3 :: l0 :: l1 :: l2 :: l3 :: rs, h, rest, hh => by
      simp only [decode?] at hh
      split at hh
      · rename_i hb
        split at hh
        · rename_i hv
          split at hh
          · rename_i ft hft
            split at hh
            · rename_i fl hfl
              simp only [Except.ok.injEq, Prod.mk.injEq] at hh
              obtain ⟨hrec, hrest⟩ := hh
              subst hrec
              subst hrest
              have ht : t = FrameType.toCode ft := FrameType.eq_toCode_of_ofCode?_eq_some hft
              have hfe : [Flags.toCode fl / 256 % 256, Flags.toCode fl % 256] = [f0, f1] :=
                Yamux.Mock.Bytes.LawfulCodec.encodeDecode (α := Flags) [f0, f1] fl [] hfl
              have hf0 : Flags.toCode fl / 256 % 256 = f0 := by
                cases hfe
                rfl
              have hf1 : Flags.toCode fl % 256 = f1 := by
                cases hfe
                rfl
              have hs : be4 (ofBe4 s0 s1 s2 s3) = [s0, s1, s2, s3] :=
                be4_ofBe4 (hb s0 (by simp)) (hb s1 (by simp)) (hb s2 (by simp))
                  (hb s3 (by simp))
              have hl : be4 (ofBe4 l0 l1 l2 l3) = [l0, l1, l2, l3] :=
                be4_ofBe4 (hb l0 (by simp)) (hb l1 (by simp)) (hb l2 (by simp))
                  (hb l3 (by simp))
              change ([wireVersion, FrameType.toCode ft] ++
                [Flags.toCode fl / 256 % 256, Flags.toCode fl % 256] ++
                be4 (ofBe4 s0 s1 s2 s3) ++ be4 (ofBe4 l0 l1 l2 l3)) ++ rs =
                v :: t :: f0 :: f1 :: s0 :: s1 :: s2 :: s3 :: l0 :: l1 :: l2 :: l3 :: rs
              rw [hf0, hf1, hs, hl, hv, ht]
              simp
            · simp at hh
          · simp at hh
        · simp at hh
      · simp at hh
  | [], _, _, hh => by simp [decode?] at hh
  | [_], _, _, hh => by simp [decode?] at hh
  | [_, _], _, _, hh => by simp [decode?] at hh
  | [_, _, _], _, _, hh => by simp [decode?] at hh
  | [_, _, _, _], _, _, hh => by simp [decode?] at hh
  | [_, _, _, _, _], _, _, hh => by simp [decode?] at hh
  | [_, _, _, _, _, _], _, _, hh => by simp [decode?] at hh
  | [_, _, _, _, _, _, _], _, _, hh => by simp [decode?] at hh
  | [_, _, _, _, _, _, _, _], _, _, hh => by simp [decode?] at hh
  | [_, _, _, _, _, _, _, _, _], _, _, hh => by simp [decode?] at hh
  | [_, _, _, _, _, _, _, _, _, _], _, _, hh => by simp [decode?] at hh
  | [_, _, _, _, _, _, _, _, _, _, _], _, _, hh => by simp [decode?] at hh

/-- The header is a wire codec (ARCHITECTURE §3.2). -/
instance : Yamux.Mock.Bytes.Codec Header where
  encode := encode
  decode? := decode?

/-- The header codec is lawful: both round-trip laws hold
(ARCHITECTURE §6, layer 1). -/
instance : Yamux.Mock.Bytes.LawfulCodec Header where
  decodeEncode := decode?_encode
  encodeDecode := fun _ _ _ h => encode_decode? h

end Header

end Yamux