import Streams.BufReader
import Bytes
import Varint

/-!
# `Framing`: length-prefixed frames

A length-prefixed frame is a length, then that many payload bytes. The
stack uses two prefix shapes:

* `uvarint`: the unsigned varint of `codec/varint`. The
  multistream-select messages, the req/resp chunks, and the mplex
  bodies use it.
* `u16be`: two bytes, big-endian. The Noise transport frames use it, so
  a Noise frame holds at most 65535 bytes.

This module knows the shape alone. Each protocol layer passes the cap of
its frames from its own constants module (ARCHITECTURE §5.1), and owns
the message inside the payload.

## The three views

* **The model.** `Frame p cap` is the proof-carrying newtype of §3.7: a
  payload of bytes under the cap. Its `Codec` instance works over the
  byte model, and its `LawfulCodec` instance proves the round trip
  (§6, layer 1).
* **The production path.** `headerB?` reads a header out of a
  `ByteArray`, and `encodeB?` writes a frame. The generic harness of
  `base/bytes` pins them to the model (§6, layer 3).
* **The IO path.** `read` takes a frame through a `BufReader`. The cap
  applies to the header, before the payload read allocates (§5.1).
  `headerB?LeCap` proves that a header that passes holds a length
  inside the cap.

## Failures

The model and the production path report through the `DecodeError` of
`base/bytes`. A short input is `truncated`. A length over the cap is
`malformed`, and so is a varint that runs past its budget (§4.3).

The IO path never gives `truncated`, since it reads more bytes instead.
A connection that ends inside a frame ends the read as `none`, the
end-of-stream channel of §3.5. A frame over the cap is `malformed`
before the read takes a payload byte.

`DecodeError`, `Codec`, `LawfulCodec`, and the byte model come from
`base/bytes`, and the varint comes from `codec/varint`. The proofs use
two theorems of the varint, `decodeEncodeSuffix` and `encodeDecode`,
and nothing from the byte model.
-/

set_option autoImplicit false

namespace Streams.Framing

open Conc Bytes

/-! ## Taking a payload -/

/-- The first `k` bytes of the input, and the rest. A non-byte among the
bytes present is `malformed`, since no suffix can repair it. Fewer than
`k` bytes is `truncated`, since more input can complete the payload. -/
def take? (k : Nat) (l : List Nat) : Except DecodeError (List Nat × List Nat) :=
  if ¬∀ x ∈ l.take k, x < 256 then .error .malformed
  else if l.length < k then .error .truncated
  else .ok (l.take k, l.drop k)

/-- A take of the bytes in front of any rest returns them whole. -/
theorem take?Append {b : List Nat} (rest : List Nat) (h : ∀ x ∈ b, x < 256) :
    take? b.length (b ++ rest) = .ok (b, rest) := by
  have htake : (b ++ rest).take b.length = b := by simp
  unfold take?
  rw [htake]
  split
  · next hn => exact absurd h hn
  · split
    · next hl => simp at hl; omega
    · simp

/-- A successful take split the input at `k`, and the part it took holds
bytes. -/
theorem ofTake? {k : Nat} {l b rest : List Nat} (h : take? k l = .ok (b, rest)) :
    b ++ rest = l ∧ b.length = k ∧ ∀ x ∈ b, x < 256 := by
  unfold take? at h
  split at h
  · cases h
  · next hbytes =>
    split at h
    · cases h
    · next hlen =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨List.take_append_drop k l, ?_, by simpa using hbytes⟩
      simp only [List.length_take]
      omega

/-- A take from an input shorter than `k` that holds bytes is
`truncated`. -/
theorem take?Short {k : Nat} {l : List Nat} (hb : ∀ x ∈ l, x < 256) (hl : l.length < k) :
    take? k l = .error .truncated := by
  have hall : ∀ x ∈ l.take k, x < 256 := fun x hx => hb x (List.mem_of_mem_take hx)
  unfold take?
  rw [ite_eq_right (fun hn => hn hall), ite_eq_left hl]

example : take? 2 [1, 2, 3] = .ok ([1, 2], [3]) := rfl
example : take? 4 [1, 2, 3] = .error .truncated := rfl
example : take? 2 [1, 300, 3] = .error .malformed := rfl

/-! ## The prefix shapes -/

/-- The shape of a length prefix. -/
inductive Prefix where
  /-- An unsigned varint (`codec/varint`). -/
  | uvarint
  /-- Two bytes, big-endian. -/
  | u16be
  deriving DecidableEq, Repr, Hashable

/-- The largest length that the prefix can carry: the 63-bit varint
budget of §4.3, or 2 ^ 16 - 1 for two bytes. -/
def Prefix.maxLen : Prefix → Nat
  | .uvarint => 2 ^ (7 * Varint.maxBytes) - 1
  | .u16be => 65535

/-- The prefix bytes of a length, over the byte model. -/
def encodeLength : Prefix → Nat → List Nat
  | .uvarint, n => Varint.encodeNat n
  | .u16be, n => [n / 256, n % 256]

/-- A length from the front of the input, and the rest. A non-byte in
the prefix is `malformed`, and an input that ends inside the prefix is
`truncated`. -/
def decodeLength? : Prefix → List Nat → Except DecodeError (Nat × List Nat)
  | .uvarint, l => (Varint.decode? l).map fun (v, rest) => (v.val, rest)
  | .u16be, [] => .error .truncated
  | .u16be, [a] => if a < 256 then .error .truncated else .error .malformed
  | .u16be, a :: b :: rest =>
    if a < 256 ∧ b < 256 then .ok (a * 256 + b, rest) else .error .malformed

/-- A length that the prefix can carry decodes from its prefix, with any
rest after it. -/
theorem decodeLength?EncodeLength (p : Prefix) (n : Nat) (rest : List Nat)
    (h : n ≤ p.maxLen) : decodeLength? p (encodeLength p n ++ rest) = .ok (n, rest) := by
  cases p with
  | uvarint =>
    -- The varint carries `n` as a `UVarint`, and the budget proof comes
    -- from `maxLen`. `omega` treats the power as an opaque number.
    have hpos := Nat.two_pow_pos (7 * Varint.maxBytes)
    have hlt : n < 2 ^ (7 * Varint.maxBytes) := by simp only [Prefix.maxLen] at h; omega
    have hv := Varint.decodeEncodeSuffix ⟨n, hlt⟩ rest
    simp only [decodeLength?, encodeLength]
    -- `Varint.encode ⟨n, _⟩` unfolds to `encodeNat n` by definition.
    rw [show Varint.encodeNat n = Varint.encode ⟨n, hlt⟩ from rfl, hv]
    rfl
  | u16be =>
    simp only [Prefix.maxLen] at h
    simp only [encodeLength, List.cons_append, List.nil_append, decodeLength?]
    rw [ite_eq_left (by omega)]
    congr 2
    omega

/-- A decoded length re-encodes to the bytes that it came from, and the
prefix can carry it. -/
theorem encodeLengthOfDecodeLength? {p : Prefix} {l rest : List Nat} {n : Nat}
    (h : decodeLength? p l = .ok (n, rest)) :
    encodeLength p n ++ rest = l ∧ n ≤ p.maxLen := by
  cases p with
  | uvarint =>
    simp only [decodeLength?] at h
    cases hv : Varint.decode? l with
    | error e => simp [hv, Except.map] at h
    | ok vr =>
      obtain ⟨v, r⟩ := vr
      simp only [hv, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      -- The varint law gives the bytes back.
      have hl := LawfulCodec.encodeDecode l v r hv
      have hpos := Nat.two_pow_pos (7 * Varint.maxBytes)
      -- `limit` unfolds to the power by definition, so the annotation
      -- hands `omega` the bound in the form `maxLen` uses.
      have hlt : v.val < 2 ^ (7 * Varint.maxBytes) := v.isLt
      exact ⟨hl, by simp only [Prefix.maxLen]; omega⟩
  | u16be =>
    match l, h with
    | [], h => simp [decodeLength?] at h
    | [a], h =>
      simp only [decodeLength?] at h
      split at h <;> cases h
    | a :: b :: r, h =>
      simp only [decodeLength?] at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [encodeLength, Prefix.maxLen, List.cons_append, List.nil_append,
          List.cons.injEq, and_true]
        omega
      · cases h

/-- A `u16be` prefix with one byte of two is `truncated`: the second byte
can still arrive. -/
theorem decodeLength?U16beShort {a : Nat} (h : a < 256) :
    decodeLength? .u16be [a] = .error .truncated := by
  simp [decodeLength?, h]

/-- Every prefix byte of a `u16be` length inside the prefix is a byte. -/
theorem ltOfMemEncodeLengthU16be {n x : Nat} (h : n ≤ Prefix.maxLen .u16be)
    (hx : x ∈ encodeLength .u16be n) : x < 256 := by
  simp only [Prefix.maxLen] at h
  simp only [encodeLength, List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

/-! ## The model -/

/-- A frame of prefix `p` whose payload fits `cap`. The payload holds
bytes, and its length fits the cap and the prefix. The decoder checks
both where the bytes enter, and Lean erases the proofs at run time
(§3.7). -/
structure Frame (p : Prefix) (cap : Nat) where
  /-- The payload bytes. -/
  payload : List Nat
  /-- Every payload entry is a byte. -/
  bytes : ∀ x ∈ payload, x < 256
  /-- The payload fits the cap and the prefix. -/
  fits : payload.length ≤ cap ∧ payload.length ≤ p.maxLen
  deriving DecidableEq, Repr

namespace Frame

variable {p : Prefix} {cap : Nat}

/-- Two frames with one payload are one frame, since the other fields
are proofs. -/
theorem ext' {f g : Frame p cap} (h : f.payload = g.payload) : f = g := by
  cases f; cases g; cases h; rfl

/-- The frame of a payload, when the payload holds bytes and fits.
`none` when it does not. -/
def ofList? (p : Prefix) (cap : Nat) (l : List Nat) : Option (Frame p cap) :=
  if h : (∀ x ∈ l, x < 256) ∧ l.length ≤ cap ∧ l.length ≤ p.maxLen then
    some ⟨l, h.1, h.2⟩
  else none

/-- `ofList?` accepts the payload of every frame, and gives the frame
back. -/
theorem ofList?Payload (f : Frame p cap) : ofList? p cap f.payload = some f := by
  unfold ofList?
  -- The proof fields of the frame satisfy the check, and structure eta
  -- with proof irrelevance closes `⟨f.payload, _, _⟩ = f`.
  rw [dite_eq_left ⟨f.bytes, f.fits⟩]

/-- `ofList?` refuses a payload longer than the cap. -/
theorem ofList?OverCap {l : List Nat} (h : cap < l.length) : ofList? p cap l = none := by
  simp only [ofList?]
  split
  · next hfit => omega
  · rfl

/-- The wire bytes of a frame: the length prefix, then the payload. -/
def encode (f : Frame p cap) : List Nat :=
  encodeLength p f.payload.length ++ f.payload

/-- One frame from the front of the input, and the rest. The cap check
comes after the prefix and before the payload take, so a length over
the cap is `malformed` for any count of payload bytes after it
(§5.1). -/
def decode? (p : Prefix) (cap : Nat) (l : List Nat) :
    Except DecodeError (Frame p cap × List Nat) :=
  match decodeLength? p l with
  | .error e => .error e
  | .ok (len, rest) =>
    if hfit : len ≤ cap ∧ len ≤ p.maxLen then
      -- `ht` names the take, so `ofTake?` can turn it into the proof
      -- fields of the frame.
      match ht : take? len rest with
      | .error e => .error e
      | .ok (payload, after) =>
        have hp := ofTake? ht
        .ok (⟨payload, hp.2.2, by rw [hp.2.1]; exact hfit⟩, after)
    else .error .malformed

/-- The decode of an encoding, with any rest after it. -/
theorem decode?EncodeAppend (f : Frame p cap) (rest : List Nat) :
    decode? p cap (encode f ++ rest) = .ok (f, rest) := by
  unfold decode? encode
  rw [List.append_assoc, decodeLength?EncodeLength p _ _ f.fits.2]
  simp only [dite_eq_left f.fits]
  split
  · next e ht => rw [take?Append rest f.bytes] at ht; cases ht
  · next payload after ht =>
    rw [take?Append rest f.bytes] at ht
    simp only [Except.ok.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    rfl

/-- A prefix with a length over the cap is `malformed`, whatever
follows it. This is the cap rule of §5.1 on the model: the decode stops
before the payload. -/
theorem decode?OverCap {l rest : List Nat} {len : Nat}
    (hd : decodeLength? p l = .ok (len, rest)) (hcap : cap < len) :
    decode? p cap l = .error .malformed := by
  unfold decode?
  rw [hd]
  simp only
  split
  · next hfit => omega
  · rfl

/-- A prefix that fits the cap, with fewer payload bytes after it than it
names, is `truncated`: more input can complete the frame. -/
theorem decode?ShortPayload {l rest : List Nat} {len : Nat}
    (hd : decodeLength? p l = .ok (len, rest)) (hcap : len ≤ cap) (hmax : len ≤ p.maxLen)
    (hb : ∀ x ∈ rest, x < 256) (hshort : rest.length < len) :
    decode? p cap l = .error .truncated := by
  unfold decode?
  rw [hd]
  -- `simp only` reduces the outer `match` on the decoded length; the
  -- `dite` on the cap and the `match` on the take stay for `split`.
  simp only
  split
  · split
    · next e ht => rw [take?Short hb hshort] at ht; cases ht; rfl
    · next payload after ht => rw [take?Short hb hshort] at ht; cases ht
  · next hfit => exact absurd ⟨hcap, hmax⟩ hfit

instance : Codec (Frame p cap) where
  encode := encode
  decode? := decode? p cap

instance : LawfulCodec (Frame p cap) where
  decodeEncode f := by
    -- `Codec.encode` and `Codec.decode?` unfold to the functions above.
    show decode? p cap (encode f) = _
    simpa using decode?EncodeAppend f []
  encodeDecode l f rest h := by
    show encode f ++ rest = l
    simp only [Codec.decode?, decode?] at h
    split at h
    · cases h
    · next len r1 hd =>
      split at h
      · split at h
        · cases h
        · next payload after ht =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hsplit, hlen, -⟩ := ofTake? ht
          obtain ⟨hl, -⟩ := encodeLengthOfDecodeLength? hd
          simp only [encode, List.append_assoc, hsplit, hlen, hl]
      · cases h

example : decode? .u16be 4 [0, 2, 7, 8, 9] = .ok (⟨[7, 8], by decide, by decide⟩, [9]) := rfl
example : decode? .u16be 4 [0, 5, 1, 2, 3, 4, 5] = .error .malformed := rfl
example : decode? .u16be 4 [0] = .error .truncated := rfl

example : decode? .uvarint 4 [3, 1, 2] = .error .truncated := rfl
example : decode? .uvarint 4 [5, 1, 2, 3, 4, 5] = .error .malformed := rfl

end Frame

/-! ## The production path -/

/-- The length at the front of `b`, and the size of its prefix. -/
def lengthB? (p : Prefix) (b : ByteArray) : Except DecodeError (Nat × Nat) :=
  match p with
  | .uvarint => (Varint.decodeB? b).map fun (v, k) => (v.val, k)
  | .u16be =>
    if h : 2 ≤ b.size then .ok (b[0].toNat * 256 + b[1].toNat, 2) else .error .truncated

/-- The header at the front of `b`: the payload length and the header
size. A length over the cap is `malformed`. This is the cap check of
the IO path, so it runs before any payload read. -/
def headerB? (p : Prefix) (cap : Nat) (b : ByteArray) : Except DecodeError (Nat × Nat) :=
  match lengthB? p b with
  | .error e => .error e
  | .ok (len, size) => if len ≤ cap ∧ len ≤ p.maxLen then .ok (len, size) else .error .malformed

/-- A header that passes holds a length inside the cap and the prefix.
`read` allocates the payload from this length, so the theorem is the
cap rule of §5.1 on the IO path. -/
theorem headerB?LeCap {p : Prefix} {cap : Nat} {b : ByteArray} {len size : Nat}
    (h : headerB? p cap b = .ok (len, size)) : len ≤ cap ∧ len ≤ p.maxLen := by
  unfold headerB? at h
  split at h
  · cases h
  · split at h
    · next hfit =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hfit
    · cases h

/-- A length over the cap is `malformed` on the production path too. -/
theorem headerB?OverCap {p : Prefix} {cap : Nat} {b : ByteArray} {len size : Nat}
    (hl : lengthB? p b = .ok (len, size)) (hcap : cap < len) :
    headerB? p cap b = .error .malformed := by
  simp only [headerB?, hl]
  split
  · next hfit => omega
  · rfl

/-- The wire bytes of a frame with this payload. `none` when the payload
does not fit the cap or the prefix. The sender splits it first. -/
def encodeB? (p : Prefix) (cap : Nat) (payload : ByteArray) : Option ByteArray :=
  if payload.size ≤ cap ∧ payload.size ≤ p.maxLen then
    some (ofNatList (encodeLength p payload.size) ++ payload)
  else none

/-- `encodeB?` writes a frame exactly when the payload fits. -/
theorem isSomeEncodeB? (p : Prefix) (cap : Nat) (payload : ByteArray) :
    (encodeB? p cap payload).isSome = decide (payload.size ≤ cap ∧ payload.size ≤ p.maxLen) := by
  simp only [encodeB?]
  split <;> simp_all

/-- One frame from the front of `b`, on `ByteArray`. The harness pins
it to `Frame.decode?`. The IO path uses `headerB?` in the same way. The
`ofList?` check cannot fail after `headerB?` passed, but it gives the
frame its proof fields. -/
def decodeB? (p : Prefix) (cap : Nat) (b : ByteArray) :
    Except DecodeError (Frame p cap × ByteArray) :=
  match headerB? p cap b with
  | .error e => .error e
  | .ok (len, size) =>
    if b.size < size + len then .error .truncated
    else
      match Frame.ofList? p cap (toNatList (b.extract size (size + len))) with
      | some f => .ok (f, b.extract (size + len) b.size)
      | none => .error .malformed

/-! ## The IO path -/

/-- One frame through the reader: the payload, and the reader that holds
the bytes after it.

* `.ok (some …)`: a frame arrived.
* `.ok none`: the stream ended, between frames or inside one.
* `.error .malformed`: the prefix breaks the spec, or the length is
  over the cap. The read stops before it takes a payload byte, and the
  caller closes the connection (§3.5).

The payload read allocates at most `cap` bytes and one chunk more
(`headerB?LeCap`). -/
def read (r : BufReader) (p : Prefix) (cap : Nat) :
    Async (Except DecodeError (Option (ByteArray × BufReader))) := do
  let mut r := r
  repeat
    -- The parse reads a window of `Varint.maxBytes` bytes, so it copies
    -- 9 bytes at most for any buffer size. No header is longer: a
    -- varint ends inside its 9-byte budget, and a `u16be` prefix takes
    -- 2. The window answers as the whole buffer would.
    match headerB? p cap (r.peek Varint.maxBytes) with
    | .ok (len, size) =>
      match ← (r.drop size).readExactly len with
      | some (payload, rest) => return .ok (some (payload, rest))
      | none => return .ok none
    | .error .malformed => return .error .malformed
    | .error .truncated =>
      -- The buffer holds less than a header: at most 8 varint bytes, or
      -- one byte of a `u16be` prefix. One more chunk can complete it.
      -- Park: the bytes of the peer wake the fill, and so does the
      -- close of the connection.
      match ← r.fill with
      | some more => r := more
      | none => return .ok none
  return .ok none

end Streams.Framing
