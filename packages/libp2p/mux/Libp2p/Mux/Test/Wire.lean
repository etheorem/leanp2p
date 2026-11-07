import Bytes

/-!
# Private test wire

The frame of `Mux.test` (`packages/libp2p/mux/docs/ARCHITECTURE.md`,
Private frame). The header is nine bytes: a kind, a stream id, and a
length. Each field is fixed-width and big-endian. A data payload
follows the header. An open, a fin, and a reset carry no payload.

`Header` is every nine-byte spelling whose kind is one of the four
codes. A stream id of zero and a length outside the data rule are
still headers. `LawfulCodec` holds for every such header.

`Frame` stores the stream id rule and the length rule in its fields,
so a value satisfies both, and `LawfulCodec` holds for it. `takeFrame`
is the check that builds one. A data length above `testPayloadCap`
fails in that check, before `takeBytes` reads a body.

`Parser` accepts `ByteArray` chunks. `feed`, `feedB`, and `drain`
each emit at most `parserFrameBudget` complete frames and keep the
rest. A partial body stores the bytes already received. The next
chunk fills the count still required. `feedB` copies a body only
after the cap check, and only up to the bytes still required. A chunk
of any length is accepted. The session slices a connection read
before it calls `feedB`. A later session reads the gap when the
connection ends. This module leaves that decision alone.
-/

set_option autoImplicit false

namespace Libp2p.Mux.Test.Wire

open Bytes

/-! ## Widths and codes -/

/-- A header is one kind byte, then a stream id, then a length. -/
def headerSize : Nat := 9

/-- The most bytes one data payload of this test session may carry. -/
def testPayloadCap : Nat := 16 * 1024

/-- The four kinds the private frame names. -/
inductive Kind where
  /-- Open a stream. -/
  | open
  /-- Bytes for an open stream. -/
  | data
  /-- Half-close one direction. -/
  | fin
  /-- Abort both directions for new operations. -/
  | reset
  deriving DecidableEq, Repr, BEq

namespace Kind

/-- The kind byte. The architecture table is the list this matches. -/
def toCode : Kind → Nat
  | .open => 1
  | .data => 2
  | .fin => 3
  | .reset => 4

/-- The kind of a byte, when the byte is one of the four codes. -/
def ofCode? : Nat → Option Kind
  | 1 => some .open
  | 2 => some .data
  | 3 => some .fin
  | 4 => some .reset
  | _ => none

end Kind

/-- The length rule. Data takes between one byte and `testPayloadCap`.
A control kind takes an empty payload. -/
def lengthOk (k : Kind) (n : Nat) : Bool :=
  match k with
  | .data => n != 0 && decide (n ≤ testPayloadCap)
  | _ => n == 0

/-! ## Big-endian `UInt32` -/

/-- The unsigned value of four big-endian bytes. -/
private def pack (a b c d : Nat) : Nat :=
  ((a * 256 + b) * 256 + c) * 256 + d

/-- Four bytes pack to a value `UInt32.ofNatLT` accepts. -/
private theorem pack_lt {a b c d : Nat}
    (_ha : a < 256) (_hb : b < 256) (_hc : c < 256) (_hd : d < 256) :
    pack a b c d < UInt32.size := by
  simp only [pack, UInt32.size]
  omega

/-- Four big-endian bytes as a `UInt32`. Each byte is below 256, so
`ofNatLT` does not reduce the sum. -/
private def be32 (a b c d : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (hd : d < 256) : UInt32 :=
  UInt32.ofNatLT (pack a b c d) (pack_lt ha hb hc hd)

/-- The four big-endian bytes of a `UInt32`. -/
def bytes32 (v : UInt32) : List Nat :=
  let n := v.toNat
  [n / 16777216, n / 65536 % 256, n / 256 % 256, n % 256]

private theorem be32_bytes32 (v : UInt32) :
    be32 (v.toNat / 16777216) (v.toNat / 65536 % 256) (v.toNat / 256 % 256) (v.toNat % 256)
      (by have := v.toNat_lt; omega) (by have := v.toNat_lt; omega)
      (by have := v.toNat_lt; omega) (by have := v.toNat_lt; omega) = v := by
  apply UInt32.toNat_inj.mp
  simp only [be32, UInt32.toNat_ofNatLT, pack]
  have := v.toNat_lt
  omega

private theorem bytes32_be32 {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (hd : d < 256) : bytes32 (be32 a b c d ha hb hc hd) = [a, b, c, d] := by
  simp only [bytes32, be32, UInt32.toNat_ofNatLT]
  have h :
      pack a b c d / 16777216 = a ∧
      pack a b c d / 65536 % 256 = b ∧
      pack a b c d / 256 % 256 = c ∧
      pack a b c d % 256 = d := by
    simp only [pack]
    omega
  obtain ⟨ha, hb, hc, hd⟩ := h
  simp [ha, hb, hc, hd]

/-- Four `UInt8` values, big-endian. `UInt8.toNat` is below 256. -/
private def be32Of (a b c d : UInt8) : UInt32 :=
  be32 a.toNat b.toNat c.toNat d.toNat
    (by simpa [UInt8.size] using a.toNat_lt)
    (by simpa [UInt8.size] using b.toNat_lt)
    (by simpa [UInt8.size] using c.toNat_lt)
    (by simpa [UInt8.size] using d.toNat_lt)

/-! ## Header -/

/-- A kind byte and the two `UInt32` fields. The stream id may be zero.
The length may sit outside the data rule. Those checks belong to `Frame`. -/
structure Header where
  kind : Kind
  streamId : UInt32
  length : UInt32
  deriving DecidableEq, Repr, BEq

namespace Header

/-- The nine header bytes. -/
def encode (h : Header) : List Nat :=
  h.kind.toCode :: (bytes32 h.streamId ++ bytes32 h.length)

/-- The kind at the front of a header. A short input is `truncated`.
A non-byte, or a byte outside the four codes, is `malformed`. -/
private def readKind : List Nat → Except DecodeError (Kind × List Nat)
  | [] => .error .truncated
  | 1 :: rest => .ok (.open, rest)
  | 2 :: rest => .ok (.data, rest)
  | 3 :: rest => .ok (.fin, rest)
  | 4 :: rest => .ok (.reset, rest)
  | _ :: _ => .error .malformed

/-- The next big-endian `UInt32`. Fewer than four bytes is `truncated`
when those bytes are bytes. A non-byte among them is `malformed`. -/
private def readU32 : List Nat → Except DecodeError (UInt32 × List Nat)
  | a :: b :: c :: d :: rest =>
    if ha : a < 256 then
      if hb : b < 256 then
        if hc : c < 256 then
          if hd : d < 256 then
            .ok (be32 a b c d ha hb hc hd, rest)
          else
            .error .malformed
        else
          .error .malformed
      else
        .error .malformed
    else
      .error .malformed
  | l => if l.any (· ≥ 256) then .error .malformed else .error .truncated

private theorem readKind_open {t : List Nat} {k : Kind} {rest : List Nat}
    (h : readKind (1 :: t) = .ok (k, rest)) : k = Kind.open ∧ t = rest := by
  simp only [readKind, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2⟩

private theorem readKind_data {t : List Nat} {k : Kind} {rest : List Nat}
    (h : readKind (2 :: t) = .ok (k, rest)) : k = Kind.data ∧ t = rest := by
  simp only [readKind, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2⟩

private theorem readKind_fin {t : List Nat} {k : Kind} {rest : List Nat}
    (h : readKind (3 :: t) = .ok (k, rest)) : k = Kind.fin ∧ t = rest := by
  simp only [readKind, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2⟩

private theorem readKind_reset {t : List Nat} {k : Kind} {rest : List Nat}
    (h : readKind (4 :: t) = .ok (k, rest)) : k = Kind.reset ∧ t = rest := by
  simp only [readKind, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2⟩

private theorem readKind_inv {l : List Nat} {k : Kind} {rest : List Nat}
    (h : readKind l = .ok (k, rest)) : l = k.toCode :: rest := by
  cases l with
  | nil => simp [readKind] at h
  | cons n t =>
    match n with
    | 0 => simp [readKind] at h
    | 1 =>
      obtain ⟨hk, rfl⟩ := readKind_open h
      cases k <;> simp at hk <;> (try cases hk) <;> simp [Kind.toCode]
    | 2 =>
      obtain ⟨hk, rfl⟩ := readKind_data h
      cases k <;> simp at hk <;> (try cases hk) <;> simp [Kind.toCode]
    | 3 =>
      obtain ⟨hk, rfl⟩ := readKind_fin h
      cases k <;> simp at hk <;> (try cases hk) <;> simp [Kind.toCode]
    | 4 =>
      obtain ⟨hk, rfl⟩ := readKind_reset h
      cases k <;> simp at hk <;> (try cases hk) <;> simp [Kind.toCode]
    | n + 5 =>
      simp [readKind] at h

private theorem readU32_inv {l : List Nat} {v : UInt32} {rest : List Nat}
    (h : readU32 l = .ok (v, rest)) : l = bytes32 v ++ rest := by
  match l with
  | a :: b :: c :: d :: rest' =>
    simp only [readU32] at h
    split at h
    · next ha =>
      split at h
      · next hb =>
        split at h
        · next hc =>
          split at h
          · next hd =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨hv, rfl⟩ := h
            have hbytes : bytes32 v = [a, b, c, d] := by
              simpa [← hv] using bytes32_be32 ha hb hc hd
            simp [hbytes]
          · cases h
        · cases h
      · cases h
    · cases h
  | [] => simp [readU32] at h
  | [_] =>
    simp only [readU32] at h
    split at h <;> cases h
  | [_, _] =>
    simp only [readU32] at h
    split at h <;> cases h
  | [_, _, _] =>
    simp only [readU32] at h
    split at h <;> cases h

private theorem readU32_bytes32 (v : UInt32) (rest : List Nat) :
    readU32 (bytes32 v ++ rest) = .ok (v, rest) := by
  have h0 : v.toNat / 16777216 < 256 := by have := v.toNat_lt; omega
  have h1 : v.toNat / 65536 % 256 < 256 := by have := v.toNat_lt; omega
  have h2 : v.toNat / 256 % 256 < 256 := by have := v.toNat_lt; omega
  have h3 : v.toNat % 256 < 256 := by have := v.toNat_lt; omega
  simp only [bytes32, List.cons_append, List.nil_append, readU32]
  rw [dite_eq_left h0, dite_eq_left h1, dite_eq_left h2, dite_eq_left h3]
  apply congrArg (fun id => Except.ok (id, rest))
  apply UInt32.toNat_inj.mp
  simp only [be32, UInt32.toNat_ofNatLT, pack]
  have := v.toNat_lt
  omega

/-- One header, and the bytes after it. -/
def decode? (l : List Nat) : Except DecodeError (Header × List Nat) :=
  match readKind l with
  | .error e => .error e
  | .ok (kind, l1) =>
    match readU32 l1 with
    | .error e => .error e
    | .ok (streamId, l2) =>
      match readU32 l2 with
      | .error e => .error e
      | .ok (length, rest) => .ok ({ kind, streamId, length }, rest)

theorem decode?_append (h : Header) (rest : List Nat) :
    decode? (encode h ++ rest) = .ok (h, rest) := by
  have hlist :
      encode h ++ rest = h.kind.toCode :: (bytes32 h.streamId ++ (bytes32 h.length ++ rest)) := by
    simp [encode, List.cons_append, List.append_assoc]
  rw [hlist]
  cases hk : h.kind <;> simp only [decode?, readKind, Kind.toCode] <;>
    rw [readU32_bytes32] <;> dsimp <;> rw [readU32_bytes32] <;> dsimp <;> cases h <;> rw [← hk] <;> rfl

private theorem encode_of_decode {l : List Nat} {h : Header} {rest : List Nat}
    (hd : decode? l = .ok (h, rest)) : encode h ++ rest = l := by
  simp only [decode?] at hd
  split at hd
  · cases hd
  · next kind l1 hk =>
    split at hd
    · cases hd
    · next streamId l2 hi =>
      split at hd
      · cases hd
      · next length rest' hl =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        simp [encode, readKind_inv hk, readU32_inv hi, readU32_inv hl, List.append_assoc]

instance : Codec Header where
  encode := encode
  decode? := decode?

instance : LawfulCodec Header where
  decodeEncode h := by
    show decode? (encode h) = .ok (h, [])
    simpa using decode?_append h []
  encodeDecode _l h rest hd := by
    show encode h ++ rest = _
    exact encode_of_decode hd

/-- The header bytes as a `ByteArray`. -/
def encodeB (h : Header) : ByteArray :=
  ofNatList (encode h)

/-- One header from the front of `b`. The walk uses the same `be32`
bounds as the model. -/
def decodeB? (b : ByteArray) : Except DecodeError (Header × ByteArray) :=
  if hsz : headerSize ≤ b.size then
    have h0 : 0 < b.size := by simp only [headerSize] at hsz; omega
    have h1 : 1 < b.size := by simp only [headerSize] at hsz; omega
    have h2 : 2 < b.size := by simp only [headerSize] at hsz; omega
    have h3 : 3 < b.size := by simp only [headerSize] at hsz; omega
    have h4 : 4 < b.size := by simp only [headerSize] at hsz; omega
    have h5 : 5 < b.size := by simp only [headerSize] at hsz; omega
    have h6 : 6 < b.size := by simp only [headerSize] at hsz; omega
    have h7 : 7 < b.size := by simp only [headerSize] at hsz; omega
    have h8 : 8 < b.size := by simp only [headerSize] at hsz; omega
    match Kind.ofCode? (b[0]'h0).toNat with
    | none => .error .malformed
    | some kind =>
      let streamId := be32Of (b[1]'h1) (b[2]'h2) (b[3]'h3) (b[4]'h4)
      let length := be32Of (b[5]'h5) (b[6]'h6) (b[7]'h7) (b[8]'h8)
      .ok ({ kind, streamId, length }, b.extract headerSize b.size)
  else
    .error .truncated

end Header

/-! ## Frame -/

/-- A frame the length rule and the stream id rule both allow. -/
structure Frame where
  kind : Kind
  streamId : UInt32
  payload : List Nat
  bytes : ∀ x ∈ payload, x < 256
  idOk : streamId ≠ 0
  fits : lengthOk kind payload.length = true

namespace Frame

theorem ext {a b : Frame} (hk : a.kind = b.kind) (hi : a.streamId = b.streamId)
    (hp : a.payload = b.payload) : a = b := by
  cases a
  cases b
  cases hk
  cases hi
  cases hp
  rfl

/-- A control frame. The payload is empty. -/
def ofControl (k : Kind) (id : UInt32) (hk : k ≠ .data) (hid : id ≠ 0) : Frame where
  kind := k
  streamId := id
  payload := []
  bytes := by
    intro _ hx
    cases hx
  idOk := hid
  fits := by
    match k, hk with
    | .open, _ => rfl
    | .fin, _ => rfl
    | .reset, _ => rfl
    | .data, hk => exact (hk rfl).elim

/-- A data frame whose payload satisfies the length rule. -/
def ofData (id : UInt32) (payload : List Nat) (hid : id ≠ 0)
    (hb : ∀ x ∈ payload, x < 256) (hs : lengthOk .data payload.length = true) : Frame where
  kind := .data
  streamId := id
  payload := payload
  bytes := hb
  idOk := hid
  fits := hs

instance : DecidableEq Frame := fun a b =>
  if h : a.kind = b.kind ∧ a.streamId = b.streamId ∧ a.payload = b.payload then
    isTrue (ext h.1 h.2.1 h.2.2)
  else
    isFalse fun heq => by
      apply h
      cases heq
      exact ⟨rfl, rfl, rfl⟩

instance : BEq Frame where
  beq a b := a.kind == b.kind && a.streamId == b.streamId && a.payload == b.payload

end Frame

/-- The payload length fits in the `UInt32` length field. `lengthOk`
bounds it by `testPayloadCap` before `ofNatLT`. -/
private theorem payload_lt_size (f : Frame) : f.payload.length < UInt32.size := by
  have h := f.fits
  have hc : testPayloadCap < UInt32.size := by decide
  cases hk : f.kind <;> simp only [lengthOk, hk] at h
  · simp only [beq_iff_eq] at h
    omega
  · simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
    omega
  · simp only [beq_iff_eq] at h
    omega
  · simp only [beq_iff_eq] at h
    omega

/-- The header a frame writes. The length is the payload length. -/
private def headerOf (f : Frame) : Header where
  kind := f.kind
  streamId := f.streamId
  length := UInt32.ofNatLT f.payload.length (payload_lt_size f)

namespace Frame

/-- The header, then the payload. -/
def encode (f : Frame) : List Nat :=
  Header.encode (headerOf f) ++ f.payload

/-- The first `k` model bytes. A non-byte in that prefix is `malformed`.
A short prefix of bytes is `truncated`. -/
private def takeBytes (k : Nat) (l : List Nat) : Except DecodeError (List Nat × List Nat) :=
  if ¬∀ x ∈ l.take k, x < 256 then .error .malformed
  else if l.length < k then .error .truncated
  else .ok (l.take k, l.drop k)

private theorem takeBytesAppend {b : List Nat} (rest : List Nat) (h : ∀ x ∈ b, x < 256) :
    takeBytes b.length (b ++ rest) = .ok (b, rest) := by
  have htake : (b ++ rest).take b.length = b := by simp
  unfold takeBytes
  rw [htake]
  split
  · next hn => exact absurd h hn
  · split
    · next hl => simp at hl; omega
    · simp

private theorem ofTakeBytes {k : Nat} {l b rest : List Nat}
    (h : takeBytes k l = .ok (b, rest)) :
    b ++ rest = l ∧ b.length = k ∧ ∀ x ∈ b, x < 256 := by
  unfold takeBytes at h
  split at h
  · cases h
  · next hbytes =>
    split at h
    · cases h
    · next _hlen =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨List.take_append_drop k l, ?_, by simpa using hbytes⟩
      simp only [List.length_take]
      omega

/-- The data frame for a length that already passed `lengthOk`.
`takeBytes` runs only after that check. -/
private def finishData (h : Header) (n : Nat) (_hn : n = h.length.toNat) (hid : h.streamId ≠ 0)
    (hs : lengthOk Kind.data n = true) (rest : List Nat) : Except DecodeError (Frame × List Nat) :=
  match ht : takeBytes n rest with
  | .error e => .error e
  | .ok (payload, after) =>
    .ok (ofData h.streamId payload hid (ofTakeBytes ht).2.2 (by
      rw [(ofTakeBytes ht).2.1]
      exact hs), after)

/-- A frame from a decoded header and the bytes after it.
A failing length rule returns `malformed` before `takeBytes`. -/
private def takeFrame (h : Header) (rest : List Nat) : Except DecodeError (Frame × List Nat) :=
  if hid : h.streamId ≠ 0 then
    if hk : h.kind = Kind.data then
      if hs : lengthOk Kind.data h.length.toNat = true then
        finishData h h.length.toNat rfl hid hs rest
      else
        .error .malformed
    else if _hs : lengthOk h.kind h.length.toNat = true then
      .ok (ofControl h.kind h.streamId hk hid, rest)
    else
      .error .malformed
  else
    .error .malformed

/-- A data length above `testPayloadCap` is `malformed` on the header
alone. `takeFrame` returns before it reads `rest`. -/
private theorem takeFrame_overCap {h : Header} {rest : List Nat}
    (hk : h.kind = Kind.data) (hid : h.streamId ≠ 0) (hc : testPayloadCap < h.length.toNat) :
    takeFrame h rest = .error .malformed := by
  have hs : lengthOk Kind.data h.length.toNat = false := by
    simp only [lengthOk, Bool.and_eq_false_iff]
    exact Or.inr (decide_eq_false (by omega : ¬h.length.toNat ≤ testPayloadCap))
  unfold takeFrame
  rw [dite_eq_left hid, dite_eq_left hk, dite_eq_right (by simp [hs])]

/-- One frame from the front of the model, and the suffix. -/
def decode? (l : List Nat) : Except DecodeError (Frame × List Nat) :=
  match Header.decode? l with
  | .error e => .error e
  | .ok (h, rest) => takeFrame h rest

/-- A declared data length above `testPayloadCap` is `malformed` once
the header is present, including when the body bytes are absent. -/
theorem decode?_overCap {l : List Nat} {h : Header} {rest : List Nat}
    (hd : Header.decode? l = .ok (h, rest)) (hk : h.kind = Kind.data) (hid : h.streamId ≠ 0)
    (hc : testPayloadCap < h.length.toNat) : decode? l = .error .malformed := by
  simp only [decode?, hd, takeFrame_overCap hk hid hc]

private theorem control_payload_nil {f : Frame} (hk : f.kind ≠ Kind.data) : f.payload = [] := by
  have hlen := f.fits
  cases hk' : f.kind <;> simp only [lengthOk, hk'] at hlen
  · simp only [beq_iff_eq] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  · exact absurd hk' hk
  · simp only [beq_iff_eq] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  · simp only [beq_iff_eq] at hlen
    exact List.eq_nil_of_length_eq_zero hlen

private theorem takeFrame_control (f : Frame) (rest : List Nat) (hk : f.kind ≠ Kind.data) :
    takeFrame (headerOf f) (f.payload ++ rest) = .ok (f, rest) := by
  have hp : f.payload = [] := control_payload_nil hk
  unfold takeFrame
  rw [dite_eq_left (by simpa [headerOf] using f.idOk)]
  rw [dite_eq_right (by simpa [headerOf] using hk)]
  rw [dite_eq_left (by
    cases hk' : f.kind <;> simp only [hk'] at hk
    · simp [hk', headerOf, hp, lengthOk]
    · exact absurd rfl hk
    · simp [hk', headerOf, hp, lengthOk]
    · simp [hk', headerOf, hp, lengthOk])]
  simp only [hp, List.nil_append]
  exact congrArg (fun g => Except.ok (g, rest))
    (ext (by unfold ofControl; rfl) (by unfold ofControl; rfl) (by unfold ofControl; simp [hp]))

private theorem takeFrame_data (f : Frame) (rest : List Nat) (hk : f.kind = Kind.data) :
    takeFrame (headerOf f) (f.payload ++ rest) = .ok (f, rest) := by
  have hs : lengthOk Kind.data f.payload.length = true := by simpa [hk] using f.fits
  unfold takeFrame
  rw [dite_eq_left (by simpa [headerOf] using f.idOk)]
  rw [dite_eq_left (by simpa [headerOf] using hk)]
  rw [dite_eq_left (by simp [headerOf, UInt32.toNat_ofNatLT, hs])]
  unfold finishData
  have hlen : (headerOf f).length.toNat = f.payload.length := by
    simp [headerOf, UInt32.toNat_ofNatLT]
  split
  · next _ ht =>
    rw [hlen] at ht
    rw [takeBytesAppend rest f.bytes] at ht
    cases ht
  · next _ _ ht =>
    rw [hlen] at ht
    rw [takeBytesAppend rest f.bytes] at ht
    simp only [Except.ok.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact congrArg (fun g => Except.ok (g, rest)) (ext hk.symm rfl rfl)

private theorem takeFrame_append (f : Frame) (rest : List Nat) :
    takeFrame (headerOf f) (f.payload ++ rest) = .ok (f, rest) := by
  cases hk : f.kind
  · exact takeFrame_control f rest (by simp [hk])
  · exact takeFrame_data f rest hk
  · exact takeFrame_control f rest (by simp [hk])
  · exact takeFrame_control f rest (by simp [hk])

theorem decode?_append (f : Frame) (rest : List Nat) :
    decode? (encode f ++ rest) = .ok (f, rest) := by
  have hbuf : encode f ++ rest = Header.encode (headerOf f) ++ (f.payload ++ rest) := by
    simp [encode, List.append_assoc]
  simpa [decode?, hbuf, Header.decode?_append (headerOf f) (f.payload ++ rest)] using
    takeFrame_append f rest

private theorem encode_of_decode {l : List Nat} {f : Frame} {rest : List Nat}
    (hd : decode? l = .ok (f, rest)) : encode f ++ rest = l := by
  simp only [decode?] at hd
  split at hd
  · cases hd
  · next h rest1 hh =>
    have hhead := Header.encode_of_decode hh
    simp only [takeFrame, finishData] at hd
    split at hd
    · next hid =>
      split at hd
      · next hk =>
        split at hd
        · next hs =>
          split at hd
          · cases hd
          · next payload after ht =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hd
            obtain ⟨hf, rfl⟩ := hd
            obtain ⟨hsplit, hlen, _⟩ := ofTakeBytes ht
            have hpay : f.payload = payload := by
              simpa [ofData] using (congrArg Frame.payload hf).symm
            have hkind : f.kind = Kind.data := (congrArg Frame.kind hf).symm
            have hidf : f.streamId = h.streamId := (congrArg Frame.streamId hf).symm
            have hlenU : h.length = UInt32.ofNatLT f.payload.length (payload_lt_size f) := by
              apply UInt32.toNat_inj.mp
              simp [hlen, hpay]
            have hhdr : h = headerOf f := by
              cases h
              rw [Header.mk.injEq]
              exact ⟨hk.trans hkind.symm, hidf.symm, hlenU⟩
            calc
              encode f ++ after = Header.encode (headerOf f) ++ f.payload ++ after := by
                simp [encode]
              _ = h.encode ++ (payload ++ after) := by
                rw [hhdr, hpay, List.append_assoc]
              _ = h.encode ++ rest1 := by rw [hsplit]
              _ = l := hhead
        · cases hd
      · next hk =>
        split at hd
        · next hs =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hd
          obtain ⟨hf, rfl⟩ := hd
          have hp : f.payload = [] := by
            simpa [ofControl] using (congrArg Frame.payload hf).symm
          have hkind : f.kind = h.kind := (congrArg Frame.kind hf).symm
          have hidf : f.streamId = h.streamId := (congrArg Frame.streamId hf).symm
          have hzero : h.length.toNat = 0 := by
            cases hk' : h.kind <;> simp only [lengthOk, hk', beq_iff_eq] at hs
            · exact hs
            · exact absurd hk' hk
            · exact hs
            · exact hs
          have hlenU : h.length = UInt32.ofNatLT f.payload.length (payload_lt_size f) := by
            apply UInt32.toNat_inj.mp
            simp [hp, hzero]
          have hhdr : h = headerOf f := by
            cases h
            rw [Header.mk.injEq]
            exact ⟨hkind.symm, hidf.symm, hlenU⟩
          calc
            encode f ++ rest1 = Header.encode (headerOf f) ++ f.payload ++ rest1 := by
              simp [encode]
            _ = h.encode ++ rest1 := by
              rw [hhdr, hp, List.append_nil]
            _ = l := hhead
        · cases hd
    · cases hd

instance : Codec Frame where
  encode := encode
  decode? := decode?

instance : LawfulCodec Frame where
  decodeEncode f := by
    show decode? (encode f) = .ok (f, [])
    simpa using decode?_append f []
  encodeDecode _l f rest hd := by
    show encode f ++ rest = _
    exact encode_of_decode hd

/-- The frame bytes as a `ByteArray`. -/
def encodeB (f : Frame) : ByteArray :=
  ofNatList (encode f)

/-- One frame from the front of `b`. The length rule runs before
`extract`, so an over-cap length does not copy a body. -/
def decodeB? (b : ByteArray) : Except DecodeError (Frame × ByteArray) :=
  match Header.decodeB? b with
  | .error e => .error e
  | .ok (h, rest) =>
    if hid : h.streamId ≠ 0 then
      let n := h.length.toNat
      if hk : h.kind = Kind.data then
        if hs : lengthOk Kind.data n = true then
          if rest.size < n then
            .error .truncated
          else
            let payload := toNatList (rest.extract 0 n)
            if hlen : payload.length = n then
              if hb : ∀ x ∈ payload, x < 256 then
                .ok (ofData h.streamId payload hid hb (by simpa [hlen] using hs),
                  rest.extract n rest.size)
              else
                .error .malformed
            else
              .error .malformed
        else
          .error .malformed
      else if _hs : lengthOk h.kind n = true then
        .ok (ofControl h.kind h.streamId hk hid, rest)
      else
        .error .malformed
    else
      .error .malformed

end Frame

/-! ## Incremental parser -/

/-- What an unfinished feed is waiting for. The session maps a nonempty
gap at connection end to a protocol error. An empty gap leaves the
connection-end cause to that session. -/
inductive Gap where
  | empty
  | partialHeader
  | partialBody
  deriving DecidableEq, Repr, BEq

/-- Complete frames one owner-loop turn takes from this parser.
The policy table in the mux architecture is this constant. -/
def parserFrameBudget : Nat := 8

/-- A data length `lengthOk` accepts is in `1 … testPayloadCap`. -/
private theorem lengthOk_data {n : Nat} (h : lengthOk Kind.data n = true) :
    0 < n ∧ n ≤ testPayloadCap := by
  simp only [lengthOk, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
  omega

/-- Bytes of a `ByteArray` are bytes. -/
private theorem toNatList_lt (b : ByteArray) : ∀ x ∈ toNatList b, x < 256 := by
  intro x hx
  simp only [toNatList, List.mem_map] at hx
  obtain ⟨u, _, rfl⟩ := hx
  simpa [UInt8.size] using u.toNat_lt

/-- The three shapes a parser may hold. Constructors stay private.
`ready` is empty, or it begins with a complete frame.
`partialHeader` is shorter than `headerSize` and nonempty.
`partialBody` is a nonzero data id, a length inside the cap, the saved
header bytes, and a body shorter than that length. -/
private inductive Raw where
  | ready (input : ByteArray)
  | partialHeader (buf : ByteArray) (hShort : buf.size < headerSize) (hPos : 0 < buf.size)
  | partialBody (streamId : UInt32) (declared : Nat) (headerBytes bodyBytes : ByteArray)
      (idOk : streamId ≠ 0) (lenOk : 0 < declared ∧ declared ≤ testPayloadCap)
      (short : bodyBytes.size < declared)

/-- Parser state. The raw constructors are private, so a caller cannot
build a control header, an over-cap length, an oversized body, two
buffers, or a non-byte entry. -/
structure Parser where
  private mk ::
  private raw : Raw

namespace Parser

/-- A parser with no buffered bytes. -/
def empty : Parser :=
  ⟨.ready ByteArray.empty⟩

/-- Empty, waiting on a header, or waiting on a body.
`ready` reports `.empty`, including when a complete frame is retained. -/
def gap (p : Parser) : Gap :=
  match p.raw with
  | .ready _ => .empty
  | .partialHeader _ _ _ => .partialHeader
  | .partialBody _ _ _ _ _ _ _ => .partialBody

/-- Bytes the parser is holding.
A partial header is shorter than `headerSize`.
A partial body holds its nine header bytes plus a body shorter than
the declared length. A ready parser holds unparsed bytes that already
arrived, including complete frames a pull did not emit. -/
def retainedBytes (p : Parser) : Nat :=
  match p.raw with
  | .ready input => input.size
  | .partialHeader buf _ _ => buf.size
  | .partialBody _ _ headerBytes bodyBytes _ _ _ => headerBytes.size + bodyBytes.size

/-- A later `drain` can emit a frame without another chunk. -/
def hasComplete (p : Parser) : Bool :=
  match p.raw with
  | .ready input => input.size != 0
  | .partialHeader _ _ _ => false
  | .partialBody _ _ _ _ _ _ _ => false

/-- Push the first `n` bytes of `src` onto `dst`.
Each step is one `push`, so a body that arrives one byte at a time
does not copy the bytes already kept. -/
private def pushCount (dst src : ByteArray) (n : Nat) : ByteArray :=
  let rec go (k : Nat) (acc : ByteArray) : ByteArray :=
    if k < n then
      if h : k < src.size then
        go (k + 1) (acc.push (src[k]'h))
      else
        acc
    else
      acc
    termination_by n - k
  go 0 dst

private def holdHeader (buf : ByteArray) : Except DecodeError Parser :=
  if h0 : buf.size = 0 then
    .ok empty
  else if h : buf.size < headerSize then
    .ok ⟨.partialHeader buf h (by omega)⟩
  else
    .error .malformed

/-- The suffix of a pull. A full frame at the front stays in `ready`.
A short header, or a data header whose body is still short, becomes
that partial shape. An illegal header fails before a body is kept. -/
private def classify (b : ByteArray) : Except DecodeError Parser :=
  if h0 : b.size = 0 then
    .ok empty
  else if h : b.size < headerSize then
    .ok ⟨.partialHeader b h (by omega)⟩
  else
    match Header.decodeB? (b.extract 0 headerSize) with
    | .error e => .error e
    | .ok (header, _) =>
      if hid : header.streamId ≠ 0 then
        if header.kind = Kind.data then
          let n := header.length.toNat
          if hlen : lengthOk Kind.data n = true then
            have lenOk := lengthOk_data hlen
            if b.size < headerSize + n then
              let bodyBytes := b.extract headerSize b.size
              if hgot : bodyBytes.size < n then
                .ok ⟨.partialBody header.streamId n (b.extract 0 headerSize) bodyBytes hid lenOk hgot⟩
              else
                .error .malformed
            else
              .ok ⟨.ready b⟩
          else
            .error .malformed
        else if header.length = 0 then
          .ok ⟨.ready b⟩
        else
          .error .malformed
      else
        .error .malformed

private def emitData (id : UInt32) (declared : Nat) (bodyBytes : ByteArray)
    (idOk : id ≠ 0) (lenOk : 0 < declared ∧ declared ≤ testPayloadCap) :
    Except DecodeError Frame :=
  let payload := toNatList bodyBytes
  if hlen : payload.length = declared then
    .ok <| Frame.ofData id payload idOk (toNatList_lt bodyBytes) (by
      simp only [lengthOk, hlen, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
      exact ⟨Nat.ne_of_gt lenOk.1, lenOk.2⟩)
  else
    .error .malformed

/-- Emit at most `budget` frames from `b`, starting at `i`.
Budget 0 keeps the suffix, including a complete frame, for a later pull. -/
private def pullBytes : Nat → ByteArray → Nat → List Frame → Except DecodeError (List Frame × Parser)
  | 0, b, i, acc =>
    (classify (b.extract i b.size)).map fun p => (acc.reverse, p)
  | budget + 1, b, i, acc =>
    if i ≥ b.size then
      .ok (acc.reverse, empty)
    else if b.size - i < headerSize then
      (holdHeader (b.extract i b.size)).map fun p => (acc.reverse, p)
    else
      match Header.decodeB? (b.extract i (i + headerSize)) with
      | .error e => .error e
      | .ok (header, _) =>
        let j := i + headerSize
        if hid : header.streamId ≠ 0 then
          if hk : header.kind = Kind.data then
            let n := header.length.toNat
            if hlen : lengthOk Kind.data n = true then
              have lenOk := lengthOk_data hlen
              if b.size - j < n then
                let bodyBytes := b.extract j b.size
                if hgot : bodyBytes.size < n then
                  .ok (acc.reverse, ⟨.partialBody header.streamId n
                    (b.extract i j) bodyBytes hid lenOk hgot⟩)
                else
                  .error .malformed
              else
                match emitData header.streamId n (b.extract j (j + n)) hid lenOk with
                | .error e => .error e
                | .ok frame => pullBytes budget b (j + n) (frame :: acc)
            else
              .error .malformed
          else if header.length = 0 then
            let frame := Frame.ofControl header.kind header.streamId hk hid
            pullBytes budget b j (frame :: acc)
          else
            .error .malformed
        else
          .error .malformed

/-- Append `chunk` to `p` and emit at most `budget` frames.
A partial body copies at most the bytes still required. It does not
encode its header again. -/
private def run (p : Parser) (chunk : ByteArray) (budget : Nat) :
    Except DecodeError (List Frame × Parser) :=
  match p.raw with
  | .ready input =>
    if input.size = 0 then
      pullBytes budget chunk 0 []
    else if chunk.size = 0 then
      pullBytes budget input 0 []
    else
      pullBytes budget (pushCount input chunk chunk.size) 0 []
  | .partialHeader buf _ _ =>
    let need := headerSize - buf.size
    let take := min need chunk.size
    let filled := pushCount buf chunk take
    let rest := chunk.extract take chunk.size
    if h : filled.size < headerSize then
      if h0 : filled.size = 0 then
        .ok ([], empty)
      else
        .ok ([], ⟨.partialHeader filled h (by omega)⟩)
    else
      pullBytes budget (filled ++ rest) 0 []
  | .partialBody id declared headerBytes bodyBytes idOk lenOk _ =>
    let need := declared - bodyBytes.size
    let take := min need chunk.size
    let filled := pushCount bodyBytes chunk take
    let rest := chunk.extract take chunk.size
    if hgot : filled.size < declared then
      .ok ([], ⟨.partialBody id declared headerBytes filled idOk lenOk hgot⟩)
    else if budget = 0 then
      .ok ([], ⟨.ready (headerBytes ++ filled ++ rest)⟩)
    else
      match emitData id declared filled idOk lenOk with
      | .error e => .error e
      | .ok frame => pullBytes (budget - 1) rest 0 [frame]

/-- Emit at most `parserFrameBudget` complete frames already in `p`.
The chunk is empty, so this needs no new connection bytes. -/
def drain (p : Parser) : Except DecodeError (List Frame × Parser) :=
  run p ByteArray.empty parserFrameBudget

/-- Append one `ByteArray` chunk and emit at most `parserFrameBudget`
frames. The copy of a data body waits until `lengthOk` accepts the
length, and it copies at most the bytes still required. Every chunk
boundary is accepted, so a long read is not a protocol error. A frame
may span any number of chunks. This function does not turn the chunk
into a model list, and it does not cap the bytes it retains. The
session slices a connection read to `testPayloadCap` before the call. -/
def feedB (p : Parser) (chunk : ByteArray) : Except DecodeError (List Frame × Parser) :=
  run p chunk parserFrameBudget

/-- `feedB` for a model chunk. A non-byte is `malformed` before the
chunk becomes a `ByteArray`. The pull emits at most `parserFrameBudget`
frames. -/
def feed (p : Parser) (chunk : List Nat) : Except DecodeError (List Frame × Parser) :=
  if chunk.any (· ≥ 256) then
    .error .malformed
  else
    feedB p (ofNatList chunk)

end Parser

end Libp2p.Mux.Test.Wire
