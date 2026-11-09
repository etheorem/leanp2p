import Libp2p.Negotiate.Constants
import Varint
import Bytes

/-!
# The multistream message

`Msg` is one multistream message: a uvarint length prefix, then the
UTF-8 bytes of the text plus a trailing newline. The length counts the
newline (ARCHITECTURE §3.2, package docs "Public surface").

The decoder splits one frame at the index the prefix computes, then
runs the computed inverse of the payload map: it reads the body as
UTF-8, re-encodes it, and compares. `Bytes.toString?` rejects bad
UTF-8. The comparison rejects a missing trailing newline and a model
value at or above 256. So the `encodeDecode` proof needs no UTF-8
reasoning.

The 1 KiB cap is checked in `splitFrame`, before any payload
inspection (contract 1). The `ls` reply framing walks its entries as
ordinary `Msg` frames on a fuel counter, so the entry reader reuses
the proved frame decoder.
-/

set_option autoImplicit false

namespace Libp2p.Negotiate

open Bytes (DecodeError)

/-! ## The payload map and its inverse -/

/-- The model bytes of a text, newline included. The one total map
between texts and payloads. -/
def payloadOf (s : String) : List Nat :=
  Bytes.toNatList (Bytes.ofString (s ++ "\n"))

/-- A total `UVarint` constructor for a length. `initiatorStart` and
`responderStart` keep the upgrade's lengths at or under `maxMsg`; the
modulo keeps the constructor total for any input. -/
def boundedVarint (n : Nat) : Varint.UVarint :=
  ⟨n % Varint.limit, Nat.mod_lt _ (by decide)⟩

/-- The total text encoder: a uvarint length prefix, then the payload. -/
def encodeText (s : String) : List Nat :=
  Varint.encode (boundedVarint (payloadOf s).length) ++ payloadOf s

/-- A multistream message. `text` excludes the trailing newline.
`fits` is the proof-carrying cap fact of root §3.7: the message fits
the 1 KiB cap, so the encoder writes the exact length. -/
structure Msg where
  text : String
  fits : (Bytes.ofString (text ++ "\n")).size ≤ maxMsg
  deriving Repr, DecidableEq

/-- The model payload length equals the byte size of the text with its
newline. -/
theorem payloadOfLength (s : String) :
    (payloadOf s).length = (Bytes.ofString (s ++ "\n")).size := by
  simp only [payloadOf, Bytes.toNatList, List.length_map, Array.length_toList]
  rfl

/-- The payload of a text is its UTF-8 bytes plus the newline byte. -/
theorem payloadOfEq (s : String) :
    payloadOf s = Bytes.toNatList (Bytes.ofString s) ++ [10] := by
  simp [payloadOf, Bytes.toNatList, Bytes.ofString, String.toByteArray_append]
  exact ⟨10, by decide, rfl⟩

/-- Every payload ends in a newline, so it is never empty. -/
theorem payloadOfNe (s : String) : payloadOf s ≠ [] := by
  rw [payloadOfEq]; simp

/-- The checked constructor. The tests build messages through it. -/
def Msg.ofText? (s : String) : Option Msg :=
  if h : (Bytes.ofString (s ++ "\n")).size ≤ maxMsg then some ⟨s, h⟩ else none

/-- A text whose frame fits the 1 KiB cap. `initiatorStart` and
`responderStart` call this before any write, so a configured id that
would produce an over-cap frame is a protocol error rather than a frame
the decoder refuses (root §5.1). -/
def fitsText (s : String) : Bool :=
  decide ((Bytes.ofString (s ++ "\n")).size ≤ maxMsg)

/-- The frame the codec writes for a message. -/
def encodeMsg (m : Msg) : List Nat := encodeText m.text

/-- The multistream header message. The literal lives in `Constants`. -/
def header : Msg := ⟨protocolId.toString, by decide⟩

/-! ## The frame split -/

/-- Split one frame at the index the length prefix computes. The cap
is checked first, before any payload inspection (contract 1). A zero
declared length is malformed. A payload cut short is truncated, so
the caller keeps waiting. -/
def splitFrame (bs : List Nat) : Except DecodeError (List Nat × List Nat) :=
  match Varint.decode? bs with
  | .error e => .error e
  | .ok (v, rest) =>
    if maxMsg < v.val then .error .malformed
    else if v.val = 0 then .error .malformed
    else if rest.length < v.val then .error .truncated
    else .ok (rest.take v.val, rest.drop v.val)

/-- The computed inverse of `payloadOf`, checked by re-encoding. -/
def textOf? (payload : List Nat) : Option String :=
  match Bytes.toString? (Bytes.ofNatList payload.dropLast) with
  | none => none
  | some t => if payloadOf t = payload then some t else none

/-- A text read back from a payload re-encodes to that payload. -/
theorem textOf?Spec {payload : List Nat} {t : String} (h : textOf? payload = some t) :
    payloadOf t = payload := by
  unfold textOf? at h
  split at h
  · simp at h
  · split at h
    · simp_all
    · simp at h

/-- The inverse reads its own image back. -/
theorem textOf?PayloadOf (s : String) : textOf? (payloadOf s) = some s := by
  unfold textOf?
  have hd : (payloadOf s).dropLast = Bytes.toNatList (Bytes.ofString s) := by
    rw [payloadOfEq]; simp
  rw [hd, Bytes.ofNatListToNatList, Bytes.toString?OfString]
  simp

/-- A payload whose last byte is not the newline reads back as no
text. -/
theorem textOf?None {payload : List Nat} (hlast : payload.getLast? ≠ some 10) :
    textOf? payload = none := by
  unfold textOf?
  cases hto : Bytes.toString? (Bytes.ofNatList payload.dropLast) with
  | none => rfl
  | some t =>
    by_cases heq : payloadOf t = payload
    · have hpl : (payloadOf t).getLast? = some 10 := by rw [payloadOfEq]; simp
      rw [heq] at hpl
      exact (hlast hpl).elim
    · simp [heq]

/-- Decode one message and the bytes left after it. -/
def decodeMsg? (bs : List Nat) : Except DecodeError (Msg × List Nat) :=
  match splitFrame bs with
  | .error e => .error e
  | .ok (payload, rest) =>
    match textOf? payload with
    | none => .error .malformed
    | some t =>
      if hf : (Bytes.ofString (t ++ "\n")).size ≤ maxMsg then .ok (⟨t, hf⟩, rest)
      else .error .malformed

/-! ## The frame lemmas -/

/-- One shared lemma: a framed payload splits back into that payload
and the remainder. -/
theorem splitFrameEncode (s : String) (h : (payloadOf s).length ≤ maxMsg) (rest : List Nat) :
    splitFrame (encodeText s ++ rest) = .ok (payloadOf s, rest) := by
  have hlim : (payloadOf s).length < Varint.limit := by
    unfold Varint.limit Varint.maxBytes maxMsg at *; omega
  have hb : (boundedVarint (payloadOf s).length).val = (payloadOf s).length := by
    simp [boundedVarint, Nat.mod_eq_of_lt hlim]
  have hpos : 0 < (payloadOf s).length := List.length_pos_iff.mpr (payloadOfNe s)
  unfold splitFrame encodeText
  rw [List.append_assoc, Varint.decodeEncodeSuffix]
  simp only [hb]
  have h1 : ¬ maxMsg < (payloadOf s).length := by omega
  have h2 : ¬ (payloadOf s).length = 0 := by omega
  simp [h1, h2]

/-- The suffix round trip: a message decodes back from its frame plus
any remainder. The lazy dialer's coalesced read needs this form. The
frame is `encodeText m.text`, definitionally `encodeMsg m`. -/
theorem decodeMsgSuffix (m : Msg) (rest : List Nat) :
    decodeMsg? (encodeText m.text ++ rest) = .ok (m, rest) := by
  have h : (payloadOf m.text).length ≤ maxMsg := by rw [payloadOfLength]; exact m.fits
  unfold decodeMsg?
  rw [splitFrameEncode m.text h]
  simp [textOf?PayloadOf, m.fits]

/-- The inverse direction: every accepted input is the encoding of
the decoded value. No UTF-8 reasoning; `textOf?` already re-encoded. -/
theorem decodeMsgEncodeDecode (bs : List Nat) (m : Msg) (rest : List Nat)
    (h : decodeMsg? bs = .ok (m, rest)) : encodeMsg m ++ rest = bs := by
  show encodeText m.text ++ rest = bs
  unfold decodeMsg? splitFrame at h
  split at h
  · simp at h
  · rename_i payload rest0 hsplit
    split at hsplit
    · simp at hsplit
    · rename_i v r0 hdec
      have hbs := Varint.encodeDecode hdec
      split at hsplit
      · simp at hsplit
      split at hsplit
      · simp at hsplit
      split at hsplit
      · simp at hsplit
      rename_i hcap _ hlen
      simp only [Except.ok.injEq, Prod.mk.injEq] at hsplit
      obtain ⟨rfl, rfl⟩ := hsplit
      split at h
      · simp at h
      · rename_i t ht
        have hp := textOf?Spec ht
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hl : (payloadOf t).length = v.val := by
            rw [hp]; simp; omega
          have hv : boundedVarint (payloadOf t).length = v := by
            cases v; simp_all [boundedVarint, Nat.mod_eq_of_lt]
          rw [encodeText, hv, hp, List.append_assoc, List.take_append_drop]
          exact hbs.symm
        · simp at h

/-- The codec writes the frame and reads one message back. -/
instance : Bytes.Codec Msg where
  encode := encodeMsg
  decode? := decodeMsg?

theorem decodeMsgEncode (m : Msg) : decodeMsg? (encodeMsg m) = .ok (m, []) := by
  simpa [encodeMsg] using decodeMsgSuffix m []

/-- The round-trip law that §3.2 requires. -/
instance : Bytes.LawfulCodec Msg where
  decodeEncode := decodeMsgEncode
  encodeDecode := by
    intro bs a rest h
    exact decodeMsgEncodeDecode bs a rest h

/-- The cap fires before the payload is read, for every payload that
follows the prefix (contract 1). -/
theorem decodeMsgCap {v : Varint.UVarint} {payload : List Nat}
    (h : maxMsg < v.val) :
    decodeMsg? (Varint.encode v ++ payload) = .error .malformed := by
  simp [decodeMsg?, splitFrame, Varint.decodeEncodeSuffix, h]

/-- A payload cut short is incomplete: more bytes may complete it. -/
theorem decodeMsgTruncated {v : Varint.UVarint} {payload : List Nat}
    (hv0 : 0 < v.val) (hcap : v.val ≤ maxMsg) (hshort : payload.length < v.val) :
    decodeMsg? (Varint.encode v ++ payload) = .error .truncated := by
  unfold decodeMsg? splitFrame
  rw [Varint.decodeEncodeSuffix]
  have h1 : ¬ maxMsg < v.val := by omega
  have h2 : ¬ v.val = 0 := by omega
  simp only [h1, h2, hshort, ite_true, ite_false]

/-- A zero declared length is malformed. -/
theorem decodeMsgZeroLength {v : Varint.UVarint} {payload : List Nat}
    (h : v.val = 0) :
    decodeMsg? (Varint.encode v ++ payload) = .error .malformed := by
  simp [decodeMsg?, splitFrame, Varint.decodeEncodeSuffix, h, maxMsg]

/-- A body whose last byte is not the newline is malformed. -/
theorem decodeMsgNoNewline {v : Varint.UVarint} {payload : List Nat}
    (hv0 : 0 < v.val) (hcap : v.val ≤ maxMsg) (hlen : payload.length = v.val)
    (hlast : payload.getLast? ≠ some 10) :
    decodeMsg? (Varint.encode v ++ payload) = .error .malformed := by
  have hnone : textOf? (List.take v.val payload) = none := by
    rw [← hlen, List.take_length]
    exact textOf?None hlast
  unfold decodeMsg? splitFrame
  rw [Varint.decodeEncodeSuffix]
  have h1 : ¬ maxMsg < v.val := by omega
  have h2 : ¬ v.val = 0 := by omega
  have h3 : ¬ payload.length < v.val := by omega
  simp only [h1, h2, h3, ite_false]
  rw [hnone]

/-- The framing budget: a message frame spans its payload plus at
most nine prefix bytes. -/
theorem encodeMsgLength (m : Msg) :
    (encodeMsg m).length ≤ maxMsg + Varint.maxBytes := by
  have h1 := Varint.lengthEncodeLe (boundedVarint (payloadOf m.text).length)
  have h2 : (payloadOf m.text).length ≤ maxMsg := by rw [payloadOfLength]; exact m.fits
  simp only [encodeMsg, encodeText, List.length_append]
  omega

/-! ## The `ls` reply framing -/

/-- One `ls` entry is an ordinary message frame: the entry's text is
the protocol id, and the frame carries the id plus its newline. -/
def lsEntries (ids : List Core.ProtocolId) : List Nat :=
  (ids.map (fun p => encodeText p.toString)).flatten

/-- The body of an `ls` reply: one entry frame per id, then the final
newline byte that ends the list. -/
def lsBody (ids : List Core.ProtocolId) : List Nat := lsEntries ids ++ [10]

/-- The full `ls` reply: the body wrapped in one uvarint length
prefix, exactly like a message. -/
def encodeLs (ids : List Core.ProtocolId) : List Nat :=
  Varint.encode (boundedVarint (lsBody ids).length) ++ lsBody ids

/-- Walk the entries of one complete `ls` body. The fuel counts
entries; the caller passes the body's byte length, which is at least
the entry count because every entry carries its newline. `[10]` alone
is the terminator, not a leading byte: a leading `0x0A` can be a
legitimate one-byte prefix for a nine-byte id. -/
def decodeEntries : Nat → List Nat → Except DecodeError (List Core.ProtocolId)
  | 0, _ => .error .malformed
  | fuel + 1, bs =>
    if bs = [10] then .ok []
    else match decodeMsg? bs with
      | .error _ => .error .malformed
      | .ok (m, rest) => (decodeEntries fuel rest).map (⟨m.text⟩ :: ·)

/-- Decode one `ls` reply frame. The outer prefix goes through the
same split and cap as a message. An entry that ends mid-body is
malformed, because only the outer prefix and length can be completed
by more bytes. -/
def decodeLs? (bs : List Nat) :
    Except DecodeError (List Core.ProtocolId × List Nat) :=
  match splitFrame bs with
  | .error e => .error e
  | .ok (body, rest) => (decodeEntries body.length body).map (·, rest)

/-- An entry frame is at least as long as its payload. -/
theorem encodeTextLength (s : String) : (payloadOf s).length ≤ (encodeText s).length := by
  simp [encodeText]

/-- The entries of an encoded list read back in order, under fuel and
cap bounds. -/
theorem decodeEntriesLs (ids : List Core.ProtocolId) (fuel : Nat)
    (hf : ids.length < fuel) (hb : (lsEntries ids).length ≤ maxMsg) :
    decodeEntries fuel (lsEntries ids ++ [10]) = .ok ids := by
  induction ids generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at hf
    | succ f => simp [decodeEntries, lsEntries]
  | cons p ps ih =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hlen : (lsEntries (p :: ps)).length =
          (encodeText p.toString).length + (lsEntries ps).length := by
        simp [lsEntries]
      have hfit : (Bytes.ofString (p.toString ++ "\n")).size ≤ maxMsg := by
        rw [← payloadOfLength]; have := encodeTextLength p.toString; omega
      have hne : lsEntries (p :: ps) ++ [10] ≠ [10] := by
        intro h
        have hl := congrArg List.length h
        rw [List.length_append, hlen] at hl
        have h0 := List.length_pos_iff.mpr (payloadOfNe p.toString)
        have h1 := encodeTextLength p.toString
        simp only [List.length_singleton] at hl
        omega
      have hsplit : lsEntries (p :: ps) ++ [10] =
          encodeText (Msg.text ⟨p.toString, hfit⟩) ++ (lsEntries ps ++ [10]) := by
        simp [lsEntries]
      simp only [decodeEntries, hne, ite_false]
      rw [hsplit, decodeMsgSuffix ⟨p.toString, hfit⟩ (lsEntries ps ++ [10])]
      change (Except.map (fun x => (⟨p.toString⟩ : Core.ProtocolId) :: x)
        (decodeEntries f (lsEntries ps ++ [10])) = .ok (p :: ps))
      rw [ih f (by simp at hf; omega) (by omega)]
      rfl

/-- The byte length of the entries is at least the id count. -/
theorem lsEntriesLength (ids : List Core.ProtocolId) :
    ids.length ≤ (lsEntries ids).length := by
  induction ids with
  | nil => simp [lsEntries]
  | cons p ps ih =>
    have h0 := List.length_pos_iff.mpr (payloadOfNe p.toString)
    have := encodeTextLength p.toString
    simp [lsEntries] at ih ⊢; omega

/-- The `ls` reply round trip. The length prefix alone delimits the
entries, so no cleanliness hypothesis is needed. -/
theorem decodeLsEncodeLs (ids : List Core.ProtocolId)
    (hbody : (lsBody ids).length ≤ maxMsg) :
    decodeLs? (encodeLs ids) = .ok (ids, []) := by
  have hlim : (lsBody ids).length < Varint.limit := by
    unfold Varint.limit Varint.maxBytes maxMsg at *; omega
  have hb : (boundedVarint (lsBody ids).length).val = (lsBody ids).length := by
    simp [boundedVarint, Nat.mod_eq_of_lt hlim]
  have hl := lsEntriesLength ids
  unfold decodeLs? encodeLs splitFrame
  rw [← List.append_nil (lsBody ids), Varint.decodeEncodeSuffix]
  simp only [hb, List.append_nil]
  have h1 : ¬ maxMsg < (lsBody ids).length := by omega
  have h2 : ¬ (lsBody ids).length = 0 := by simp [lsBody]
  simp only [h1, h2, ite_false, Nat.lt_irrefl, List.take_length, List.drop_length]
  have hb2 : (lsEntries ids).length ≤ maxMsg := by simp [lsBody] at hbody; omega
  rw [lsBody, decodeEntriesLs ids _ (by simp; omega) hb2]
  rfl

/-- A frame that splits back is exactly the prefix plus body plus
remainder. -/
theorem splitFrameInv {bs body rest : List Nat} (h : splitFrame bs = .ok (body, rest)) :
    Varint.encode (boundedVarint body.length) ++ body ++ rest = bs := by
  unfold splitFrame at h
  split at h
  · simp at h
  · rename_i v r0 hdec
    have hbs := Varint.encodeDecode hdec
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i hcap _ hlen
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hl : (r0.take v.val).length = v.val := by simp; omega
    have hv : boundedVarint (r0.take v.val).length = v := by
      cases v; simp_all [boundedVarint, Nat.mod_eq_of_lt]
    rw [hv, List.append_assoc, List.take_append_drop]
    exact hbs.symm

/-- Entries that read back are exactly the encoding of the list. -/
theorem decodeEntriesInv (f : Nat) (bs : List Nat) (ids : List Core.ProtocolId)
    (h : decodeEntries f bs = .ok ids) : lsEntries ids ++ [10] = bs := by
  induction f generalizing bs ids with
  | zero => simp [decodeEntries] at h
  | succ f ih =>
    unfold decodeEntries at h
    split at h
    · rename_i hb
      simp only [Except.ok.injEq] at h
      subst h
      simp [lsEntries, hb]
    · split at h
      · simp at h
      · rename_i m rest hm
        cases hr : decodeEntries f rest with
        | error e => simp [hr, Except.map] at h
        | ok ids' =>
          simp [hr, Except.map] at h
          subst h
          have h1 := decodeMsgEncodeDecode bs m rest hm
          have h2 := ih rest ids' hr
          simp only [lsEntries, List.map_cons, List.flatten_cons, List.append_assoc] at h2 ⊢
          rw [h2]
          exact h1

/-- The all-input inverse of the `ls` reply: every accepted input is
the encoding of the decoded list. -/
theorem decodeLsInv {bs : List Nat} {ids : List Core.ProtocolId} {rest : List Nat}
    (h : decodeLs? bs = .ok (ids, rest)) : encodeLs ids ++ rest = bs := by
  unfold decodeLs? at h
  split at h
  · simp at h
  · rename_i body r hs
    cases he : decodeEntries body.length body with
    | error e => simp [he, Except.map] at h
    | ok ids' =>
      simp [he, Except.map] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb := decodeEntriesInv _ _ _ he
      have hs' := splitFrameInv hs
      unfold encodeLs lsBody
      rw [hb]
      exact hs'

end Libp2p.Negotiate
