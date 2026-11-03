import Multiformats.Tables
import Multiformats.Constants
import Multiformats.Wire

/-!
# Component wire framing

This core owns protocol tags, fixed widths, variable lengths, and byte
budgets. Protocol-specific value validation and text presentation sit
above it. A frame contains only information that survives on the wire.
-/

set_option autoImplicit false

namespace Multiformats.ComponentWire

open Mock

/-- The raw framing invariant is independent of protocol-specific text rules. -/
def validValue (protocol : Protocol) (value : List Nat) : Prop :=
  (∀ b ∈ value, b < 256) ∧ value.length ≤ maxComponentBytes ∧
    match protocol.fixedBytes? with
    | none => True
    | some count => value.length = count

instance (protocol : Protocol) (value : List Nat) : Decidable (validValue protocol value) := by
  unfold validValue
  cases protocol.fixedBytes? <;> infer_instance

/-- The checked value carries its framing constraints through every consumer. -/
structure Frame where
  proto : Protocol
  value : List Nat
  valid : validValue proto value
  deriving DecidableEq, Repr

/-- A raw value enters the proved core only after its checks pass. -/
def ofValue? (protocol : Protocol) (value : List Nat) : Except Error Frame :=
  if h : validValue protocol value then .ok ⟨protocol, value, h⟩ else .error .badValue

/-- Fixed-width values need no redundant length prefix. -/
def encodeValue (protocol : Protocol) (value : List Nat) : List Nat :=
  match protocol.fixedBytes? with
  | some _ => value
  | none => Wire.encodeNat value.length ++ value

/-- A protocol tag identifies exactly one canonical registry member. -/
def encode (frame : Frame) : List Nat :=
  Wire.encodeNat frame.proto.toCode ++ encodeValue frame.proto frame.value

/-- Budget checks count framing bytes without materializing the payload again. -/
def encodedLength (frame : Frame) : Nat :=
  (Wire.encodeNat frame.proto.toCode).length +
    (match frame.proto.fixedBytes? with
     | some _ => 0
     | none => (Wire.encodeNat frame.value.length).length) + frame.value.length

/-- The budget calculation measures the exact emitted length. -/
theorem encodedLengthEq (frame : Frame) : encodedLength frame = (encode frame).length := by
  cases hs : frame.proto.fixedBytes? <;>
    simp [encodedLength, encode, encodeValue, hs, List.length_append, Nat.add_assoc]

/-- The production encoder writes a component into an existing byte builder. -/
def appendB (frame : Frame) (output : ByteArray) : ByteArray :=
  let output := Wire.writeNatB frame.proto.toCode output
  let output := match frame.proto.fixedBytes? with
    | some _ => output
    | none => Wire.writeNatB frame.value.length output
  Wire.writeBytesB frame.value output

/-- A standalone frame needs only an empty initial builder. -/
def toByteArray (frame : Frame) : ByteArray := appendB frame ByteArray.empty

/-- The declared width or length is checked before extracting a value. -/
def decodeValue? (protocol : Protocol) (input : List Nat) : Except Error (List Nat × List Nat) := do
  match protocol.fixedBytes? with
  | some count => Wire.takeBytes maxComponentBytes count input
  | none =>
      let (count, tail) ← (Varint.decode? input).mapError Error.framing
      Wire.takeBytes maxComponentBytes count.val tail

/-- Unknown tags and non-byte model entries are rejected at the boundary. -/
def decodeAt? (input : List Nat) : Except Error (Frame × List Nat) := do
  let (rawProtocol, tail) ← (Varint.decode? input).mapError Error.framing
  let protocol ← match Protocol.ofCode? rawProtocol.val with
    | none => .error .unknownProtocol
    | some protocol => .ok protocol
  if protocol.toCode = rawProtocol.val then
    let (value, rest) ← decodeValue? protocol tail
    let frame ← ofValue? protocol value
    .ok (frame, rest)
  else .error .unknownProtocol

/-- The component cap implies the varint length bound. -/
theorem valueLengthLt (frame : Frame) : frame.value.length < Varint.limit := by
  have h := frame.valid.2.1
  simp only [maxComponentBytes] at h
  simp only [Varint.limit]
  omega

/-- The payload rule composes with an arbitrary following frame. -/
theorem decodeValueEncode (frame : Frame) (rest : List Nat) :
    decodeValue? frame.proto (encodeValue frame.proto frame.value ++ rest) =
      .ok (frame.value, rest) := by
  have take := Wire.takeBytesAppend maxComponentBytes frame.value rest
    frame.valid.2.1 frame.valid.1
  cases hs : frame.proto.fixedBytes? with
  | none =>
      have hl := valueLengthLt frame
      simp [decodeValue?, encodeValue, hs, Wire.encodeNat, List.append_assoc,
        Varint.decodeEncodeSuffix, Wire.toVarint, Nat.mod_eq_of_lt hl,
        take, Bind.bind, Except.bind, Except.mapError]
  | some count =>
      have hlen : frame.value.length = count := by
        simpa only [hs] using frame.valid.2.2
      simpa only [decodeValue?, encodeValue, hs, hlen] using take

/-- Every valid component returns with its suffix untouched. -/
theorem decodeEncodeSuffix (frame : Frame) (rest : List Nat) :
    decodeAt? (encode frame ++ rest) = .ok (frame, rest) := by
  have hc : frame.proto.toCode < Varint.limit := Protocol.codeLt frame.proto
  have payload := decodeValueEncode frame rest
  simp only [encode, List.append_assoc, decodeAt?, Wire.encodeNat,
    Varint.decodeEncodeSuffix, Wire.toVarint, Nat.mod_eq_of_lt hc,
    Protocol.ofCodeToCode, Bind.bind, Except.bind, Except.mapError]
  simp only [ite_true, payload, ofValue?, dite_eq_left frame.valid]

/-- A successful value parse reconstructs exactly its consumed prefix. -/
theorem decodeValueOk (protocol : Protocol) (input value rest : List Nat)
    (h : decodeValue? protocol input = .ok (value, rest)) :
    input = encodeValue protocol value ++ rest := by
  cases hs : protocol.fixedBytes? with
  | some count =>
      simp only [decodeValue?, hs] at h
      have result := Wire.takeBytesOk maxComponentBytes count input value rest h
      simpa only [encodeValue, hs] using result.2.2.2
  | none =>
      cases hc : Varint.decode? input with
      | error error => simp [decodeValue?, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
      | ok pair =>
          obtain ⟨count, tail⟩ := pair
          simp only [decodeValue?, hs, hc, Except.mapError, Bind.bind, Except.bind] at h
          obtain ⟨hlen, _, _, split⟩ := Wire.takeBytesOk maxComponentBytes count.val tail value rest h
          have header := Varint.encodeDecode input count tail hc
          have all := header.trans (congrArg (Varint.encode count ++ ·) split)
          simpa only [encodeValue, hs, Wire.encodeNat, hlen, Wire.toVarintVal,
            List.append_assoc] using all

/-- Framing accepts no spelling that its encoder would change. -/
theorem encodeDecode (input : List Nat) (frame : Frame) (rest : List Nat)
    (h : decodeAt? input = .ok (frame, rest)) : input = encode frame ++ rest := by
  cases ht : Varint.decode? input with
  | error error => simp [decodeAt?, ht, Except.mapError, Bind.bind, Except.bind] at h
  | ok pair =>
      obtain ⟨rawProtocol, tail⟩ := pair
      simp only [decodeAt?, ht, Except.mapError, Bind.bind, Except.bind] at h
      cases hp : Protocol.ofCode? rawProtocol.val with
      | none => simp [hp] at h
      | some protocol =>
          simp only [hp] at h
          split at h
          · rename_i codeEq
            cases hv : decodeValue? protocol tail with
            | error error => simp [hv] at h
            | ok pair =>
                obtain ⟨value, after⟩ := pair
                simp only [hv] at h
                by_cases good : validValue protocol value
                · have hf : ofValue? protocol value = .ok ⟨protocol, value, good⟩ := by
                    simp only [ofValue?, dite_eq_left good]
                  simp only [hf] at h
                  have he := Prod.mk.inj (Except.ok.inj h)
                  rcases he with ⟨rfl, rfl⟩
                  have header := Varint.encodeDecode input rawProtocol tail ht
                  have payload := decodeValueOk protocol tail value after hv
                  simpa only [encode, Wire.encodeNat, codeEq, Wire.toVarintVal,
                    List.append_assoc] using
                    header.trans (congrArg (Varint.encode rawProtocol ++ ·) payload)
                · simp [ofValue?, good] at h
          · cases h

/-- Even a valueless protocol consumes at least its tag. -/
theorem encodeNonempty (frame : Frame) : encode frame ≠ [] := by
  intro h
  have hn := Varint.encodeNonempty (Wire.toVarint frame.proto.toCode)
  have hl := congrArg List.length h
  have hp : 0 < (Varint.encode (Wire.toVarint frame.proto.toCode)).length :=
    List.length_pos_iff.mpr hn
  simp only [encode, Wire.encodeNat, List.length_append, List.length_nil] at hl
  omega

/-- Both fixed and variable payloads preserve the model's byte bounds. -/
theorem encodeBytes (frame : Frame) : ∀ b ∈ encode frame, b < 256 := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact Varint.encodeBytes (Wire.toVarint frame.proto.toCode) b hb
  · cases hs : frame.proto.fixedBytes? with
    | some count =>
        have member : b ∈ frame.value := by simpa only [encodeValue, hs] using hb
        exact frame.valid.1 b member
    | none =>
        simp only [encodeValue, hs, List.mem_append] at hb
        rcases hb with hb | hb
        · exact Varint.encodeBytes (Wire.toVarint frame.value.length) b hb
        · exact frame.valid.1 b hb

/-- A component codec consumes one prefix, leaving the rest for the sequence reader. -/
instance : Bytes.Codec Frame where
  encode := encode
  decode? input := (decodeAt? input).mapError Error.toDecodeError

/-- The laws follow from the prefix theorems, with no component-specific axiom. -/
instance : Bytes.LawfulCodec Frame where
  decodeEncode frame := by
    have h := decodeEncodeSuffix frame []
    simp only [List.append_nil] at h
    change (decodeAt? (encode frame)).mapError Error.toDecodeError = _
    rw [h]
    rfl
  encodeDecode input frame rest h := by
    change (decodeAt? input).mapError Error.toDecodeError = .ok (frame, rest) at h
    cases hd : decodeAt? input with
    | error error => simp [hd, Except.mapError] at h
    | ok pair =>
        simp only [hd, Except.mapError, Except.ok.injEq] at h
        cases h
        exact (encodeDecode input frame rest hd).symm

/-- The independent cursor path uses the same documented widths and caps. -/
def decodeAtB? (input : ByteArray) (position : Nat := 0) : Except Error (Frame × Nat) := do
  let (rawProtocol, next) ← Wire.readVarintAt input position
  let protocol ← match Protocol.ofCode? rawProtocol.val with
    | none => .error .unknownProtocol
    | some protocol => .ok protocol
  let (value, after) ← match protocol.fixedBytes? with
    | some count => Wire.takeBytesAt input next count maxComponentBytes
    | none => do
        let (count, next) ← Wire.readVarintAt input next
        Wire.takeBytesAt input next count.val maxComponentBytes
  let frame ← ofValue? protocol value
  .ok (frame, after)

end Multiformats.ComponentWire
