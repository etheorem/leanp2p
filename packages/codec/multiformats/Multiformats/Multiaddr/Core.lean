import Multiformats.SequenceWire
import Multiformats.Multiaddr.Segments

/-!
# Canonical multiaddrs

An address stores only information present in its wire encoding. Parsed
peer-text presentation lives in `Multiaddr.Text`; it is not part of the
value covered by the exact `LawfulCodec` roundtrip. Construction checks
component semantics, path ordering and the complete address budget.
-/

set_option autoImplicit false

namespace Multiformats

/-- The raw component surface used by address constructors and transport seams. -/
structure Component where
  proto : Protocol
  value : List Nat
  deriving DecidableEq, Repr, Hashable

namespace Multiaddr

/-- Acceptance adds protocol semantics and a whole-address budget to checked framing. -/
def acceptFrames (frames : List ComponentWire.Frame) : Bool :=
  (frames.all validFrame && validOrder frames) &&
    decide ((frames.map ComponentWire.encodedLength).sum ≤ maxAddressBytes)

end Multiaddr

/-- A canonical wire value; the sequence carries its complete validity check. -/
structure Multiaddr where
  wire : SequenceWire.Value Multiaddr.acceptFrames
  deriving DecidableEq, Repr

namespace Multiaddr

/-- Proof-carrying frames stay internal to the binary core. -/
def frames (address : Multiaddr) : List ComponentWire.Frame := address.wire.frames

/-- Callers see the protocol and raw value bytes in wire order. -/
def components (address : Multiaddr) : List Component :=
  address.frames.map fun frame => ⟨frame.proto, frame.value⟩

/-- Each stored component passed the semantic check at construction. -/
theorem frameValid (address : Multiaddr) (frame : ComponentWire.Frame)
    (member : frame ∈ address.frames) : validFrame frame = true :=
  List.all_eq_true.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp address.wire.valid).1).1 frame member

/-- A checked component has a total text representation. -/
def frameText (frame : ComponentWire.Frame) (valid : validFrame frame = true) : String :=
  let value := valueString frame valid
  if frame.proto == .unix then "/unix" ++ value
  else if frame.proto.fixedBytes? == some 0 then "/" ++ frame.proto.name
  else "/" ++ frame.proto.name ++ "/" ++ value

/-- Canonical text uses the bare base58 peer id; the empty binary value prints `/`. -/
def toString (address : Multiaddr) : String :=
  if address.frames.isEmpty then "/"
  else String.join (address.frames.attach.map fun frame =>
    frameText frame.val (frameValid address frame.val frame.property))

instance : ToString Multiaddr := ⟨toString⟩

/-- Transport diagnostics use the same canonical text as other callers. -/
def describe (address : Multiaddr) : String := toString address

/-- Empty binary addresses are valid even though empty text is rejected. -/
def empty : Multiaddr := ⟨⟨[], rfl⟩⟩

/-- Already framed values still pass the whole-address checks at construction. -/
def ofFrames? (frames : List ComponentWire.Frame) : Except Error Multiaddr :=
  if h : acceptFrames frames = true then .ok ⟨⟨frames, h⟩⟩ else .error .badAddress

/-- Raw components first acquire their framing proofs, then their address proof. -/
def fromComponents? (components : List Component) : Except Error Multiaddr := do
  let frames ← components.mapM fun component =>
    ComponentWire.ofValue? component.proto component.value
  ofFrames? frames

/-- The optional constructor matches the transport seam's checked construction API. -/
def ofComponents? (components : List Component) : Option Multiaddr :=
  (fromComponents? components).toOption

/-- A predicate view is useful at callers that only need acceptance. -/
def check (components : List Component) : Bool := (ofComponents? components).isSome

/-- Encoding reuses the proved ordered sequence model. -/
def encode (address : Multiaddr) : List Nat := SequenceWire.encode address.wire

/-- The stored budget is exactly the length of the encoded wire value. -/
theorem encodeLengthLe (address : Multiaddr) : (encode address).length ≤ maxAddressBytes := by
  have budget := (Bool.and_eq_true_iff.mp address.wire.valid).2
  have bound := of_decide_eq_true budget
  simpa only [encode, SequenceWire.encode, ← SequenceWire.encodeFramesLength] using bound

/-- The model rejects an over-budget complete message before decoding components. -/
def decode? (input : List Nat) : Except Error (Multiaddr × List Nat) := do
  if input.length > maxAddressBytes then .error .overCap
  else
    let (wire, rest) ← SequenceWire.decode? acceptFrames input
    .ok (⟨wire⟩, rest)

/-- Every address, including empty and repeated-protocol values, roundtrips exactly. -/
theorem decodeEncode (address : Multiaddr) : decode? (encode address) = .ok (address, []) := by
  have budget : ¬ (encode address).length > maxAddressBytes := by
    have h := encodeLengthLe address
    omega
  unfold decode?
  rw [ite_eq_right budget]
  simp only [encode, SequenceWire.decodeEncode, Bind.bind, Except.bind]

/-- Accepted buffers retain every consumed byte and their returned remainder. -/
theorem encodeDecode (input : List Nat) (address : Multiaddr) (rest : List Nat)
    (h : decode? input = .ok (address, rest)) : input = encode address ++ rest := by
  simp only [decode?] at h
  split at h
  · cases h
  · cases hw : SequenceWire.decode? acceptFrames input with
    | error error => simp [hw, Bind.bind, Except.bind] at h
    | ok pair =>
        obtain ⟨wire, tail⟩ := pair
        simp only [hw, Bind.bind, Except.bind] at h
        cases h
        exact SequenceWire.encodeDecode acceptFrames input wire rest hw

/-- Canonical wire identity is injective over complete ordered address values. -/
theorem encodeInjective (left right : Multiaddr) (same : encode left = encode right) :
    left = right := by
  have hl := decodeEncode left
  have hr := decodeEncode right
  rw [same, hr] at hl
  exact (Prod.mk.inj (Except.ok.inj hl)).1.symm

/-- The model never writes an entry outside the byte domain. -/
theorem encodeBytes (address : Multiaddr) : ∀ b ∈ encode address, b < 256 :=
  SequenceWire.encodeFramesBytes address.frames

/-- The public address type owns its model codec instance. -/
instance : Bytes.Codec Multiaddr where
  encode := encode
  decode? input := (decode? input).mapError Error.toDecodeError

/-- These are exact equality laws on the canonical value, without presentation metadata. -/
instance : Bytes.LawfulCodec Multiaddr where
  decodeEncode address := by
    change (decode? (encode address)).mapError Error.toDecodeError = _
    rw [decodeEncode]
    rfl
  encodeDecode input address rest h := by
    change (decode? input).mapError Error.toDecodeError = .ok (address, rest) at h
    cases hd : decode? input with
    | error error => simp [hd, Except.mapError] at h
    | ok pair =>
        simp only [hd, Except.mapError, Except.ok.injEq] at h
        cases h
        exact (encodeDecode input address rest hd).symm

/-- Hashing canonical bytes makes wire-equal addresses share their hash. -/
instance : Hashable Multiaddr where
  hash address := hash (encode address)

/-- Ordering uses canonical bytes, independently of the registry source's row order. -/
instance : Ord Multiaddr where
  compare left right := compare (encode left) (encode right)

example (address : Multiaddr) :
    Bytes.Codec.decode? (Bytes.Codec.encode address) = .ok (address, []) :=
  Bytes.codecRoundTrip address

end Multiaddr

end Multiformats
