import Bytes
import Multiformats.ComponentWire
import Multiformats.Multiaddr.Value

/-!
# Operations on component sequences

These functions preserve wire order and compare canonical components.
Composition returns raw component lists: the address boundary must
check its budget and ordering before constructing a validated address.
-/

set_option autoImplicit false

namespace Multiformats.SequenceOps

open ComponentWire (Frame)

/-- Appending retains duplicates and the order supplied by the caller. -/
def encapsulate (left right : List Frame) : List Frame := left ++ right

/-- Each tail is visited once; the remembered index is the most recent match. -/
private def scanLast (needle : List Frame) (index : Nat) (found : Option Nat) :
    List Frame → Option Nat
  | [] => if needle.isEmpty then some index else found
  | frames@(_ :: tail) =>
      let found := if needle.isPrefixOf frames then some index else found
      scanLast needle (index + 1) found tail

/-- A subaddress matches complete components, never bytes inside a payload. -/
def lastIndexOf (frames needle : List Frame) : Option Nat := scanLast needle 0 none frames

/-- Go leaves an absent subaddress unchanged; an empty result is its nil form. -/
def decapsulate? (frames needle : List Frame) : Option (List Frame) :=
  match lastIndexOf frames needle with
  | none => some frames
  | some index =>
      let kept := frames.take index
      if kept.isEmpty then none else some kept

/-- The JavaScript convention also treats an absent subaddress as a miss. -/
def decapsulateThrow? (frames needle : List Frame) : Option (List Frame) :=
  match lastIndexOf frames needle with
  | none => none
  | some _ => decapsulate? frames needle

/-- Remove the last matching protocol and every component after it. -/
def decapsulateCode (frames : List Frame) (code : Nat) : List Frame :=
  match frames.reverse.findIdx? (fun frame => frame.proto.toCode == code) with
  | none => frames
  | some index => frames.take (frames.length - 1 - index)

/-- Splitting produces component sequences; their later boundary remains checked. -/
def split (frames : List Frame) : List (List Frame) := frames.map (fun frame => [frame])

/-- Joining concatenates in the original order, without a normalization pass. -/
def join (addresses : List (List Frame)) : List Frame := addresses.flatten

/-- Splitting and joining cannot change a sequence's components or their order. -/
theorem joinSplit (frames : List Frame) : join (split frames) = frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih => simpa [join, split] using congrArg (frame :: ·) ih

/-- The protocol view reports canonical registry names. -/
def protocols (frames : List Frame) : List (Nat × String) :=
  frames.map (fun frame => (frame.proto.toCode, frame.proto.name))

/-- Go returns the first occurrence and the empty string for a valueless protocol. -/
def valueForProtocol? (frames : List Frame) (code : Nat) : Option String := do
  let frame ← frames.find? (fun frame => frame.proto.toCode == code)
  (Multiaddr.valueString? frame).toOption

/-- The component view carries decoded path text, as in the JavaScript API. -/
structure ComponentView where
  code : Nat
  name : String
  value : Option String
  deriving DecidableEq, Repr

/-- A Unix path drops its leading slash in the components view only. -/
def component (frame : Frame) : ComponentView :=
  let value := if frame.proto.fixedBytes? == some 0 then none
    else if frame.proto == .unix then do
      let text ← (Multiaddr.valueString? frame).toOption
      (Multiaddr.percentDecode? (String.ofList (text.toList.drop 1))).toOption
    else if frame.proto == .«http-path» then
      Bytes.toString? (Bytes.ofNatList frame.value)
    else (Multiaddr.valueString? frame).toOption
  ⟨frame.proto.toCode, frame.proto.name, value⟩

/-- The view retains one entry per component, including valueless protocols. -/
def components (frames : List Frame) : List ComponentView := frames.map component

/-- This helper parses protocol names only, not complete addresses with values. -/
def protocolsWithString? (text : String) : Option (List (Nat × String)) := do
  let chars := text.toList.dropWhile (· == '/')
  let body := String.ofList ((chars.reverse.dropWhile (· == '/')).reverse)
  if body.isEmpty then some []
  else
    (body.splitOn "/").mapM fun name => do
      let protocol ← Protocol.ofName? name
      some (protocol.toCode, protocol.name)

/-- Membership compares complete component sequences. -/
def contains (addresses : List (List Frame)) (address : List Frame) : Bool :=
  addresses.contains address

/-- Deduplication keeps the first appearance and the caller's ordering. -/
def unique (addresses : List (List Frame)) : List (List Frame) :=
  (addresses.foldl (fun reversed address =>
    if reversed.contains address then reversed else address :: reversed) []).reverse

/-- Filtering preserves the relative order of retained addresses. -/
def filter (addresses : List (List Frame)) (predicate : List Frame → Bool) : List (List Frame) :=
  addresses.filter predicate

end Multiformats.SequenceOps
