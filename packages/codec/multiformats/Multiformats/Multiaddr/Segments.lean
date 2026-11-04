import Multiformats.Multiaddr.Value

/-!
# Address text segments

Separating segmentation from value conversion keeps the original peer
text available to the presentation layer. Unix consumes the remaining
path verbatim; other valued protocols consume exactly one segment.
-/

set_option autoImplicit false

namespace Multiformats.Multiaddr

/-- A valueless protocol has no text field; a valued protocol keeps its spelling. -/
structure Segment where
  proto : Protocol
  text : Option String
  deriving DecidableEq, Repr

/-- The accumulator keeps long component sequences on the tail-recursive path. -/
private def segments (reversed : List Segment) : List String → Except Error (List Segment)
  | [] => .ok reversed.reverse
  | name :: tail => do
      let protocol ← match Protocol.ofName? name with
        | some protocol => .ok protocol
        | none => .error .unknownProtocol
      if protocol == .unix then
        if tail.isEmpty then .error .badValue
        else .ok (reversed.reverse ++ [⟨protocol, some ("/" ++ String.intercalate "/" tail)⟩])
      else if protocol.fixedBytes? == some 0 then
        segments (⟨protocol, none⟩ :: reversed) tail
      else
        match tail with
        | [] => .error .badValue
        | value :: rest =>
            if value.isEmpty then .error .badValue
            else segments (⟨protocol, some value⟩ :: reversed) rest

/-- One optional trailing separator is tolerated; empty interior segments fail. -/
def parseSegments? (text : String) : Except Error (List Segment) := do
  if text.utf8ByteSize > maxAddressBytes then .error .overCap
  else
    match text.toList with
    | '/' :: chars =>
        let chars := if chars.getLast? == some '/' then chars.dropLast else chars
        if chars.isEmpty then .error .badAddress else segments [] ((String.ofList chars).splitOn "/")
    | _ => .error .badAddress

/-- Converting segments does not discard the caller's separate text view. -/
def segmentFrame? (segment : Segment) : Except Error ComponentWire.Frame :=
  parseValue? segment.proto (segment.text.getD "")

/-- A zone needs its IPv6 address; a Unix path terminates the sequence. -/
def validOrder : List ComponentWire.Frame → Bool
  | [] => true
  | frame :: rest =>
      if frame.proto == .unix then rest.isEmpty
      else if frame.proto == .ip6zone then
        (rest.head?.map (·.proto) == some .ip6) && validOrder rest
      else validOrder rest

end Multiformats.Multiaddr
