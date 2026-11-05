import Multiformats.Multiaddr.Core
import Lean.Data.Json

/-!
# Address text and presentation

`Multiaddr` stores canonical wire values. `Text` also remembers the
parsed segments, so CID-form peer text survives normalization. Only
the canonical value has a `Codec` instance: binary decoding cannot
recover a spelling that the wire format does not carry.
-/

set_option autoImplicit false

namespace Multiformats.Multiaddr

/-- A parsed text view keeps its spelling tied to the checked wire components. -/
structure Text where
  address : Multiaddr
  segments : List Segment
  valid : segments.mapM segmentFrame? = .ok address.frames
  deriving DecidableEq, Repr

/-- Parse once, then retain both the canonical value and its original text segments. -/
def parseText? (text : String) : Except Error Text := do
  let segments ← parseSegments? text
  match converted : segments.mapM segmentFrame? with
  | .error error => .error error
  | .ok frames =>
      if valid : acceptFrames frames = true then
        .ok ⟨⟨⟨frames, valid⟩⟩, segments, converted⟩
      else .error .badAddress

/-- Transport callers receive the canonical value directly. -/
def parse? (text : String) : Except Error Multiaddr := Text.address <$> parseText? text

/-- Text normalization keeps CID-form peer ids and canonicalizes other components. -/
def Text.toString (text : Text) : String :=
  if text.address.frames.isEmpty then "/"
  else String.join ((text.address.frames.attach.zip text.segments).map fun (frame, segment) =>
    let original := segment.text.getD ""
    if frame.val.proto == .p2p && !original.startsWith "Qm" && !original.startsWith "1" then
      "/p2p/" ++ original
    else frameText frame.val (frameValid text.address frame.val frame.property))

instance : ToString Text := ⟨Text.toString⟩

/-- JSON uses the standard string encoder, including escaping. -/
def toJSON (address : Multiaddr) : String := (Lean.Json.str address.toString).compress

/-- A JSON address must be a string accepted by the strict text parser. -/
def ofJSON? (input : String) : Except Error Multiaddr := do
  if input.utf8ByteSize > maxAddressJsonBytes then .error .overCap
  else
    let value ← (Lean.Json.parse input).mapError (fun _ => Error.badAddress)
    let text ← value.getStr?.mapError (fun _ => Error.badAddress)
    parse? text

end Multiformats.Multiaddr
