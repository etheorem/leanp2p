import Bytes
import Yamux.Constants
import Yamux.Error
import Yamux.Header

/-!
# Yamux frames

A frame is the 12-byte header plus, for a data frame, its payload
(ARCHITECTURE §4.8). A window update, a ping, and a `GoAway` carry their
value in the header's length field and no payload at all.

`parse?` is the streaming boundary: it answers `none` while the buffer
cannot complete a frame, so the reader keeps waiting, and answers an
error when the bytes already present violate the specification. A short
input is never an error (ARCHITECTURE §3.5).
-/

namespace Yamux

/-- One yamux unit on the wire. -/
structure Frame where
  /-- The frame header. -/
  header : Header
  /-- The data payload of a data frame, and nothing for a control frame. -/
  payload : List Nat
  deriving Repr, DecidableEq, BEq, Hashable

namespace Frame

/-- The frames the encoder produces: a data frame carries exactly the
bytes its header declares, within the frame cap, and a control frame
carries no payload. -/
def WellFormed (f : Frame) : Prop :=
  match f.header.frameType with
  | .data => f.payload.length = f.header.length.val ∧ f.header.length.val ≤ maxDataFrame
  | _ => f.payload = []

/-- The wire bytes of a frame. -/
def encode (f : Frame) : List Nat := Header.encode f.header ++ f.payload

/-- Read one frame off the front of a buffer. -/
def parse? (bs : List Nat) : Except ProtocolError (Option (Frame × List Nat)) :=
  match Header.decode? bs with
  | .error .truncated => .ok none
  | .error .malformed => .error .header
  | .ok (h, rest) =>
      match h.frameType with
      | .data =>
          if h.length.val > maxDataFrame then .error .overlongData
          else if h.length.val > rest.length then .ok none
          else
            .ok (some ({ header := h, payload := rest.take h.length.val },
              rest.drop h.length.val))
      | _ => .ok (some ({ header := h, payload := [] }, rest))

/-! ## The parser laws -/

/-- A data frame whose payload matches its header parses back, and
consumes every one of its bytes. -/
theorem parse?_encode_data {f : Frame} (ht : f.header.frameType = .data)
    (hlen : f.payload.length = f.header.length.val)
    (hcap : f.header.length.val ≤ maxDataFrame) :
    parse? (encode f) = .ok (some (f, [])) := by
  unfold parse? encode
  rw [Header.decode?_encode_append]
  dsimp only
  rw [ht]
  have hcap' : ¬ f.header.length.val > maxDataFrame := by omega
  have hlen' : ¬ f.header.length.val > f.payload.length := by omega
  simp only [hcap', hlen', ite_false]
  rw [← hlen, List.take_length, List.drop_length]

/-- A control frame with no payload parses back, and consumes its twelve
bytes. -/
theorem parse?_encode_control {f : Frame} (ht : f.header.frameType ≠ .data)
    (hp : f.payload = []) :
    parse? (encode f) = .ok (some (f, [])) := by
  unfold parse? encode
  rw [Header.decode?_encode_append]
  dsimp only
  cases h : f.header.frameType
  · exact absurd h ht
  · rw [← hp]
  · rw [← hp]
  · rw [← hp]

end Frame

end Yamux