import Bytes
import Conc
import Streams.Error
import Streams.Stream
import Libp2p.Protocols.Mock.Core
import Libp2p.Protocols.Constants

/-!
# Ping

The pure half of `/ipfs/ping/1.0.0`: the protocol id, the payload
size, and the echo check. The IO half: the echo handler and the
initiator, which share the pure `splitPayloads` and its theorems.

Per `vendor/specs/ping/ping.md`: the initiator sends 32 random
bytes, and the responder echoes them. In this package, the initiator
treats an echo of another size or other bytes as a protocol error.

The private echo loop `echoLoop` and the initiator's `awaitEcho` are
`partial def`s: the peer may stay silent, and no measure shows that a
read returns. A stream that ends before one whole payload arrives is
`.truncated`.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Ping

/-- The ping protocol id. -/
def protocolId : Mock.Core.ProtocolId := Constants.pingId

/-- The ping payload size of the spec. -/
def payloadSize : Nat := Constants.pingSize

/-- The failures of the pure echo check, plus the IO arms: `truncated`
(a partial payload at end of stream) and `stream` (a stream fault). -/
inductive Error where
  | wrongSize (got : Nat)
  | mismatch
  /-- The stream ended before one whole payload arrived. -/
  | truncated
  /-- The stream returned an error. -/
  | stream (e : Streams.Error)
  deriving DecidableEq, BEq, Repr

/-- Check one echo: 32 bytes, equal to the sent payload. -/
def checkEcho (sent echo : List Nat) : Except Error Unit :=
  if echo.length ≠ payloadSize then .error (.wrongSize echo.length)
  else if echo ≠ sent then .error .mismatch
  else .ok ()

/-- An exact echo of a 32-byte payload passes. -/
theorem checkEchoAccepts (sent : List Nat) (h : sent.length = payloadSize) :
    checkEcho sent sent = .ok () := by
  simp [checkEcho, h]

/-- Another size fails before the comparison. -/
theorem checkEchoWrongSize (sent echo : List Nat) (h : echo.length ≠ payloadSize) :
    checkEcho sent echo = .error (.wrongSize echo.length) := by
  simp [checkEcho, h]

/-- A same-size echo that differs fails. -/
theorem checkEchoMismatch (sent echo : List Nat) (hlen : echo.length = payloadSize)
    (hne : echo ≠ sent) : checkEcho sent echo = .error .mismatch := by
  simp [checkEcho, hlen, hne]

/-- A passing echo is the sent payload, of the spec size. -/
theorem checkEchoSound (sent echo : List Nat) (h : checkEcho sent echo = .ok ()) :
    echo = sent ∧ sent.length = payloadSize := by
  by_cases hlen : echo.length = payloadSize
  · by_cases hne : echo ≠ sent
    · simp [checkEcho, hlen, hne] at h
    · have heq : echo = sent := by simpa using hne
      exact ⟨heq, heq ▸ hlen⟩
  · simp [checkEcho, hlen] at h

/-! ## The echo handler and the initiator -/

/-- Split the accumulated bytes into whole 32-byte payloads and the
tail. The echo handler writes every whole payload; the tail waits for
more bytes. -/
def splitPayloads (acc : List Nat) : List (List Nat) × List Nat :=
  if payloadSize ≤ acc.length then
    let (rest, tail) := splitPayloads (acc.drop payloadSize)
    (acc.take payloadSize :: rest, tail)
  else ([], acc)
termination_by acc.length
decreasing_by
  simp only [List.length_drop]
  have hp : payloadSize = 32 := rfl
  omega

/-- An accumulator below the payload size holds no whole
payload. -/
theorem splitPayloadsShort (acc : List Nat) (h : acc.length < payloadSize) :
    splitPayloads acc = ([], acc) := by
  rw [splitPayloads]
  rw [ite_eq_right (by omega : ¬ payloadSize ≤ acc.length)]

/-- The splitter takes one whole payload from the front and keeps
the tail. -/
theorem splitPayloadsWhole (sent tail : List Nat)
    (h : sent.length = payloadSize) (ht : tail.length < payloadSize) :
    splitPayloads (sent ++ tail) = ([sent], tail) := by
  have hcond : payloadSize ≤ (sent ++ tail).length := by
    simp [List.length_append, h]
  rw [splitPayloads]
  rw [ite_eq_left hcond, List.take_left' h, List.drop_left' h,
      splitPayloadsShort tail ht]

/-- Write every whole payload, in order, as one stream write. A write
waits until the muxer has sent its frame, so a write per payload would
cost one round trip through the muxer and the secure connection per
32 bytes. The echoes are a byte stream, and the initiator reads them as
one (the module doc), so one write changes nothing on the wire but the
framing. -/
private def writeAll (s : Streams.Stream) (whole : List (List Nat)) :
    Conc.Async (Except Error Unit) := do
  if whole.isEmpty then return .ok ()
  match ← s.write (Bytes.ofNatList whole.flatten) with
  | .error e => return .error (.stream e)
  | .ok () => return .ok ()

/-- The echo loop. The module doc gives the reason for `partial`. -/
private partial def echoLoop (s : Streams.Stream) (acc : List Nat) :
    Conc.Async (Except Error Unit) := do
  match ← s.read with
  | .error e => return .error (.stream e)
  | .ok none =>
      if acc.isEmpty then return .ok () else return .error .truncated
  | .ok (some chunk) =>
      let (whole, tail) := splitPayloads (acc ++ Bytes.toNatList chunk)
      match ← writeAll s whole with
      | .error e => return .error e
      | .ok () => echoLoop s tail

/-- The echo handler: write back every whole payload, until the stream
closes. A partial payload at the close is a protocol error. -/
def handleCore (s : Streams.Stream) : Conc.Async (Except Error Unit) :=
  echoLoop s []

/-- One map from this protocol's error into the coarse core error,
used once, at the seam value. -/
def mapPingError : Error → Mock.Core.Error
  | .stream e => Mock.Core.mapStreamError e
  | e => .protocol (toString (repr e))

/-- The ping handler value. -/
def pingHandler : Mock.Core.StreamHandler :=
  { id := protocolId,
    handle := fun _ctx s => ExceptT.mk ((Except.mapError mapPingError) <$> handleCore s) }

/-- Accumulate echo chunks until one whole payload is present. The
initiator reads one 32-byte payload, so an accumulator above that size
is an oversized echo. The module doc gives the reason for `partial`. -/
private partial def awaitEcho (s : Streams.Stream) (acc : List Nat) :
    Conc.Async (Except Error (List Nat)) := do
  match splitPayloads acc with
  | (p :: _, _) =>
      if acc.length = payloadSize then return .ok p
      else return .error (.wrongSize acc.length)
  | ([], _) =>
      match ← s.read with
      | .error e => return .error (.stream e)
      | .ok none => return .error .truncated
      | .ok (some chunk) => awaitEcho s (acc ++ Bytes.toNatList chunk)

/-- Send one 32-byte payload, await the echo, check it with
`checkEcho`, and return the round-trip time in milliseconds inside
`some`. The echo path never returns `.ok none`. -/
def ping (s : Streams.Stream) (clock : Conc.Clock) (payload : ByteArray) :
    Conc.Async (Except Error (Option Nat)) := do
  if payload.size ≠ payloadSize then return .error (.wrongSize payload.size)
  let t0 ← clock.nowMs
  match ← s.write payload with
  | .error e => return .error (.stream e)
  | .ok () =>
      match ← awaitEcho s [] with
      | .error e => return .error e
      | .ok echo =>
          match checkEcho (Bytes.toNatList payload) echo with
          | .error e => return .error e
          | .ok () =>
              let t1 ← clock.nowMs
              return .ok (some (t1 - t0))

end Libp2p.Protocols.Ping
