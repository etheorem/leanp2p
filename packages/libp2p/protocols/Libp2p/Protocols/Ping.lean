import Bytes
import Conc
import Streams
import Libp2p.Protocols.Mock.Core
import Libp2p.Protocols.Constants

/-!
# Ping

The pure half of `/ipfs/ping/1.0.0`: the protocol id, the payload
size, and the echo check. Sub-unit 1b adds the IO half: the echo
handler, the initiator, and the theorems P5 and P6.

Per `vendor/specs/ping/ping.md`: the initiator sends 32 random
bytes, and the responder echoes them. A payload of another size, or
an echo that differs from the sent payload, is a protocol error.

The private echo loop `echoLoop` and the initiator's `awaitEcho` are
`partial def`s: the peer may stay silent, and no measure shows that a
read returns. A partial payload at the end of the stream is
`.truncated`, a recorded delta from the spike's responder, which
closes silently.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Ping

/-- The ping protocol id. -/
def protocolId : Mock.Core.ProtocolId := Constants.pingId

/-- The ping payload size of the spec. -/
def payloadSize : Nat := Constants.pingSize

/-- The failures of the pure echo check, plus the IO arms of 1b:
`truncated` (a partial payload at end of stream) and `stream` (a
stream fault). -/
inductive Error where
  | wrongSize (got : Nat)
  | mismatch
  /-- The stream ended with a partial payload, a recorded delta from
  the spike's responder. -/
  | truncated
  /-- The stream answered a fault. -/
  | stream (e : Streams.Error)
  deriving DecidableEq, BEq, Repr

/-- Check one echo: 32 bytes, equal to the sent payload. -/
def checkEcho (sent echo : List Nat) : Except Error Unit :=
  if echo.length ≠ payloadSize then .error (.wrongSize echo.length)
  else if echo ≠ sent then .error .mismatch
  else .ok ()

/-- P1: an exact echo of a 32-byte payload passes. -/
theorem checkEchoAccepts (sent : List Nat) (h : sent.length = payloadSize) :
    checkEcho sent sent = .ok () := by
  simp [checkEcho, h]

/-- P2: another size fails before the comparison. -/
theorem checkEchoWrongSize (sent echo : List Nat) (h : echo.length ≠ payloadSize) :
    checkEcho sent echo = .error (.wrongSize echo.length) := by
  simp [checkEcho, h]

/-- P3: a same-size echo that differs fails. -/
theorem checkEchoMismatch (sent echo : List Nat) (hlen : echo.length = payloadSize)
    (hne : echo ≠ sent) : checkEcho sent echo = .error .mismatch := by
  simp [checkEcho, hlen, hne]

/-- P4: a passing echo is the sent payload, of the spec size. -/
theorem checkEchoSound (sent echo : List Nat) (h : checkEcho sent echo = .ok ()) :
    echo = sent ∧ sent.length = payloadSize := by
  by_cases hlen : echo.length = payloadSize
  · by_cases hne : echo ≠ sent
    · simp [checkEcho, hlen, hne] at h
    · have heq : echo = sent := by simpa using hne
      exact ⟨heq, heq ▸ hlen⟩
  · simp [checkEcho, hlen] at h

/-! ## The echo handler and the initiator (sub-unit 1b) -/

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

/-- P6: an accumulator below the payload size holds no whole
payload. -/
theorem splitPayloadsShort (acc : List Nat) (h : acc.length < payloadSize) :
    splitPayloads acc = ([], acc) := by
  rw [splitPayloads]
  rw [ite_eq_right (by omega : ¬ payloadSize ≤ acc.length)]

/-- P5: the splitter takes one whole payload from the front and keeps
the tail. -/
theorem splitPayloadsWhole (sent tail : List Nat)
    (h : sent.length = payloadSize) (ht : tail.length < payloadSize) :
    splitPayloads (sent ++ tail) = ([sent], tail) := by
  have hcond : payloadSize ≤ (sent ++ tail).length := by
    simp [List.length_append, h]
  rw [splitPayloads]
  rw [ite_eq_left hcond, List.take_left' h, List.drop_left' h,
      splitPayloadsShort tail ht]

/-- Write every whole payload, in order. Structural: the list
shrinks. -/
private def writeAll (s : Streams.Stream) :
    List (List Nat) → Conc.Async (Except Error Unit)
  | [] => return .ok ()
  | p :: ps => do
      match ← s.write (Bytes.ofNatList p) with
      | .error e => return .error (.stream e)
      | .ok () => writeAll s ps

/-- The echo loop. `partial`: the peer may stay silent, and no measure
shows a read returns; the module doc records the reason. -/
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
    handle := fun s => ExceptT.mk ((Except.mapError mapPingError) <$> handleCore s) }

/-- Accumulate echo chunks until one whole payload is present.
`partial`: the peer may stay silent; the module doc records the
reason. -/
private partial def awaitEcho (s : Streams.Stream) (acc : List Nat) :
    Conc.Async (Except Error (List Nat)) := do
  match splitPayloads acc with
  | (p :: _, _) => return .ok p
  | ([], _) =>
      match ← s.read with
      | .error e => return .error (.stream e)
      | .ok none => return .error .truncated
      | .ok (some chunk) => awaitEcho s (acc ++ Bytes.toNatList chunk)

/-- Send one 32-byte payload, await the echo, check it with the 1a
`checkEcho`, and return the round-trip time in milliseconds. `.ok
none` never occurs on the echo path; the option carries the measured
time. -/
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
