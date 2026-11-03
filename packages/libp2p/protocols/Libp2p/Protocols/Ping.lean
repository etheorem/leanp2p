import Libp2p.Protocols.Constants

/-!
# Ping

The pure half of `/ipfs/ping/1.0.0`: the protocol id, the payload
size, and the echo check. The IO handler and the initiator are
sub-unit 1b.

Per `vendor/specs/ping/ping.md`: the initiator sends 32 random
bytes, and the responder echoes them. A payload of another size, or
an echo that differs from the sent payload, is a protocol error.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Ping

/-- The ping protocol id. -/
def protocolId : Mock.Core.ProtocolId := Constants.pingId

/-- The ping payload size of the spec. -/
def payloadSize : Nat := Constants.pingSize

/-- The failures of the pure echo check. The IO arm (a partial
payload at end of stream) joins it in sub-unit 1b. -/
inductive Error where
  | wrongSize (got : Nat)
  | mismatch
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

end Libp2p.Protocols.Ping
