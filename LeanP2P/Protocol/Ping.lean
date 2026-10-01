import LeanP2P.Conn.Stream
import LeanP2P.Crypto.PeerId
import LeanP2P.Crypto.Messages
import LeanP2P.Net.Multiaddr
import LeanP2P.Crypto.Bytes
/-!
# Ping protocol (VECTOR_TEST_PLAN.md, phase 3 step 20)

Per vendor/specs/ping/ping.md: the protocol id is `/ipfs/ping/1.0.0`; the
initiator sends 32 random bytes, the responder echoes them, and the
initiator measures the RTT. Any payload size ≠ 32 or a payload mismatch
aborts the ping.
-/

namespace LeanP2P.Ping

def protocol : String := "/ipfs/ping/1.0.0"

/-- The ping payload size (spec: 32 random bytes). -/
def payloadSize : Nat := 32

/-- Responder: accumulate bytes until `payloadSize` are available, echo
them, repeat until EOF. Real byte streams may split or coalesce writes. -/
partial def handle (s : Stream) : IO Unit := do
  let rec loop (acc : ByteArray) : IO Unit := do
    if acc.size >= payloadSize then do
      s.write (acc.extract 0 payloadSize)
      loop (acc.extract payloadSize acc.size)
    else do
      match ← s.read with
      | none => s.close
      | some chunk => loop (acc ++ chunk)
  loop ByteArray.empty

/-- Initiator: send a 32-byte random payload, await the echo, check it and
return the RTT in ms. -/
def ping (s : Stream) (payload : ByteArray) : IO (Option Nat) := do
  if payload.size != payloadSize then return none
  let t0 ← IO.monoMsNow
  s.write payload
  match ← s.read with
  | none => return none
  | some echo =>
    let t1 ← IO.monoMsNow
    if echo == payload then return some (t1 - t0) else return none

end LeanP2P.Ping
