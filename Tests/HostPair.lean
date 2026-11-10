import Conc
import Streams
import Libp2p.Identity
import Libp2p.Security
import Libp2p.Mux
import Libp2p.Host
import Multiformats.Multiaddr

/-!
# Two hosts over the sim

The protocol suites run their handlers between two real hosts, on the
test values of root §3.1 (PRINCIPLES 1.4): the in-memory sim transport,
the fixed-key Noise value with Ed25519 identities from one byte each,
and a test clock. The muxer is yamux. The server listens on
`/memory/4100`, and the client holds a session to it.
-/

set_option autoImplicit false

namespace Tests.HostPair

open Conc (Async Clock OnceRef TestClock)
open Libp2p.Host (Host Failure)

/-- A host on `net` and `clock`: the fixed-key Noise value with an
Ed25519 identity from one byte, yamux, and the sim transport. The
ephemeral keys come from an `Rng` seeded with 32 copies of
`idByte + 50`. Its failures go to `failures`. -/
def mkHost (net : Streams.Sim.Net) (clock : Clock) (idByte : UInt8)
    (failures : OnceRef (List Failure)) : Async Host := do
  let .ok identity := Libp2p.Identity.PrivKey.ofData? .ed25519 ⟨Array.replicate 32 idByte⟩
    | throw (IO.userError "test identity does not build")
  let some static := Libp2p.Security.Noise.Bytes32.ofByteArray? ⟨Array.replicate 32 (idByte + 100)⟩
    | throw (IO.userError "test static key is not 32 bytes")
  let noise := Libp2p.Security.Noise.fixedKeyProtocol { identity, static }
    ⟨Array.replicate 32 (idByte + 50)⟩
  match ← (Host.new {
      identity
      transports := [net.transport]
      security := [noise]
      muxers := [Libp2p.Mux.yamux]
      clock
      onFailure := fun f => failures.update (f :: ·) } : BaseIO _) with
  | .ok h => return h
  | .error _ => throw (IO.userError "test host does not build")

/-- Two hosts over a new sim net: the server listens, and the client
holds a session to it. -/
structure Pair where
  client : Host
  server : Host
  /-- The peer id the client proved for the server. -/
  serverPeer : Libp2p.Identity.PeerId
  /-- The address the server listens on. -/
  serverAddr : Multiformats.Multiaddr
  /-- The failures of the server's owned tasks, newest first. -/
  failures : OnceRef (List Failure)
  /-- The test clock both hosts run on. `Pair.close` closes it. -/
  clock : TestClock

/-- The pair. With `split`, the sim delivers each byte as its own read. -/
def hostPair (split : Bool := false) : Async Pair := do
  let net ← Streams.Sim.Net.new split
  let tc ← TestClock.new
  let failures ← OnceRef.new []
  let client ← mkHost net tc.clock 1 (← OnceRef.new [])
  let server ← mkHost net tc.clock 2 failures
  let addr ← match Multiformats.Multiaddr.parse? "/memory/4100" with
    | .ok a => pure a
    | .error _ => throw (IO.userError "test address")
  let .ok bound ← server.startListening addr | throw (IO.userError "listen failed")
  let .ok serverPeer ← client.dial bound | throw (IO.userError "dial failed")
  return { client, server, serverPeer, serverAddr := bound, failures, clock := tc }

/-- Close both hosts, then the clock. Each close joins its own tasks
(§5.5). -/
def Pair.close (p : Pair) : Async Unit := do
  p.client.close
  p.server.close
  p.clock.close

end Tests.HostPair
