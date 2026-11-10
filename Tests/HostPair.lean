import Conc
import Streams
import Libp2p.Identity
import Libp2p.Security
import Libp2p.Mux
import Libp2p.Host
import Multiformats.Multiaddr

/-!
# Two hosts over the sim

The protocol suites run their handlers between two real hosts: Noise
with Ed25519 identities from one byte each, yamux, and the in-memory
sim transport (CLAUDE.md, "Dependency Inversion"). The server listens
on `/memory/4100`, and the client holds a session to it.
-/

set_option autoImplicit false

namespace Tests.HostPair

open Conc (Async OnceRef)
open Libp2p.Host (Host Failure)

/-- A host on `net`: Noise with an Ed25519 identity from one byte, yamux,
and the sim transport. Its failures go to `failures`. -/
def mkHost (net : Streams.Sim.Net) (idByte : UInt8) (failures : OnceRef (List Failure)) :
    Async Host := do
  let .ok identity := Libp2p.Identity.PrivKey.ofData? .ed25519 ⟨Array.replicate 32 idByte⟩
    | throw (IO.userError "test identity does not build")
  let some static := Libp2p.Security.Noise.Bytes32.ofByteArray? ⟨Array.replicate 32 (idByte + 100)⟩
    | throw (IO.userError "test static key is not 32 bytes")
  match ← (Host.new {
      identity
      transports := [net.transport]
      security := [Libp2p.Security.Noise.securityProtocol { identity, static }]
      muxers := [Libp2p.Mux.yamux]
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

/-- The pair. With `split`, the sim delivers each byte as its own read. -/
def hostPair (split : Bool := false) : Async Pair := do
  let net ← Streams.Sim.Net.new split
  let failures ← OnceRef.new []
  let client ← mkHost net 1 (← OnceRef.new [])
  let server ← mkHost net 2 failures
  let addr ← match Multiformats.Multiaddr.parse? "/memory/4100" with
    | .ok a => pure a
    | .error _ => throw (IO.userError "test address")
  let .ok bound ← server.startListening addr | throw (IO.userError "listen failed")
  let .ok serverPeer ← client.dial bound | throw (IO.userError "dial failed")
  return { client, server, serverPeer, serverAddr := bound, failures }

/-- Close both hosts. Each close joins its own tasks (§5.5). -/
def Pair.close (p : Pair) : Async Unit := do
  p.client.close
  p.server.close

end Tests.HostPair
