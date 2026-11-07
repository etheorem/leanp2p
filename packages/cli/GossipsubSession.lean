import Conc
import Streams
import Libp2p.Core
import Libp2p.Host
import Libp2p.Mux
import Libp2p.Security.Noise
import Libp2p.Protocols.Gossipsub.HostSeam
import Libp2p.Protocols.Gossipsub.Node
import Libp2p.Protocols.Identify

/-! Real socket participant wiring. This module owns host assembly only. -/
set_option autoImplicit false

namespace Cli.GossipsubSession

open Conc Streams Multiformats Libp2p.Core Libp2p.Identity Libp2p.Host
open Libp2p.Protocols Libp2p.Protocols.Constants
open Libp2p.Protocols.Gossipsub Libp2p.Protocols.Gossipsub.Node

/-- Use the production yamux session through the core muxer seam. -/
def yamuxMuxer : Libp2p.Core.Muxer := Libp2p.Mux.yamux

/-- The real host surface needed by the gossipsub node. -/
structure Running where
  host : Libp2p.Host.Host
  node : Node

/-- Build Noise and the real TCP host. Node.start installs meshsub. -/
def start (identity : PrivKey) (nodeConfig : Node.Config := {}) : IO (Except String Running) := do
  let generated ← (Libp2p.Security.Noise.Config.generate identity).run
  let noise ← match generated with
    | .error e => return .error (reprStr e)
    | .ok cfg => pure cfg
  let pubkey ← match identity.toPublic with
    | .error e => return .error (reprStr e)
    | .ok key => pure key
  let config : Libp2p.Host.Config := {
    identity := identity
    transports := [Streams.Tcp.transport]
    security := [Libp2p.Security.Noise.securityProtocol noise]
    muxers := [yamuxMuxer]
    handlers := [Identify.respondHandler pubkey [] [] none "leanp2p"] }
  let hostResult ← BaseIO.toIO (Libp2p.Host.Host.new config)
  let host ← match hostResult with
    | .error e => return .error (reprStr e)
    | .ok value => pure value
  let node ← BaseIO.toIO (Node.start (HostSeam.ofHost host) nodeConfig)
  return .ok { host, node }

/-- Listen only after Node.start has registered meshsub. -/
def listen (running : Running) (addr : Multiaddr) : Conc.Async (Except String Multiaddr) := do
  return (← running.host.startListening addr).mapError (fun e => reprStr e)

/-- Stop node and host concurrently, then let the caller drain records. -/
def stop (running : Running) : Conc.Async Unit := do
  let tasks ← TaskSet.new
  tasks.spawn running.node.stop
  tasks.spawn (Libp2p.Host.Host.close running.host)
  tasks.joinAll

end Cli.GossipsubSession
