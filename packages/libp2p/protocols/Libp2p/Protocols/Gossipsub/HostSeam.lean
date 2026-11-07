import Libp2p.Host
import Libp2p.Core

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub

/-- The host operations used by a gossipsub node. -/
structure HostSeam where
  /-- Open a stream to a peer. -/
  newStream : Libp2p.Identity.PeerId → List Libp2p.Core.ProtocolId →
    Conc.Async (Except Libp2p.Core.Error (Libp2p.Core.ProtocolId × Streams.Stream))
  /-- Register a stream handler. -/
  setHandler : Libp2p.Core.StreamHandler → BaseIO Unit

/-- Adapt a host to the node operations. -/
def HostSeam.ofHost (host : Libp2p.Host.Host) : HostSeam where
  setHandler := host.setHandler
  newStream := fun peer ids => do
    match ← host.newStream peer ids with
    | .ok pair => return .ok pair
    | .error (.stream e) => return .error e
    | .error e => return .error (.protocol e.render)

end Libp2p.Protocols.Gossipsub
