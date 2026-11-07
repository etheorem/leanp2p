import Libp2p.Mux.Constants
import Libp2p.Core
import Yamux.Session
import Yamux.Constants

set_option autoImplicit false

namespace Libp2p.Mux

open Libp2p.Core

/-- Map one yamux protocol error to the core seam error. -/
def mapStreamError (e : Streams.Error) : Libp2p.Core.Error :=
  match e with
  | .closed => .closed "yamux: closed"
  | .reset => .protocol "yamux: reset"
  | .timeout => .timeout "yamux: timeout"

def mapYamuxError (e : Yamux.ProtocolError) : Libp2p.Core.Error :=
  .protocol s!"yamux: {repr e}"

/-- The production yamux muxer over the real core connection seam. -/
def yamux : Libp2p.Core.Muxer where
  id := yamuxId
  «open» := fun role connection leftover => ExceptT.mk do
    let yamuxRole := match role with
      | .initiator => Yamux.Role.client
      | .responder => Yamux.Role.server
    match ← Yamux.Session.new yamuxRole connection leftover with
    | session =>
      return .ok {
        openStream := fun _ => ExceptT.mk do
          return (← session.openStream).mapError mapStreamError
        accept := session.acceptStream
        close := session.close
        join := ExceptT.mk do return (← session.join).mapError mapYamuxError }

end Libp2p.Mux
