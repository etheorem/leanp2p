import Libp2p.Core.Mux
import Libp2p.Mux.Constants
import Yamux.Session

/-!
# The yamux muxer

`Mux.yamux` is the thin libp2p value over the landed session of
`net/yamux`. It moves the role, the connection, and the negotiation
leftover into `Session.new`. It maps errors returned by `openStream`
and `join` into `Core.Error` at this boundary. The frames, the window,
and the tasks stay in `net/yamux`.
-/

set_option autoImplicit false

namespace Libp2p.Mux

open Libp2p.Core

/-- The Yamux side of a core role. The initiator is the client. It
opens odd ids from 1. The responder is the server. It opens even ids
from 2. -/
private def yamuxRole : Role → Yamux.Role
  | .initiator => .client
  | .responder => .server

/-- A Yamux protocol failure at the seam. Every arm ends the session,
so the seam reports the protocol arm. The detail is the derived
`Repr`. -/
private def mapProtocolError (e : Yamux.ProtocolError) : Error :=
  .protocol s!"yamux: {repr e}"

/-- A refusal from `Session.openStream`. `closed` and `reset` use the
closed arm, because this call has produced no stream. `timeout` uses
the timeout arm. A later read or write on the returned stream keeps
`Streams.Error`. -/
private def mapOpenError (e : Streams.Error) : Error :=
  let detail := s!"yamux: {repr e}"
  match e with
  | .closed => .closed detail
  | .reset => .closed detail
  | .timeout => .timeout detail

/-- The production yamux muxer. `id` is `yamuxId`. `open` starts the
landed session. The adapter maps its returned open and join errors
into `Core.Error`. -/
def yamux : Muxer where
  id := yamuxId
  «open» := fun role connection leftover => ExceptT.mk do
    let session ← Yamux.Session.new (yamuxRole role) connection leftover
    return .ok {
      openStream := fun _ =>
        ExceptT.mk ((Except.mapError mapOpenError) <$> session.openStream)
      accept := session.acceptStream
      close := session.close
      join := ExceptT.mk ((Except.mapError mapProtocolError) <$> session.join)
    }

end Libp2p.Mux
