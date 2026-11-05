/-!
# The role of one side

Every connection and every session has two sides: the one that dialed
and the one that accepted. The security handshake, the muxer session,
and the policy hooks all take the side as an input (ARCHITECTURE §4.9),
so the type has its own module, and each of them imports only this.
-/

set_option autoImplicit false

namespace Libp2p.Core

/-- The two directions of a connection or a session (§3.4). The
initiator dialed, and the responder accepted. The direction picks the
handshake's message order and the muxer's stream-id parity, and no
spec gives it a wire code, so the set has no `toCode`/`ofCode?` pair
(the core pair, decisions). -/
inductive Role where
  /-- Our side dialed the connection. -/
  | initiator
  /-- Our side accepted the connection. -/
  | responder
  deriving DecidableEq, Repr, Hashable

end Libp2p.Core
