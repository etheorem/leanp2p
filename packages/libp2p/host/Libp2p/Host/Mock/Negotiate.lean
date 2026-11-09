import Conc
import Streams
import Libp2p.Identity
import Libp2p.Core

/-!
# Mock: the surface of `libp2p/negotiate` that the host uses

The merged `libp2p/negotiate` takes the seam types of `Libp2p.Core`
(issue #53), so this mock carries those types too. The mock stays
until the host swap of issue #70 lands (RULES.md, "Working ahead of
the tree"). It imports nothing from the negotiate package, and it
states no axiom. Both entries fail with the name of the package: no
body negotiates, runs a handshake, or opens a session.

The host needs two calls beside `Negotiate.upgrade`. The merged
package has neither, so the swap retypes the host's use of them
(issue #70):

* `upgradeWith`, the upgrade with a checkpoint after the handshake and
  before the muxer stage. The host's gater and resource manager decide
  there, by the proved peer (the core ARCHITECTURE, "The policy
  shapes"); go's
  upgrader calls `InterceptSecured` at the same place
  (`vendor/go-libp2p/p2p/net/upgrader/upgrader.go`, line 176). A refusal is a
  value, `UpgradeResult.refused`, and no `Core.Error` arm (§3.5).
* `negotiateStream`, multistream-select over one muxed stream. The host
  serves each inbound stream through it, and `newStream` negotiates
  each outbound one. The bytes it reads past the selecting message go
  to the stream's front (§4.7, `Stream.prependBytes`).
-/

set_option autoImplicit false

namespace Libp2p.Host.Mock.Negotiate

open Conc Streams Libp2p.Identity Libp2p.Core

/-- How a stream negotiation failed. The host reads two arms: the end of
the stream before a selection, an orderly end, and the empty proposal
list. -/
inductive Error where
  /-- The stream ended before the negotiation selected a protocol. -/
  | closed
  /-- The initiator has no id to propose. -/
  | noProtocols
  /-- Any other failure, rendered. -/
  | failed (detail : String)
  deriving DecidableEq, Repr

/-- The failure as the coarse seam error (§3.5). -/
def Error.toCore : Error → Core.Error
  | .closed => .closed "multistream: the stream ended before a selection"
  | .noProtocols => .protocol "multistream: no protocol to propose"
  | .failed d => .protocol s!"multistream: {d}"

/-- A connection that the upgrade finished. -/
structure Upgraded where
  /-- The muxer session over the secure connection. -/
  session : MuxSession
  /-- The peer id that the handshake proved, and the upgrader checked. -/
  remotePeer : PeerId
  /-- Wait until the session and the secure connection under it end. -/
  join : ExceptT Core.Error Async Unit

/-- How an upgrade with a checkpoint ended, when no stage failed. -/
inductive UpgradeResult (ρ : Type) where
  /-- Every stage ran, and the checkpoint admitted the peer. -/
  | upgraded (u : Upgraded)
  /-- The checkpoint refused the proved peer, for `reason`. -/
  | refused (reason : ρ)

/-- The upgrade with a checkpoint: negotiate the security protocol, run
the handshake, check the expected peer, call `admit` with the proved
peer, negotiate the muxer, and open the session, all under the 30 s
deadline on `clock` (§5.4). -/
opaque upgradeWith {ρ : Type} (_clock : Clock) (_role : Role) (_conn : Connection)
    (_pending : ByteArray) (_expected : Option PeerId) (_admit : PeerId → BaseIO (Option ρ))
    (_secs : List SecurityProtocol) (_muxers : List Muxer) :
    ExceptT Core.Error Async (UpgradeResult ρ) :=
  throw (.closed "libp2p/negotiate (W5.5) is not integrated")

/-- Negotiate one of `ids` over a stream, as `role`. The answer is the
selected id and the stream, with the bytes read past the selecting
message at its front. -/
opaque negotiateStream (_role : Role) (_s : Stream) (_ids : List ProtocolId) :
    ExceptT Error Async (ProtocolId × Stream) :=
  throw (.failed "libp2p/negotiate (W5.5) is not integrated")

end Libp2p.Host.Mock.Negotiate
