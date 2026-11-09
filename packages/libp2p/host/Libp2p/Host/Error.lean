import Multiformats
import Libp2p.Identity
import Libp2p.Core

/-!
# `Host.Error`

The host and `cli/` match on one error type (ARCHITECTURE §3.5). Every
seam below the host fails with the coarse `Core.Error`, and the host
wraps it once, at its own boundary, in the arm of the phase that
failed: `upgrade`, `session`, or `stream`. The other
arms name the decisions the host makes itself: a policy hook said no,
the peerstore holds no address, no transport serves an address, nobody
listens there, the dial targets our own id, or the host is shutting
down. An `IO.Error` fault passes underneath, as a fault (§3.5; the
package ARCHITECTURE, contract 8).
-/

set_option autoImplicit false

namespace Libp2p.Host

open Multiformats Libp2p.Identity

/-- The policy checkpoint that refused a connection (§3.4: a closed
set). The gater answers at the first three (`Core.ConnectionGater`),
and the resource manager at the fourth (`Core.ResourceManager`,
`Core.ConnectionScope.setPeer`). No spec gives a checkpoint a wire
code, so the set has no `toCode`/`ofCode?` pair, as `Core.Role` has
none. -/
inductive Checkpoint where
  /-- `ConnectionGater.allowDial`, before an outbound dial. -/
  | dial
  /-- `ConnectionGater.allowInbound`, after an accept. -/
  | inbound
  /-- `ConnectionGater.allowSecured`, after the handshake, before the
  muxer stage. -/
  | secured
  /-- `ResourceManager.openConnection`, or `ConnectionScope.setPeer`
  once the handshake has proved the peer. -/
  | resources
  deriving DecidableEq, Repr

/-- The checkpoint's name in a log line. -/
def Checkpoint.render : Checkpoint → String
  | .dial => "dial"
  | .inbound => "inbound"
  | .secured => "secured"
  | .resources => "resources"

/-- A host failure: a seam failure that the host wraps, or a decision
of the host. -/
inductive Error where
  /-- The upgrade of a connection failed. The arm keeps the seam error
  as it came, with its rendered detail for the log. -/
  | upgrade (e : Core.Error)
  /-- A session ended with a failure after its upgrade: its `join`
  answered the seam error. -/
  | session (e : Core.Error)
  /-- A stream failed: its open, its negotiation, or its handler. The
  host resets the stream, and the session stays. -/
  | stream (e : Core.Error)
  /-- A policy hook refused the connection at this checkpoint. -/
  | gated (at_ : Checkpoint)
  /-- `dialPeer` found no address for the peer in the peerstore. -/
  | noAddresses (peer : PeerId)
  /-- No configured transport handles the address
  (`Streams.Transport.handles`). -/
  | noTransport (addr : Multiaddr)
  /-- The transport dialed the address, and nobody listens there. -/
  | unreachable (addr : Multiaddr)
  /-- The dial targets the host's own peer id. -/
  | dialSelf
  /-- The host is shut down, or is shutting down (§5.5). -/
  | closing
  deriving DecidableEq, Repr

namespace Error

/-- The log line of the error. -/
def render : Error → String
  | .upgrade e => s!"upgrade failed: {e.render}"
  | .session e => s!"session failed: {e.render}"
  | .stream e => s!"stream failed: {e.render}"
  | .gated c => s!"refused by policy at the {c.render} checkpoint"
  | .noAddresses p => s!"no address for peer {p}"
  | .noTransport a => s!"no transport handles {a.describe}"
  | .unreachable a => s!"nobody listens at {a.describe}"
  | .dialSelf => "a dial to our own peer id"
  | .closing => "the host is closing"

instance : ToString Error := ⟨render⟩

end Error

end Libp2p.Host