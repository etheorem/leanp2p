import Conc
import Libp2p.Core.Error
import Libp2p.Core.ProtocolId
import Libp2p.Core.Mock.Identity
import Libp2p.Core.Mock.Streams

/-!
# Security interfaces

`SecurityProtocol` upgrades a raw connection to a `SecureConn`
(ARCHITECTURE §4.9). Implementations live in `libp2p/security`.

Ciphertext read past the handshake seeds the security protocol's own
transport reader. `SecureConn.leftover` contains bytes at the plaintext
level of `SecureConn.conn`, for the next negotiation stage (§4.7).

A transport AEAD failure closes the connection. Its read returns `none`,
and `join` reports the protocol error so the owner can distinguish the
failure from an orderly end (§3.5).
-/

set_option autoImplicit false

namespace Libp2p.Core

open Libp2p.Core.Mock

/-! ## `Role` -/

/-- The local direction of a connection or stream. The handshake uses
it for message order; the muxer uses it for stream-id assignment. -/
inductive Role where
  /-- The side that dialed the connection, or opened the stream. -/
  | initiator
  /-- The side that accepted it. -/
  | responder
  deriving DecidableEq, Repr, Hashable

namespace Role

/-- The role of the peer on the other end. -/
def opposite : Role → Role
  | .initiator => .responder
  | .responder => .initiator

/-- Reversing a role twice restores it. -/
@[simp] theorem opposite_opposite (r : Role) : r.opposite.opposite = r := by
  cases r <;> rfl

/-- The two ends of a connection never share a role. -/
theorem opposite_ne (r : Role) : r.opposite ≠ r := by
  cases r <;> decide

end Role

/-! ## `SecureConn` -/

/-- The connection and authenticated identities returned by a handshake. -/
structure SecureConn where
  /-- The secure view of the connection: `read` answers plaintext, and
  `write` encrypts. Its `close` closes the underlying transport
  connection too. -/
  conn : Streams.Connection
  /-- The peer id of our own key, as the handshake presented it. -/
  localPeer : Identity.PeerId
  /-- The peer id the remote side proved during the handshake. The
  upgrader checks it against the peer id it dialed (§4.9). -/
  remotePeer : Identity.PeerId
  /-- Plaintext bytes read past the handshake. The next stage consumes
  them before reading `conn`. -/
  leftover : ByteArray
  /-- Wait for the secure transport and its tasks to end. Return
  `.ok ()` for an orderly end or the protocol error; a fault throws.
  The owner closes before joining. Implementations join their tasks
  before reading `Conc.Outcome.answer`. -/
  join : Conc.Async (Except Error Unit)

/-- Close the secure connection, and with it the transport connection.
A second close does nothing. The owner calls `join` after it. -/
def SecureConn.close (sc : SecureConn) : IO Unit :=
  sc.conn.close

/-! ## `SecurityProtocol` -/

/-- A security protocol selected by multistream-select. -/
structure SecurityProtocol where
  /-- The negotiated protocol id, defined by the implementation. -/
  id : ProtocolId
  /-- Run the handshake in the given role over the raw connection. The
  `ByteArray` contains negotiation leftovers, consumed before reading
  the connection.

  A failure is `.authentication` when the peer failed to prove its key,
  `.protocol` when it broke the handshake format, `.timeout` when the
  deadline of §5.4 expired, and `.closed` when the connection ended
  first. The handshake closes the connection before it answers with an
  error. -/
  handshake : Role → Streams.Connection → ByteArray → ExceptT Error Conc.Async SecureConn

end Libp2p.Core
