import Conc
import Streams

/-!
# Mock core surface

`#16` cannot import `Libp2p.Core` while `#15` is unmerged: the core package is
still a stub, so there is no `ProtocolId`, no `Error`, no `Role`, no
`SecureConn` and no `SecurityProtocol` to speak of. This file is that
stand-in, and the only mock this unit carries.

The names and the shapes are copies of the core ARCHITECTURE, "Public
surface", and of the modules PR #37 adds (`Libp2p/Core/{Error,ProtocolId,
Security}.lean`), not a simplification of them: `Error` keeps all four arms
with a rendered detail, `SecureConn` keeps the two peer ids, the leftover
bytes and `join`, and `SecurityProtocol.id` is a `ProtocolId` rather than a
`String`. At the integration the import `Libp2p.Security.Mock.Core` becomes
`Libp2p.Core` and this file goes; no declaration outside this file changes
shape.

`Role.opposite` is left out because nothing in this unit uses it.
-/

set_option autoImplicit false

namespace Libp2p.Core

/-- A libp2p peer identity. Opaque here; the identity package owns it. -/
opaque PeerId : Type

/-- An application-defined protocol name used by multistream-select (§3.4). -/
structure ProtocolId where
  /-- The id as the peer sends it, without the multistream newline. -/
  toString : String
  deriving DecidableEq, Hashable, Ord, Repr

namespace ProtocolId

instance : ToString ProtocolId := ⟨ProtocolId.toString⟩

end ProtocolId

/-- A libp2p failure with the rendered implementation error as detail. The
arms are the seam's, not the implementation's: a handshake that cannot parse a
token is `.protocol`, a failed AEAD tag or an unexpected peer is
`.authentication`, and a connection that ends mid-handshake is `.closed`. -/
inductive Error where
  /-- The peer, or our own input, broke a spec. -/
  | protocol (detail : String)
  /-- The peer failed to authenticate, or authenticated as a peer we did not
  expect. -/
  | authentication (detail : String)
  /-- A deadline expired before the operation finished (§5.4). -/
  | timeout (detail : String)
  /-- The connection ended before the operation finished. -/
  | closed (detail : String)
  deriving DecidableEq, Repr, Hashable

namespace Error

/-- The rendered error of the implementation that the arm carries. -/
def detail : Error → String
  | .protocol d => d
  | .authentication d => d
  | .timeout d => d
  | .closed d => d

/-- The log line of an error: the arm, then the detail. -/
def render : Error → String
  | .protocol d => s!"protocol error: {d}"
  | .authentication d => s!"authentication failed: {d}"
  | .timeout d => s!"timeout: {d}"
  | .closed d => s!"closed: {d}"

instance : ToString Error := ⟨render⟩

end Error

/-- The local direction of a connection. The handshake uses it for message
order. -/
inductive Role where
  /-- The side that dialed. -/
  | initiator
  /-- The side that accepted. -/
  | responder
  deriving DecidableEq, Repr, Hashable

namespace Role

/-- The role of the peer on the other end. -/
def opposite : Role → Role
  | .initiator => .responder
  | .responder => .initiator

end Role

/-- The connection and authenticated identities returned by a handshake.

The transport keys are not fields: the implementation keeps them behind this
structure's own `read` and `write`, which is what makes the record
transport-agnostic. -/
structure SecureConn where
  /-- The secure view of the connection: `read` answers plaintext, and
  `write` encrypts. Its `close` closes the underlying connection too. -/
  conn : Streams.Connection
  /-- The peer id of our own key, as the handshake presented it. -/
  localPeer : PeerId
  /-- The peer id the remote side proved during the handshake. -/
  remotePeer : PeerId
  /-- Plaintext bytes read past the handshake (§4.7). -/
  leftover : ByteArray
  /-- Wait for the secure transport and its tasks to end. -/
  join : Conc.Async (Except Error Unit)

/-- Close the secure connection, and with it the underlying connection. -/
def SecureConn.close (sc : SecureConn) : IO Unit :=
  sc.conn.close

/-- The handshake a security protocol exposes: a role, the raw connection and
the negotiation leftovers in, a secure connection or a seam error out. -/
abbrev Handshake :=
  Role → Streams.Connection → ByteArray → ExceptT Error Conc.Async SecureConn

/-- A security protocol selected by multistream-select. -/
structure SecurityProtocol where
  /-- The negotiated protocol id, defined by the implementation. -/
  id : ProtocolId
  /-- Run the handshake in the given role over the raw connection. -/
  handshake : Handshake

end Libp2p.Core
