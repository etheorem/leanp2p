import Conc
import Streams
import Libp2p.Security.Mock.Identity

/-!
# Mock: the surface of `libp2p/core` that Noise uses

W5.2 (`libp2p/core`, etheorem/leanp2p#15) has not merged, so this
package builds against a mock of its frozen surface (RULES.md, "Working
ahead of the tree"). The types are copies of the core ARCHITECTURE,
"Public surface": `ProtocolId`, `Role`, `Core.Error` with its four arms,
and the security seam, `SecureConn` and `SecurityProtocol`, with the
handshake signature of root §4.9. The mock imports nothing from the
real package, and it states no axiom. `PeerId` comes from the identity
mock beside it.

At the integration, the package imports `Libp2p.Core`, drops
`open Libp2p.Security.Mock`, and the module goes.
-/

set_option autoImplicit false

namespace Libp2p.Security.Mock.Core

open Conc Streams Libp2p.Security.Mock.Identity

/-- A protocol id: the exact text that multistream-select carries
(§3.4). -/
structure ProtocolId where
  /-- The id text, exactly as it travels on the wire. -/
  toString : String
  deriving DecidableEq, Hashable, Ord, Repr

instance : ToString ProtocolId := ⟨ProtocolId.toString⟩

/-- The two directions of a connection (§3.4). The initiator dialed,
and the responder accepted. -/
inductive Role where
  | initiator
  | responder
  deriving DecidableEq, Repr, Hashable

/-- The coarse seam error (§3.5, §4.9). Each arm carries the rendered
error of the implementation. -/
inductive Error where
  | protocol (detail : String)
  | authentication (detail : String)
  | timeout (detail : String)
  | closed (detail : String)
  deriving DecidableEq, Repr

/-- The log line of the error: the kind, then the rendered detail. -/
def Error.render : Error → String
  | .protocol d => s!"protocol error: {d}"
  | .authentication d => s!"authentication failure: {d}"
  | .timeout d => s!"timeout: {d}"
  | .closed d => s!"closed: {d}"

instance : ToString Error := ⟨Error.render⟩

/-- A connection after a security handshake: the secure `read`,
`write`, and `close`, the two peer ids the handshake proved, the
ciphertext the handshake over-read (§4.7), and the completion. -/
structure SecureConn extends Connection where
  /-- The peer id of our identity key. -/
  localPeer : PeerId
  /-- The peer id the peer proved in the handshake. -/
  remotePeer : PeerId
  /-- The ciphertext the handshake read past its last message. -/
  leftover : ByteArray
  /-- Wait until the secure connection has ended, and answer how it
  ended. -/
  join : ExceptT Error Async Unit

/-- The security seam: one security protocol that multistream-select
can negotiate. -/
structure SecurityProtocol where
  /-- The id that multistream-select negotiates, such as `/noise`. -/
  id : ProtocolId
  /-- Run the handshake in the given role over the connection. The
  `ByteArray` holds the bytes the negotiation over-read. -/
  handshake : Role → Connection → ByteArray → ExceptT Error Async SecureConn

end Libp2p.Security.Mock.Core
