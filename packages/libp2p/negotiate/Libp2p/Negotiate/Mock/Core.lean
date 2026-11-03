import Std
import Conc
import Libp2p.Negotiate.Mock.Streams
import Libp2p.Negotiate.Mock.Identity

/-!
# Core mocks for units 1a and 1b

`ProtocolId` and `Role` live in `libp2p/core` (W5.2, not merged yet).
Unit 1b adds `Error`, `SecurityProtocol`, `SecureConn`, `Muxer`, and
`MuxSession`. This module holds them verbatim from the core
ARCHITECTURE "Public surface", so the negotiate core and the upgrader
compile against the frozen shapes. The import swaps to `Libp2p.Core`
when W5.2 lands. `Repr` joins the derived classes per root §3.2, so
`State`, `Event`, and `Action` can derive `Repr` per root §3.3.

`SecurityProtocol` and `Muxer` mention the streams `Connection`, and
`SecureConn` mentions the identity `PeerId`, so this module imports
the two sibling mocks. The imports are same-leaf and the lint's
rule 3 allows them.
-/

set_option autoImplicit false

namespace Libp2p.Negotiate.Mock.Core

/-- A wrapped-string protocol id. Peers define ids, so the set stays
open. Code compares `ProtocolId` values only (root §3.4). -/
structure ProtocolId where
  toString : String
  deriving DecidableEq, Hashable, Repr

/-- The role of one side of a negotiation (root §4.9). No spec gives
roles a wire code, so it has no `toCode`/`ofCode?` pair. -/
inductive Role where
  | initiator
  | responder
  deriving DecidableEq, Repr, Hashable

/-- The coarse error of root §4.9. Each arm carries the error of the
implementation, in its rendered form. The upgrader and the host act on
this one type (root §3.5). -/
inductive Error where
  | protocol (s : String)
  | authentication (s : String)
  | timeout (s : String)
  | closed (s : String)
  deriving DecidableEq, Repr

/-- The post-handshake connection. It holds the underlying
`Connection` because `Muxer.open` takes a `Connection` (core
ARCHITECTURE, "Public surface"). The `leftover` is every byte the
handshake read past its end; it seeds the reader of the next stage. -/
structure SecureConn where
  conn : Mock.Streams.Connection
  localPeer : Mock.Identity.PeerId
  remotePeer : Mock.Identity.PeerId
  leftover : ByteArray
  close : BaseIO Unit

/-- The security seam. `handshake` consumes the `ByteArray` the
negotiation over-read before it reads the connection (root §4.7). -/
structure SecurityProtocol where
  id : ProtocolId
  handshake : Role → Mock.Streams.Connection → ByteArray →
    ExceptT Error Conc.Async SecureConn

/-- The uniform session view of core ARCHITECTURE, "Public surface".
The upgrader returns the opened session and never calls its fields. -/
structure MuxSession where
  openStream : ExceptT Error Conc.Async Mock.Streams.Stream
  accept : Conc.Async (Option Mock.Streams.Stream)
  close : IO Unit
  join : Conc.Async Unit

/-- The muxer seam. The field is the frozen `open` of the core docs;
`open` is a Lean keyword, so the field is declared escaped and called
`mux.«open»`. -/
structure Muxer where
  id : ProtocolId
  «open» : Role → Mock.Streams.Connection → ByteArray →
    ExceptT Error Conc.Async MuxSession

end Libp2p.Negotiate.Mock.Core
