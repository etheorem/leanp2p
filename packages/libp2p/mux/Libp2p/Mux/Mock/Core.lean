import Libp2p.Mux.Mock.Core.ProtocolId
import Conc
import Streams

/-!
# Mock: the muxer seam of `libp2p/core`

W5.2 is not merged. This module copies the seam that `Mux.test` must
compile against (the core pair, public surface; the mux pair, public
surface). It holds no protocol logic.

`Role` and the four `Error` arms follow the core architecture. The
`String` on each arm is a provisional rendered payload. `MuxSession.join`
is a provisional name for the completion the owner joins. Neither
spelling is a landed `Libp2p.Core` declaration.

`Connection` and `Stream` come from `Streams`. `Async` comes from
`Conc`. This module does not copy those types. When W5.2 lands, delete
this module and `Mock/Core/ProtocolId.lean`. The imports move to the
`Libp2p.Core` modules that own the same names.
-/

set_option autoImplicit false

namespace Libp2p.Mux.Mock.Core

open Conc

/-- The local direction of a connection. The core architecture names
`initiator` and `responder`, and gives the set no wire code. -/
inductive Role where
  | initiator
  | responder
  deriving DecidableEq, Repr, Hashable

/-- The coarse seam error. The four arms are the categories in the
core architecture. `detail` is a provisional `String` rendering of the
implementation error. -/
inductive Error where
  | protocol (detail : String)
  | authentication (detail : String)
  | timeout (detail : String)
  | closed (detail : String)
  deriving DecidableEq, Repr, Hashable

/-- The session view a `Muxer` returns. `join` is the provisional
completion the owner waits on after `close`. -/
structure MuxSession where
  /-- Open one outbound stream. The argument is a `ProtocolId`. -/
  openStream :
    ProtocolId → ExceptT Error Async Streams.Stream
  /-- The next inbound stream. `none` means the session has closed. -/
  accept :
    Async (Option Streams.Stream)
  /-- Close the session. -/
  close :
    IO Unit
  /-- Wait until the session tasks end. `.ok ()` is an orderly end.
  `.error` is the protocol result. A fault throws. -/
  join :
    Async (Except Error Unit)

/-- A muxer selected by its protocol id. `«open»` is the field `open`:
`open` is a Lean keyword. -/
structure Muxer where
  /-- The id the negotiator compares. -/
  id : ProtocolId
  /-- Start a session. The `ByteArray` is the negotiation leftover. -/
  «open» :
    Role →
    Streams.Connection →
    ByteArray →
    ExceptT Error Async MuxSession

end Libp2p.Mux.Mock.Core
