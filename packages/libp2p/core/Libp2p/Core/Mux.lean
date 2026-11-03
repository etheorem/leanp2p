import Conc
import Libp2p.Core.Error
import Libp2p.Core.ProtocolId
import Libp2p.Core.Security
import Libp2p.Core.Mock.Streams

/-!
# Multiplexer interfaces

`Muxer` opens a session over a secure connection. `MuxSession` exposes
streams and session shutdown (ARCHITECTURE §4.9). Implementations live
in `libp2p/mux`.

The field `«open»` uses guillemets because `open` is a Lean keyword.
Callers can write `m.open role conn leftover`.
-/

set_option autoImplicit false

namespace Libp2p.Core

open Libp2p.Core.Mock

/-- The host view of a muxer session, backed by its owned loop tasks. -/
structure MuxSession where
  /-- Open an outbound stream. The id is a label, carried by mplex
  and ignored by yamux; the host must still negotiate the protocol.
  Return `.closed` after the session ends. -/
  openStream : ProtocolId → ExceptT Error Conc.Async Streams.Stream
  /-- Accept an inbound stream. Session close wakes pending accepts
  with `none`. -/
  accept : Conc.Async (Option Streams.Stream)
  /-- Close the session: stop both directions of every stream, close
  the connection, and wake every parked `accept` with `none`. A second
  close does nothing. -/
  close : IO Unit
  /-- Wait for every session task to end. Return `.ok ()` for an
  orderly end or the protocol error; a fault throws. The owner closes
  before joining. Implementations join their `TaskSet` before reading
  `Conc.Outcome.answer`. -/
  join : Conc.Async (Except Error Unit)

/-- A stream multiplexer selected by multistream-select. -/
structure Muxer where
  /-- The negotiated protocol id, defined by the implementation. -/
  id : ProtocolId
  /-- Start a session over the secure connection. Consume the plaintext
  negotiation leftovers as the loop's first input, before reading the
  connection. Start owned tasks before returning; the caller closes
  and joins the session. -/
  «open» : Role → Streams.Connection → ByteArray → ExceptT Error Conc.Async MuxSession

end Libp2p.Core
