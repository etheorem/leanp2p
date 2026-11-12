import Conc
import Streams
import Quic.Constants
import Quic.Error

/-!
# The views of a QUIC connection

The application holds a QUIC connection as a `Quic.Conn`, and its
streams as `Streams.Stream` values. Neither touches the shim: each view
posts a `Command` to the endpoint's loop and parks on its answer
(`Quic/Loop.lean`), so the shim sees one caller (root ARCHITECTURE
§3.3). This module holds the types the application sees and the views
over the loop's queues.

## The streams

A `Streams.Stream` of a QUIC stream reads from an inbox that the loop
fills. A read posts the count of its bytes to the loop, which returns
that credit to the peer. The peer cannot send past the window we
granted, so the window bounds the inbox (PRINCIPLES 3.4). A write
posts its bytes and parks until the loop answers. While the stream's
unacknowledged bytes stay under `streamSendCap`, the loop answers once
the shim holds the bytes for sending. Past the cap, it answers after
the peer's acknowledgments. From there the QUIC stack owns the bytes,
and it sends them again until the peer acknowledges them (RFC 9000
§13.3). A TCP stack owns the bytes of a finished socket write the same
way: that is "on the wire" in the `Stream` contract.

The two directions of a stream end apart (RFC 9000 §3). The peer's
RESET_STREAM ends our reads with `.reset`. The peer's STOP_SENDING ends
our writes with `.reset`, and our reads go on. Our own `reset` ends
both, drops the bytes that wait in the inbox, and returns their credit.

## The admission

A listener asks its caller about each new connection when the
connection's first datagram arrives, before any state exists for it
(`Admitted`). The caller answers with three things: the certificate
check of the connection, a value of its own that comes back with the
connection, and the release of that value. The release runs for a
connection that ends before the listener hands it over. A refusal
costs the peer one CONNECTION_REFUSED
and us no state. The go reference asks its resource manager at the same
point (the package ARCHITECTURE, "The admission").
-/

set_option autoImplicit false

namespace Quic

open Conc Streams Multiformats

/-- The check of a peer's certificate (DER): `none` accepts, and
`some reason` refuses inside the handshake. -/
abbrev Check := ByteArray → Option String

/-- A listener caller's answer for a new connection (the module doc,
"The admission"). -/
structure Admitted (α : Type) where
  /-- The check of the peer's certificate inside the handshake. -/
  check : Check
  /-- The caller's value, which comes back with the connection. -/
  value : α
  /-- Runs once when the connection ends before the listener hands it
  over: its handshake failed, the accept queue was full, or the
  endpoint ended. After the hand-over the receiver owns `value`. -/
  release : BaseIO Unit

/-- What a stream's inbox carries. -/
inductive Item where
  /-- Bytes of the peer. -/
  | data (b : ByteArray)
  /-- The peer's FIN. -/
  | fin
  /-- The peer's RESET_STREAM, or our own reset. -/
  | reset

/-- The read side of a stream view, as the `Stream` contract states it:
the first read after an error answers the error, and the reads after it
answer `.ok none`. -/
private inductive ReadSide where
  /-- Reads take the inbox. -/
  | live
  /-- Our reset came before the next read: that read answers `.reset`
  at once, ahead of the bytes the loop has yet to drop. -/
  | resetPending
  /-- The stream has ended: reads answer `.ok none`. -/
  | ended

/-- The answer of a read that the side gives without the inbox, and the
side after it: a pending reset answers once, then the side has ended. -/
private def ReadSide.answer :
    ReadSide → Option (Except Streams.Error (Option ByteArray)) × ReadSide
  | .live => (none, .live)
  | .resetPending => (some (.error .reset), .ended)
  | .ended => (some (.ok none), .ended)

/-- One QUIC connection, as the application sees it. -/
structure Conn where
  /-- The endpoint's handle of the connection. -/
  handle : UInt64
  /-- The peer's certificate, DER, which the caller's check accepted. -/
  peerCertificate : ByteArray
  /-- The ALPN protocol the handshake selected. RFC 9001 §8.1 makes it
  mandatory, so it is never empty. -/
  alpn : String
  /-- Our address: the UDP socket's. -/
  localAddr : Multiaddr
  /-- The peer's address. -/
  remoteAddr : Multiaddr
  /-- Open a stream. Parks while the peer allows no more streams. -/
  openStream : Async (Except Error Stream)
  /-- The next stream the peer opened; `none` once the connection has
  ended. -/
  accept : Async (Option Stream)
  /-- Close the connection with an application error code and a reason;
  `orderlyClose` is an orderly close. A second close does nothing. -/
  close : (code : UInt64) → (reason : String) → BaseIO Unit
  /-- Wait until the connection has ended, and answer how: `.ok` for an
  orderly close by either side, the error otherwise. -/
  join : Async (Except Error Unit)

/-- The commands of the views to the loop. -/
inductive Command where
  /-- Open a stream on `conn`; the answer goes to `reply`. -/
  | openStream (conn : UInt64) (reply : Chan (Except Error Stream))
  /-- Append `bytes` to a stream, and the FIN after them when `fin`
  holds; the answer goes to `reply`. -/
  | write (conn stream : UInt64) (bytes : ByteArray) (fin : Bool)
      (reply : Chan (Except Streams.Error Unit))
  /-- The reader took `n` bytes of a stream: return their credit. -/
  | consume (conn stream : UInt64) (n : UInt64)
  /-- Reset both directions of a stream. -/
  | reset (conn stream : UInt64)
  /-- Close `conn` with an application error code and a reason. -/
  | close (conn : UInt64) (code : UInt64) (reason : String)
  /-- The application took the peer's stream from the accept queue. -/
  | accepted (conn stream : UInt64)

/-- The parts of one connection that the loop fills or closes, and that
its views park on. -/
structure ConnPorts where
  /-- The peer's streams that wait for `accept`, with their ids. -/
  accepts : Chan (UInt64 × Stream)
  /-- Closed at the end of the connection. -/
  ended : Chan Unit
  /-- How the connection ended: `none` for an orderly end. -/
  result : OnceRef (Option Error)

/-- The ports of a new connection. The accept queue holds
`acceptBacklog` streams, which the stream credit keeps from filling
(`Quic.acceptBacklog`). -/
def ConnPorts.new : BaseIO ConnPorts := do
  return {
    accepts := ← Chan.new acceptBacklog
    ended := ← Chan.new 1
    result := ← OnceRef.new none }

/-- The error of an operation that waited when the endpoint ended. -/
def endedError : Error := .ended

/-- The stream view over the loop's command queue (the module doc,
"The streams"). -/
def mkStream (commands : Chan Command) (conn sid : UInt64) (inbox : Chan Item) :
    BaseIO Stream := do
  let side ← OnceRef.new ReadSide.live
  let post (c : Command) : BaseIO Bool := commands.trySend c
  return {
    read := do
      -- One atomic step (root §4.1, rule 3). The ascription names the
      -- `BaseIO` call: inside `Async`, the lift would otherwise take the
      -- binder's type for its own.
      let early ← (side.updateGet ReadSide.answer :
        BaseIO (Option (Except Streams.Error (Option ByteArray))))
      if let some answer := early then return answer
      -- Park: the loop's next item wakes it, and so does the end of the
      -- connection, which closes the inbox.
      match ← inbox.recv with
      | some (.data b) =>
        discard <| post (.consume conn sid b.size.toUInt64)
        return .ok (some b)
      | some .fin => side.set .ended; return .ok none
      | some .reset => side.set .ended; return .error .reset
      | none => side.set .ended; return .error .closed
    write := fun b => do
      let reply ← Chan.new 1
      unless ← post (.write conn sid b false reply) do return .error .closed
      -- Park: the loop answers, and the end of the connection answers
      -- every write that waits.
      match ← reply.recv with
      | some r => return r
      | none => return .error .closed
    close := do
      let reply ← Chan.new 1
      if ← post (.write conn sid .empty true reply) then
        -- Park: the loop answers the FIN like a write.
        discard reply.recv
    reset := do
      -- The view answers the next read itself. The loop drops the
      -- inbox's bytes only when it takes the command, and a read before
      -- that would return them. A stream that has ended stays ended.
      side.update fun
        | .ended => .ended
        | _ => .resetPending
      discard <| post (.reset conn sid) }

/-- The connection view over the loop's command queue. `owner` is the
task set of the endpoint that the connection owns, a dial's endpoint.
The connection's join is then the endpoint's join too. -/
def mkConn (commands : Chan Command) (owner : Option TaskSet) (localAddr : Multiaddr)
    (handle : UInt64) (ports : ConnPorts) (cert : ByteArray) (alpn : String)
    (remoteAddr : Multiaddr) : Conn where
  handle
  peerCertificate := cert
  alpn
  localAddr
  remoteAddr
  openStream := do
    let reply ← Chan.new 1
    unless ← (commands.trySend (.openStream handle reply) : BaseIO Bool) do
      return .error endedError
    -- Park: the loop answers when the peer's credit allows, and the end
    -- of the connection answers every open that waits.
    match ← reply.recv with
    | some r => return r
    | none => return .error endedError
  accept := do
    -- Park: the peer's next stream wakes it, and so does the end of the
    -- connection, which closes the queue.
    match ← ports.accepts.recv with
    | some (sid, s) =>
      -- The loop returns the stream's credit once it is also over.
      discard <| (commands.trySend (.accepted handle sid) : BaseIO Bool)
      return some s
    | none => return none
  close := fun code reason => do
    discard <| commands.trySend (.close handle code reason)
  join := do
    -- Park: the end of the connection closes `ended`.
    discard ports.ended.recv
    if let some tasks := owner then tasks.joinAll
    match ← (ports.result.get : BaseIO (Option Error)) with
    | some e => return .error e
    | none => return .ok ()

end Quic
