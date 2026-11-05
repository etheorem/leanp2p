import Yamux.Loop

/-!
# The session

`Session.new` runs a yamux session over a `Connection` of
`net/streams`, and answers its surface (ARCHITECTURE §4.8):

* `openStream` opens a stream with an id of our parity, and
  `acceptStream` takes the next stream the peer opened. Each one is a
  `Stream` of `net/streams`, served by the loop.
* `ping` measures a round trip, and `goAway` ends the session for new
  streams on both sides.
* `close` ends the session, and `join` waits for its tasks and answers
  how it ended (§3.1, "Lifecycle"): `.ok ()` for a normal end, the
  `ProtocolError` for a broken peer. A fault of the connection throws:
  a read fault, a failed write (unless the peer's go-away ended the
  session), or `timeExpired` for a write past the write deadline or for
  a keepalive that no pong answered.

The `Role` picks the parity, and the muxer value of the layer above maps
its own role onto it. The plaintext that the muxer negotiation over-read
arrives as `leftover`: the loop takes it as its first event (§4.7).
-/

set_option autoImplicit false

namespace Yamux

open Conc Streams

/-- A running yamux session. -/
structure Session where
  /-- Open a stream. `.error .closed` when the session has ended, or
  when the stream ids have run out. -/
  openStream : Async (Except Streams.Error Stream)
  /-- The next stream the peer opened. `none` once the session has
  ended. -/
  acceptStream : Async (Option Stream)
  /-- Ping the peer, and return when the answer arrives. `.error
  .timeout` when no answer comes within `pingDeadlineMs`, and `.error
  .closed` when the session ends first. -/
  ping : Async (Except Streams.Error Unit)
  /-- Send a go-away: no new stream opens on either side, and the open
  streams go on. -/
  goAway : Async Unit
  /-- End the session: a normal go-away goes out, every stream ends, and
  the connection closes. A second call does nothing. -/
  close : IO Unit
  /-- Wait until every task of the session has ended, and answer how
  the session ended. The owner calls it after `close`, or to learn of
  the peer's end. -/
  join : Async (Except ProtocolError Unit)

namespace Session

/-- Run a session over `conn`, on our `role`. `leftover` holds the
plaintext that the muxer negotiation read past its last message. The
timers run on `clock`; production code passes `Clock.system`, and a
test passes a test clock. `keepalive` is the host's keepalive interval
(ARCHITECTURE, "Decisions"), `keepaliveIntervalMs` when the host gives
none; `none` turns keepalives off. -/
def new (role : Role) (conn : Connection) (leftover : ByteArray := .empty)
    (clock : Clock := Clock.system) (keepalive : Option Nat := some keepaliveIntervalMs) :
    BaseIO Session := do
  let sh : Shared := {
    conn
    clock
    events := ← Chan.new eventQueueCap
    out := ← Chan.newUnbounded
    controlCount := ← OnceRef.new 0
    room := ← Chan.new 1
    writes := ← Completions.new
    attempts := ← OnceRef.new ({}, false)
    opens := ← Completions.new
    accepts := ← Chan.new backlogCap
    credits := ← Chan.new 1
    alarm := ← Alarm.new
    outcome := ← Outcome.new
    peerGoAway := ← OnceRef.new false
    ownerEnded := ← OnceRef.new false }
  -- The leftover is the first event; the queue is empty, so it takes
  -- it. It holds the reader's credit, so the reader starts after the
  -- loop has stepped it (`Yamux/Loop.lean`, "The reader's credit").
  -- Before it goes a tick, so the core knows when the bytes arrived; the
  -- tick also starts the keepalive interval.
  discard <| sh.events.trySend (.tick (← clock.nowMs))
  if leftover.isEmpty then discard <| sh.credits.trySend ()
  else discard <| sh.events.trySend (.bytes ⟨leftover⟩)
  let tasks ← TaskSet.new
  tasks.spawn do
    let (ending, ports) ← sh.run role keepalive
    sh.teardown ending ports
  tasks.spawn sh.writer
  tasks.spawn sh.reader
  tasks.spawn sh.ticker
  return {
    openStream := do
      let some (tag, slot) ← sh.opens.register | return .error .closed
      if let .error _ ← sh.events.send (.openStream tag) then
        sh.opens.resolve tag (.error .closed)
        return .error .closed
      -- Park: the loop answers the tag, and `teardown` closes the slot.
      match ← slot.recv with
      | some answer => return answer
      | none => return .error .closed
    -- Park: the loop's offer wakes it, and `teardown` closes the queue.
    acceptStream := sh.accepts.recv
    ping := do
      let some (tag, slot) ← sh.writes.register | return .error .closed
      -- The tick first, so the pong's deadline counts from now (module
      -- doc of `Yamux/Core.lean`, "Time").
      discard <| sh.events.send (.tick (← (clock.nowMs : BaseIO Nat)))
      if let .error _ ← sh.events.send (.ping tag) then
        sh.writes.resolve tag (.error .closed)
        return .error .closed
      -- Park: the loop answers the tag, and the writer closes the table
      -- when it ends.
      match ← slot.recv with
      | some answer => return answer
      | none => return .error .closed
    goAway := discard <| sh.events.send .goAway
    -- The loop parks on the event queue, or, under back-pressure, on the
    -- writer's signal; the close reaches both.
    close := do
      sh.events.close
      sh.room.close
    join := do
      tasks.joinAll
      -- The ascriptions mark the reads `BaseIO`, so the lift into
      -- `Async` applies (see `Conc.TaskSet.joinAll`).
      -- A fault of the connection under a clean answer throws (§3.5).
      let result ← sh.outcome.answer
      let writeFault ← (sh.outcome.writeFault : BaseIO (Option IO.Error))
      let goneAway ← (sh.peerGoAway.get : BaseIO Bool)
      let ownerEnded ← (sh.ownerEnded.get : BaseIO Bool)
      -- A failed write under a clean answer throws too, unless the peer's
      -- go-away or the owner's close ended the session, as in go-yamux
      -- (`Yamux/Loop.lean`, `recordWriteFault`).
      match writeFault, result with
      | some e, .ok () => if goneAway || ownerEnded then return result else throw e
      | _, _ => return result }

end Session

end Yamux
