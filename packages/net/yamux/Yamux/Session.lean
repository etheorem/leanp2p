import Conc
import Yamux.Core
import Yamux.Mock.Bytes
import Yamux.Mock.Streams

/-!
# The yamux session

The shell around the core (ARCHITECTURE §3.3, §4.8): one loop task drives
`Core.step`, one reader task feeds it bytes, and the application talks
to it through `Stream` values.

The application never touches the loop. A write takes a tag and an
answer slot, posts `Event.write`, and parks on the slot; the loop
performs the core's `Action.done` or `Action.refused` for that tag and
the park ends. No promise enters the core.

`openStream` and `acceptStream` hand out the application view: an inbox
the loop fills plus the three events that post back. `close` closes the
event channel, which wakes the loop's `Chan.recv` with `none`, and
closes the connection.

The connection and the stream come from `Yamux.Mock.Streams` until W4.1
merges; the swap is one import and one namespace.
-/

namespace Yamux

open Conc

/-- One answer slot per tag: the id of an opened stream, or the end of a
write, or the error that refused it. -/
abbrev Slot := Chan (Except ProtocolError (Option StreamId))

/-- A running session. -/
structure Session where
  /-- This endpoint's role. -/
  role : Role
  /-- The connection the loop reads and writes. -/
  conn : Mock.Streams.Connection
  /-- Events into the loop. -/
  events : Chan Event
  /-- Peer-opened streams, waiting for `acceptStream`. -/
  accepts : Chan StreamId
  /-- The core state. One loop task owns it. -/
  core : OnceRef State
  /-- The answer slots, by tag. -/
  tags : OnceRef (List (Nat × Slot))
  /-- The inbox of each live stream, by id. -/
  inboxes : OnceRef (List (Nat × Chan ByteArray))
  /-- The next tag. -/
  nextTag : OnceRef Nat

namespace Session

/-- Start a session over a connection. The leftover bytes are what the
muxer negotiation over-read (ARCHITECTURE §4.7): they are the first
input of the core, not a second reader. -/
def new (conn : Mock.Streams.Connection) (role : Role) (leftover : List Nat := []) :
    BaseIO Session := do
  let events ← Chan.new 64
  let accepts ← Chan.new 16
  let start : State := Core.init role
  let st : State := { start with pending := leftover }
  let core ← OnceRef.new st
  let tags ← OnceRef.new ([] : List (Nat × Slot))
  let inboxes ← OnceRef.new ([] : List (Nat × Chan ByteArray))
  let nextTag ← OnceRef.new 0
  pure { role := role, conn := conn, events := events, accepts := accepts,
         core := core, tags := tags, inboxes := inboxes, nextTag := nextTag }

/-- The answer slot of a tag, if the tag is still live. -/
def slotFor (s : Session) (tag : Nat) : BaseIO (Option Slot) := do
  let xs ← s.tags.get
  pure ((xs.find? (fun p => p.1 == tag)).map (·.2))

/-- Run one action. -/
def perform (s : Session) : Action → Async Unit
  | .send bs => s.conn.write (Mock.Bytes.ofNatList bs)
  | .deliver sid bs => do
      let xs ← s.inboxes.get
      match xs.find? (fun p => p.1 == sid.val) with
      | some p => discard (Chan.send p.2 (Mock.Bytes.ofNatList bs))
      | none => pure ()
  | .accept sid => discard (Chan.send s.accepts sid)
  | .opened tag sid => do
      match ← s.slotFor tag with
      | some slot => discard (Chan.send slot (.ok (some sid)))
      | none => pure ()
  | .done tag => do
      match ← s.slotFor tag with
      | some slot => discard (Chan.send slot (.ok none))
      | none => pure ()
  | .refused tag e => do
      match ← s.slotFor tag with
      | some slot => discard (Chan.send slot (.error e))
      | none => pure ()
  | .close => s.conn.close

/-- The loop: one event at a time, one `step`, then the actions. -/
partial def pump (s : Session) : Async Unit := do
  match ← Chan.recv s.events with
  | none => pure ()
  | some e => do
      let st ← s.core.get
      match Core.step st e with
      | .error _ => s.conn.close
      | .ok (st', acts) => do
          s.core.set st'
          for a in acts do
            s.perform a
          pump s

/-- The reader: bytes off the connection become one `bytes` event. A
closed connection ends the reader, and the loop keeps its own channel,
so a close of one side wakes the other. -/
partial def reader (s : Session) : Async Unit := do
  match ← s.conn.read with
  | none => pure ()
  | some bs => do
      discard (Chan.send s.events (.bytes (Mock.Bytes.toNatList bs)))
      reader s

/-- The application view of one stream: an inbox the loop fills, and the
three events that post back. -/
def streamOf (s : Session) (sid : StreamId) (inbox : Chan ByteArray) : Mock.Streams.Stream :=
  { read := do
      match ← Chan.recv inbox with
      | some bs => pure (.ok (some bs))
      | none => pure (.ok none)
    write := fun bs => do
      let n ← s.nextTag.get
      s.nextTag.set (n + 1)
      let tag : Nat := n
      let slot ← Chan.new 1
      s.tags.update (fun xs => (tag, slot) :: xs)
      discard (Chan.send s.events (.write sid tag (Mock.Bytes.toNatList bs)))
      match ← Chan.recv slot with
      | some (.ok _) => pure (.ok ())
      | some (.error _) => pure (.error .closed)
      | none => pure (.error .closed)
    close := do
      discard (Chan.send s.events (.closeWrite sid))
    reset := do
      discard (Chan.send s.events (.reset sid)) }

/-- Ask for a new stream: the SYN goes out, and the answer carries the
id the allocator chose. -/
def openStream (s : Session) : Async (Option Mock.Streams.Stream) := do
  let n ← s.nextTag.get
  s.nextTag.set (n + 1)
  let tag : Nat := n
  let slot ← Chan.new 1
  s.tags.update (fun xs => (tag, slot) :: xs)
  let inbox ← Chan.new 16
  discard (Chan.send s.events (.open tag))
  match ← Chan.recv slot with
  | some (.ok (some sid)) => do
      s.inboxes.update (fun xs => (sid.val, inbox) :: xs)
      pure (some (s.streamOf sid inbox))
  | _ => pure none

/-- Take the next peer-opened stream, if any. -/
def acceptStream (s : Session) : Async (Option (StreamId × Mock.Streams.Stream)) := do
  match ← Chan.recv s.accepts with
  | none => pure none
  | some sid => do
      let inbox ← Chan.new 16
      s.inboxes.update (fun xs => (sid.val, inbox) :: xs)
      pure (some (sid, s.streamOf sid inbox))

/-- End the session: the loop's `recv` wakes with `none`, and the
connection closes. -/
def close (s : Session) : IO Unit := do
  Chan.close s.events
  s.conn.close

end Session

end Yamux
