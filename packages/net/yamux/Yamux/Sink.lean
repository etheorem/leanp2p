import Yamux.Core

/-!
# The action sink

The core answers an event with a list of actions (ARCHITECTURE §3.3).
The shell performs them: it writes the bytes of a frame, hands payload
to a stream, opens a stream to the application, answers a tagged write,
or tears the connection down.

This module names those effects as a seam, so a test can record a run
without a socket and the loop above can fill the seam with the real
connection. The seam carries no protocol decision: each field does one
thing, and the core decides when.

A sink is `IO` because the connection is. The loop of `Yamux/Loop.lean`
is the asynchronous driver; this layer stays small enough to read in
one sitting.
-/

namespace Yamux

/-- The effects one action asks for. -/
structure Sink where
  /-- Write these bytes to the connection. -/
  send : List Nat → IO Unit
  /-- Hand these bytes to the application on a stream. -/
  deliver : StreamId → List Nat → IO Unit
  /-- Offer a peer-opened stream to the application. -/
  accept : StreamId → IO Unit
  /-- Answer a stream request: this tag now owns this id. -/
  opened : Nat → StreamId → IO Unit
  /-- The bytes of a tagged write are on the wire. -/
  done : Nat → IO Unit
  /-- The tagged write cannot go. -/
  refused : Nat → ProtocolError → IO Unit
  /-- Tear the connection down. -/
  close : IO Unit

/-- Run one action. -/
def Sink.perform (k : Sink) : Action → IO Unit
  | .send bs => k.send bs
  | .deliver sid bs => k.deliver sid bs
  | .accept sid => k.accept sid
  | .opened tag sid => k.opened tag sid
  | .done tag => k.done tag
  | .refused tag e => k.refused tag e
  | .close => k.close

/-- Run the actions of one step, in order. -/
def Sink.performAll (k : Sink) : List Action → IO Unit
  | [] => pure ()
  | a :: rest => do
      k.perform a
      k.performAll rest

end Yamux
