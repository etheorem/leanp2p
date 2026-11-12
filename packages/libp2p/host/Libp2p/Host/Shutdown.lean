import Conc
import Streams
import Libp2p.Host.Registry
import Libp2p.Host.Gate
import Libp2p.Host.Swarm

/-!
# The shutdown

`close` runs the sequence of ARCHITECTURE §5.5, in order (the package
ARCHITECTURE, contract 4):

1. set the closing flag, and close the shutdown channel that a dial
   delay waits on;
2. close the listeners, those of the secured transports included: each
   accept loop parks on its listener, and the close wakes it. A secured
   listener's close also ends the connections still in their handshake,
   its pending connections (`net/quic`, `Quic/Loop.lean`, "The
   end");
3. close the pending connections: each inbound or outbound upgrade
   parks on its connection, and the close wakes it, with the upgrade
   deadline as the backstop (§5.4);
4. shut down the sessions: each serve task parks in
   `MuxSession.accept`, and `MuxSession.close` wakes it with `none`;
5. join the session loops: the serve tasks, which join their stream
   tasks and their sessions;
6. join the host tasks: the accept loops and the inbound upgrades,
   then the listeners. A secured listener's join also waits for the
   sessions it gave, which share its socket; stage 4 closed them.

Every stage closes the parks of the tasks that a later stage joins, so
every join returns (PRINCIPLES 3.1, 3.2). A path that registers after a
stage took its list sees the flag of stage 1, and closes what it
registered itself (`Libp2p.Host.Swarm`, "The race with the
shutdown").

A fault of a joined task does not stop the sequence: the later joins
still run, and `close` throws the first fault at the end.
-/

set_option autoImplicit false

namespace Libp2p.Host

open Conc Streams

/-- The stages of the shutdown, in their order (§5.5). `close` names
each one as it starts it, so a suite can check the order. -/
inductive Stage where
  /-- The closing flag is set. -/
  | flag
  /-- The listeners close. -/
  | listeners
  /-- The pending connections close. -/
  | pending
  /-- The sessions shut down. -/
  | sessions
  /-- The session loops are joined. -/
  | sessionLoops
  /-- The host tasks are joined. -/
  | hostTasks
  deriving DecidableEq, Repr

namespace Host

/-- Run `act`, and answer its fault instead of throwing it. -/
private def capture (act : Async Unit) : Async (Option IO.Error) := do
  try
    act
    return none
  catch e => return some e

/-- Shut the host down in the order of §5.5 (module doc). `onStage`
hears each stage as it starts; the default ignores it. A second call
finds every list taken and every gate closed, and returns. -/
def close (h : Host) (onStage : Stage → BaseIO Unit := fun _ => pure ()) : Async Unit := do
  -- The ascriptions mark the steps `BaseIO`, so the lift into `Async`
  -- applies (see `Conc.TaskSet.joinAll`).
  (onStage .flag : BaseIO Unit)
  (h.closing.set true : BaseIO Unit)
  (h.shutdown.close : BaseIO Unit)

  (onStage .listeners : BaseIO Unit)
  let listeners ← (h.listeners.updateGet fun ls => (ls.getD [], none) : BaseIO (List Listener))
  for l in listeners do
    discard l.close.toBaseIO
  let securedListeners ← (h.securedListeners.updateGet fun ls => (ls.getD [], none) :
    BaseIO (List Libp2p.Core.SecuredListener))
  for l in securedListeners do
    discard l.close.toBaseIO

  (onStage .pending : BaseIO Unit)
  let pending ← (h.pending.updateGet fun m => (m.getD {}, none) :
    BaseIO (Std.HashMap Nat Connection))
  for (_, c) in pending do
    c.closeQuietly

  (onStage .sessions : BaseIO Unit)
  let table ← (h.sessions.get : BaseIO (SessionTable Served))
  for (_, e) in SessionTable.liveEntries table do
    discard e.session.upgraded.session.close.toBaseIO

  (onStage .sessionLoops : BaseIO Unit)
  let sessionFault ← capture h.sessionTasks.close

  (onStage .hostTasks : BaseIO Unit)
  let hostFault ← capture h.hostTasks.close
  let mut listenerFault : Option IO.Error := none
  for l in listeners do
    listenerFault := listenerFault <|> (← capture l.join)
  for l in securedListeners do
    listenerFault := listenerFault <|> (← capture l.join)

  if let some e := sessionFault <|> hostFault <|> listenerFault then throw e

end Host

end Libp2p.Host
