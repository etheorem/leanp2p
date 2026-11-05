import Libp2p.Mux.Mock.Core
import Libp2p.Mux.Test.State
import Libp2p.Mux.Test.Wire
import Conc
import Streams

/-!
# Runtime shell for the test session

One owner task steps `Libp2p.Mux.Test.State`. One reader task calls
`Connection.read` and posts slices. Callers post opens, writes, and
resets on the same event channel. The owner performs each outbound
`Connection.write`, then `ackSend` or `failSend`, and only then takes
another event.

A turn takes at most one queued event, then at most one parser budget,
then at most one outbound chunk. A byte event's `feed` is that budget.
A non-byte event is followed by one retained pull in the same turn.
A dequeued connection end or reader fault is held while a complete
frame remains. Each later turn answers one caller event and takes one
budget, and no chunk starts after that dequeue.
Teardown closes the event channel before it drains. An owner that
throws stores that `IO.Error`, wakes every waiter, and throws the
same error. Every later `join` throws the stored error.
-/

set_option autoImplicit false

namespace Libp2p.Mux.Test.Session

open Libp2p.Mux.Mock.Core
open Libp2p.Mux.Test.State
open Libp2p.Mux.Test.Wire
open Conc hiding Error

/-- Events waiting for the owner. The architecture policy table is
this capacity. -/
def eventChannelCap : Nat := 32

/-- Unread frames queued on one live stream. A further frame resets
that stream. -/
def inboundFrameCredit : Nat := 4

/-- A one-shot barrier. The owner sends on `entered` and then waits
on `release`. -/
structure TurnGate where
  entered : Chan Unit
  release : Chan Unit

/-- Refs a test installs through `startWithHooks`. `start` does not
take this structure, and `Libp2p.Mux` does not import it. With no
hooks the owner reads no hook ref. -/
structure TestHooks where
  /-- Live entries in the port map, written after each retirement sweep. -/
  registrySize : IO.Ref Nat
  /-- The owner throws `InvariantError.sendInFlight` on the next event. -/
  forceInvariant : IO.Ref Bool
  /-- The owner throws `mux: missing port 0` on the next event. -/
  forceMissingPort : IO.Ref Bool
  /-- One unit after an open, a write, or a reader event is accepted.
  `none` sends nothing. -/
  acceptedEvent : IO.Ref (Option (Chan Unit))
  /-- Remote frames the owner has applied. -/
  appliedFrames : IO.Ref Nat
  /-- Each resolved local open, and each caller event a deferred turn
  releases, sends `appliedFrames` here. `none` sends nothing. -/
  captureOpenFrames : IO.Ref (Option (Chan Nat))
  /-- Pause once after a budget that leaves a complete frame. -/
  pauseAfterBudget : IO.Ref (Option TurnGate)
  /-- Pause once after a cause has won and before `Outcome` is written. -/
  beforeOutcome : IO.Ref (Option TurnGate)

/-- Throw `e` as `InvariantError.toIOError`. The owner uses this for
every pure-step failure. It does not continue with the old state. -/
private def throwInvariant {α : Type} (e : InvariantError) : Async α :=
  throw e.toIOError

/-! ## Ports, events, runtime -/

private structure Port where
  mode : OnceRef (Option PortEnd)
  inbox : Chan (Except Streams.Error ByteArray)
  permits : Chan Unit

/-- `write` carries the handle's port. A retired id leaves the map,
and a late write answers from that port. `halfClose` and `reset`
name the stream id. -/
private inductive Event where
  | openLocal (reply : Chan (Except Error Streams.Stream))
  | write (port : Port) (id : UInt32) (tag : Nat) (bytes : ByteArray) (heldPermit : Bool)
  | halfClose (id : UInt32)
  | reset (id : UInt32)
  | bytes (chunk : ByteArray)
  | ended
  | readerFault (error : IO.Error)

/-- A dequeued connection end or reader fault. The owner stores it
while a complete frame remains, and clears it when that cause is
claimed or dropped. -/
private inductive DeferredTerminal where
  | ended
  | readerFault (error : IO.Error)

private structure Runtime where
  conn : Streams.Connection
  events : Chan Event
  livePermits : Chan Unit
  acceptPermits : Chan Unit
  acceptQ : Chan Streams.Stream
  writes : Streams.Completions Unit
  ports : OnceRef (Std.HashMap UInt32 Port)
  state : OnceRef State
  outcome : Outcome Error
  tasks : TaskSet
  closing : OnceRef Bool
  /-- Set when normal or exceptional teardown begins. A second entry
  does not record another result. -/
  teardownStarted : OnceRef Bool
  /-- The first `IO.Error` that escaped the owner. `join` throws it
  after `TaskSet.joinAll` has consumed its report. A later store
  leaves this value in place. -/
  ownerFault : OnceRef (Option IO.Error)
  /-- See `DeferredTerminal`. The owner is the only task that reads
  or writes this cell. -/
  deferredTerminal : OnceRef (Option DeferredTerminal)
  /-- The opener whose `openLocal` step is running. `resolveOpen`
  publishes on it and clears it. -/
  pendingOpen : OnceRef (Option (Chan (Except Error Streams.Stream)))
  hooks : Option TestHooks

private def preload (c : Chan Unit) (n : Nat) : BaseIO Unit := do
  for _ in List.range n do
    discard <| c.trySend ()

private def returnLivePermit (rt : Runtime) : BaseIO Unit := do
  discard <| rt.livePermits.trySend ()

private def returnWritePermit (p : Port) : BaseIO Unit := do
  discard <| p.permits.trySend ()

private def returnAcceptPermit (rt : Runtime) : BaseIO Unit := do
  discard <| rt.acceptPermits.trySend ()

private def newPort : BaseIO Port := do
  let permits ← Chan.new State.admittedWriteCap
  preload permits State.admittedWriteCap
  return {
    mode := ← OnceRef.new none
    inbox := ← Chan.new inboundFrameCredit
    permits }

private def portMode (p : Port) : BaseIO WriteMode := do
  match ← p.mode.get with
  | some .halfClosed => return .halfClosed
  | some .reset => return .reset
  | some .sessionClosed => return .sessionClosed
  | none => return .open

private def lookup (rt : Runtime) (id : UInt32) : BaseIO (Option Port) := do
  return (← rt.ports.get).get? id

/-- The port an active action names. Absence is an internal failure.
Terminal cleanup walks the map itself and does not call this. -/
private def requirePort (rt : Runtime) (id : UInt32) : Async Port := do
  match ← lookup rt id with
  | some p => return p
  | none => throw <| IO.userError s!"mux: missing port {id}"

private def publishRegistry (rt : Runtime) : BaseIO Unit := do
  if let some hooks := rt.hooks then
    hooks.registrySize.set (← rt.ports.get).size

/-- Tell a test that an event entered the channel. No hook, and an
empty watch channel, send nothing. -/
private def noteAccepted (rt : Runtime) : Async Unit := do
  let some hooks := rt.hooks | return
  let some ch ← (hooks.acceptedEvent.get : BaseIO (Option (Chan Unit))) | return
  discard <| ch.send ()

/-- Send `appliedFrames` while a test is watching opens or deferred releases. -/
private def noteOpenFrames (rt : Runtime) : Async Unit := do
  let some hooks := rt.hooks | return
  let some ch ← (hooks.captureOpenFrames.get : BaseIO _) | return
  discard <| ch.send (← hooks.appliedFrames.get)

/-- One use of a test barrier. The slot is cleared before the wait. -/
private def waitGate (slot : IO.Ref (Option TurnGate)) : Async Unit := do
  let some gate ← (slot.get : BaseIO (Option TurnGate)) | return
  slot.set none
  discard <| gate.entered.send ()
  discard <| gate.release.recv

/-- After a budget that left a complete frame, let a test queue an event. -/
private def pauseAfterBudget (rt : Runtime) : Async Unit := do
  let s ← (rt.state.get : BaseIO State)
  if !s.parser.hasComplete then return
  let some hooks := rt.hooks | return
  waitGate hooks.pauseAfterBudget

/-- After the pure cause has won, and before `Outcome` changes. -/
private def pauseBeforeOutcome (rt : Runtime) : Async Unit := do
  let some hooks := rt.hooks | return
  waitGate hooks.beforeOutcome

private def chunkWire (id : UInt32) (raw : ByteArray) : ByteArray :=
  Header.encodeB {
    kind := .data
    streamId := id
    length := UInt32.ofNat raw.size } ++ raw

private def failReply (reply : Chan (Except Error Streams.Stream)) (e : Error) :
    BaseIO Unit := do
  discard <| reply.trySend (.error e)
  reply.close

/-- Answer one event that teardown owns. The caller answers an event
whose send failed, and does not call this. -/
private def releaseQueued (rt : Runtime) (ev : Event) : BaseIO Unit := do
  match ev with
  | .openLocal reply =>
    failReply reply closedError
    returnLivePermit rt
  | .write port _ tag _ held =>
    rt.writes.resolve tag (.error .closed)
    if held then returnWritePermit port
  | _ => pure ()

private def writeStream (rt : Runtime) (id : UInt32) (p : Port) (bytes : ByteArray) :
    Async (Except Streams.Error Unit) := do
  if !bytes.isEmpty then
    match ← p.permits.recv with
    | none =>
      match ← (portMode p : BaseIO WriteMode) with
      | .reset => return .error .reset
      | _ => return .error .closed
    | some _ => pure ()
  let some (tag, slot) ← (rt.writes.register : BaseIO _)
    | do
      if !bytes.isEmpty then returnWritePermit p
      return .error .closed
  match ← rt.events.send (.write p id tag bytes (!bytes.isEmpty)) with
  | .error _ =>
    if !bytes.isEmpty then returnWritePermit p
    rt.writes.resolve tag (.error .closed)
    return .error .closed
  | .ok () =>
    noteAccepted rt
    match ← slot.recv with
    | some answer => return answer
    | none => return .error .closed

private def mint (rt : Runtime) (id : UInt32) : Async Streams.Stream := do
  let p ← (newPort : BaseIO Port)
  rt.ports.update fun m => m.insert id p
  publishRegistry rt
  let base ← Streams.Stream.ofPort {
    inbox := p.inbox
    endedBy := do
      match ← (p.mode.get : BaseIO (Option PortEnd)) with
      | some .reset => return some .reset
      | _ => return none
    completions := rt.writes
    postWrite := fun _ _ => pure (.ok ())
    postConsumed := fun _ => pure (.ok ())
    postClose := rt.events.send (.halfClose id)
    postReset := rt.events.send (.reset id) }
  return { base with write := writeStream rt id p }

/-! ## Owner steps -/

private def claimClose (rt : Runtime) : Async (List Action) := do
  let s ← (rt.state.get : BaseIO State)
  if s.cause.isRunning then
    let step := State.claim s .ownerClose
    rt.state.set step.state
    return step.actions
  else
    return []

private def doWrite (rt : Runtime) (bytes : ByteArray) : Async (List Action) := do
  -- The pure state still holds the outbound tag until this write
  -- returns. The closing flag is read again here, after it may have
  -- changed during the previous action. The `try` covers the write alone.
  if ← (rt.closing.get : BaseIO Bool) then
    return ← claimClose rt
  let wrote : Except IO.Error Unit ←
    try
      rt.conn.write bytes
      pure (.ok ())
    catch e =>
      pure (.error e)
  let s ← (rt.state.get : BaseIO State)
  match wrote with
  | .ok () =>
    match State.ackSend s with
    | .ok step =>
      rt.state.set step.state
      return step.actions
    | .error e => throwInvariant e
  | .error e =>
    if ← (rt.closing.get : BaseIO Bool) then
      claimClose rt
    else if s.cause.isRunning then
      match State.failSend s e with
      | .ok step =>
        rt.state.set step.state
        return step.actions
      | .error inv => throwInvariant inv
    else
      throwInvariant .sendAfterTerminal

/-- Close the event channel, then take every event that entered before
that close. Each queued open and write is answered here. -/
private def rejectQueued (rt : Runtime) : BaseIO Unit := do
  rt.events.close
  for ev in ← (rt.events.drain : BaseIO (List Event)) do
    releaseQueued rt ev

/-- Wake admission, completions, and every port still in the map.
Closes are idempotent. This path does not record an outcome. A missing
map entry is a port already dropped after its retirement actions. -/
private def wakeWaiters (rt : Runtime) : Async Unit := do
  if let some reply ← (rt.pendingOpen.get : BaseIO _) then
    failReply reply closedError
    rt.pendingOpen.set none
  rt.writes.closeAll
  rt.livePermits.close
  rt.acceptPermits.close
  rt.acceptQ.close
  let ports ← (rt.ports.get : BaseIO (Std.HashMap UInt32 Port))
  for (_, p) in ports.toList do
    p.inbox.close
    p.permits.close
  rt.ports.set ({} : Std.HashMap UInt32 Port)
  rt.conn.closeQuietly

private def finishCause (rt : Runtime) (c : Cause) : Async Unit := do
  if ← (rt.teardownStarted.get : BaseIO Bool) then return
  rt.teardownStarted.set true
  rejectQueued rt
  -- The pure cause has already won. Close may set the request flag
  -- during this wait. `markClosing` runs only for owner close.
  pauseBeforeOutcome rt
  match c with
  | .running =>
    throw <| IO.userError "mux: teardown while running"
  | .ownerClose =>
    rt.outcome.markClosing
    rt.outcome.finish (.ok ())
  | .connectionEnd =>
    rt.outcome.finish (.ok ())
  | .readerFault e | .writerFault e =>
    rt.outcome.recordFault e
    rt.outcome.finish (.ok ())
  | .protocol e =>
    rt.outcome.finish (.error e)
  wakeWaiters rt

/-- The owner threw. Wake the same waiters. Do not store a successful
result, and do not replace the error the caller rethrows. -/
private def teardownOnExit (rt : Runtime) : Async Unit := do
  rt.teardownStarted.set true
  rejectQueued rt
  try
    wakeWaiters rt
  catch _ =>
    pure ()

/-- Drop ids whose retirement actions have already run. The handle
keeps its `Port`. -/
private def forgetRetired (rt : Runtime) : BaseIO Unit := do
  let live := (← (rt.state.get : BaseIO State)).live
  rt.ports.update fun m =>
    m.toList.foldl (init := ({} : Std.HashMap UInt32 Port)) fun acc (id, p) =>
      if (live.get? id).isSome then acc.insert id p else acc
  publishRegistry rt

private def perform (rt : Runtime) (acts : List Action) : Async Unit := do
  let mut queue := acts
  repeat
    match queue with
    | [] => break
    | act :: rest =>
      queue := rest
      match act with
      | .sendFrame frame =>
        let more ← doWrite rt (Frame.encodeB frame)
        queue := more ++ queue
      | .sendChunk id _ bytes =>
        let more ← doWrite rt (chunkWire id bytes)
        queue := more ++ queue
      | .resolveOpen result =>
        match ← (rt.pendingOpen.get : BaseIO _) with
        | none => throw <| IO.userError "mux: open reply missing"
        | some reply =>
          rt.pendingOpen.set none
          match result with
          | .error e => failReply reply e
          | .ok id =>
            noteOpenFrames rt
            let stream ← mint rt id
            discard <| reply.trySend (.ok stream)
            reply.close
      | .resolveWrite tag result =>
        rt.writes.resolve tag result
      | .returnLivePermit =>
        returnLivePermit rt
      | .returnWritePermit id =>
        returnWritePermit (← requirePort rt id)
      | .returnAcceptPermit _ =>
        returnAcceptPermit rt
      | .setPort id reason =>
        let p ← requirePort rt id
        p.mode.set (some reason)
      | .closeWritePermits id =>
        let p ← requirePort rt id
        p.permits.close
      | .deliver id bytes =>
        let p ← requirePort rt id
        let sent ← (p.inbox.trySend (.ok bytes) : BaseIO Bool)
        if !sent && !(← (p.inbox.isClosed : BaseIO Bool)) then
          let s ← (rt.state.get : BaseIO State)
          match State.resetLocal s id with
          | .ok step =>
            rt.state.set step.state
            queue := step.actions ++ queue
          | .error e => throwInvariant e
      | .enqueueAccept id =>
        let stream ← mint rt id
        if !(← (rt.acceptQ.trySend stream : BaseIO Bool)) then
          throw <| IO.userError s!"mux: accept enqueue failed {id}"
      | .closeInbox id =>
        let p ← requirePort rt id
        p.inbox.close
      | .closeAccept =>
        rt.acceptQ.close
      | .terminal c =>
        finishCause rt c
  forgetRetired rt

/-- Claim owner close when the session is still running, and perform
that claim. An earlier winner leaves the action list empty. -/
private def performClose (rt : Runtime) : Async Unit := do
  let actions ← claimClose rt
  if !actions.isEmpty then
    perform rt actions

private def enact (rt : Runtime) (step : Step) : Async Unit := do
  rt.state.set step.state
  perform rt step.actions

private def enactExcept (rt : Runtime) (x : Except InvariantError Step) : Async Unit := do
  match x with
  | .ok step => enact rt step
  | .error e => throwInvariant e

private def applyFrame (rt : Runtime) (f : Frame) : Async Unit := do
  if let some hooks := rt.hooks then
    hooks.appliedFrames.modify (· + 1)
  let s ← (rt.state.get : BaseIO State)
  if !s.cause.isRunning then return
  if f.kind == Kind.open then
    match State.classifyRemote s f.streamId with
    | .error _ =>
      enactExcept rt (State.openRemote s f.streamId false false)
    | .ok () =>
      let gotLive ← (rt.livePermits.tryRecv : BaseIO (Option Unit))
      let gotAccept ← (rt.acceptPermits.tryRecv : BaseIO (Option Unit))
      match State.openRemote s f.streamId gotLive.isSome gotAccept.isSome with
      | .error e =>
        if gotLive.isSome then returnLivePermit rt
        if gotAccept.isSome then returnAcceptPermit rt
        throwInvariant e
      | .ok step => enact rt step
  else
    enactExcept rt (State.apply s f)

private def pullOnce (rt : Runtime) : Async Unit := do
  let s ← (rt.state.get : BaseIO State)
  let pulled := State.pull s
  rt.state.set pulled.state
  perform rt pulled.actions
  for f in pulled.frames do
    if (← (rt.state.get : BaseIO State)).cause.isRunning then
      applyFrame rt f
  pauseAfterBudget rt

private def feed (rt : Runtime) (chunk : ByteArray) : Async Unit := do
  let s ← (rt.state.get : BaseIO State)
  if !s.cause.isRunning then return
  match Parser.feedB s.parser chunk with
  | .error _ =>
    enact rt (State.claim s (.protocol protocolMalformed))
  | .ok (frames, p) =>
    rt.state.set (State.setParser s p)
    for f in frames do
      if (← (rt.state.get : BaseIO State)).cause.isRunning then
        applyFrame rt f
  pauseAfterBudget rt

/-- A dequeued write carries the handle's port. Admission reads that
port. It does not invent a mode when the map no longer has the id.
After the session has left `running`, the same port returns the permit. -/
private def onWrite (rt : Runtime) (p : Port) (id : UInt32) (tag : Nat)
    (bytes : ByteArray) (held : Bool) : Async Unit := do
  let s ← (rt.state.get : BaseIO State)
  if !s.cause.isRunning then
    rt.writes.resolve tag (.error .closed)
    if held then returnWritePermit p
    return
  let mode ← portMode p
  if bytes.isEmpty then
    enact rt (State.writeEmpty s tag mode)
  else if mode ≠ .open then
    rt.writes.resolve tag (writeAnswer mode)
    if held then returnWritePermit p
  else
    enact rt (State.admitWrite s id tag bytes)

/-- `true` when the caller may pump. Connection end and a reader fault
return `false`. A close request wins while the session is still running.
A byte event's `true` result means `feed` already spent the budget. -/
private def dispatch (rt : Runtime) (ev : Event) : Async Bool := do
  if ← (rt.closing.get : BaseIO Bool) then
    releaseQueued rt ev
    performClose rt
    return false
  match ev with
  | .ended =>
    let s ← (rt.state.get : BaseIO State)
    if s.cause.isRunning then
      enact rt (State.inboundEnd s)
    return false
  | .readerFault e =>
    let s ← (rt.state.get : BaseIO State)
    if s.cause.isRunning then
      enact rt (State.claim s (.readerFault e))
    return false
  | .openLocal reply =>
    rt.pendingOpen.set (some reply)
    let s ← (rt.state.get : BaseIO State)
    enact rt (State.openLocal s)
    return true
  | .write port id tag bytes held =>
    onWrite rt port id tag bytes held
    return true
  | .halfClose id =>
    let s ← (rt.state.get : BaseIO State)
    enact rt (State.halfClose s id)
    return true
  | .reset id =>
    let s ← (rt.state.get : BaseIO State)
    enactExcept rt (State.resetLocal s id)
    return true
  | .bytes chunk =>
    feed rt chunk
    return true

/-- Send one ready chunk. `false` means the session had nothing to
send, or a terminal cell or the close request already owns the turn. -/
private def pumpOne (rt : Runtime) : Async Bool := do
  if (← rt.deferredTerminal.get).isSome then return false
  if ← (rt.closing.get : BaseIO Bool) then return false
  let s ← (rt.state.get : BaseIO State)
  if !s.cause.isRunning then return false
  if ← (rt.closing.get : BaseIO Bool) then return false
  let step := State.pump s
  if step.actions.isEmpty then return false
  if ← (rt.closing.get : BaseIO Bool) then return false
  enact rt step
  return true

/-- The test hook throws before the event is applied. The event is
answered first, so the waiter does not stay parked. -/
private def takeTestFault (rt : Runtime) (ev : Event) : Async Unit := do
  let some hooks := rt.hooks | return
  if ← hooks.forceInvariant.get then
    releaseQueued rt ev
    throwInvariant .sendInFlight
  if ← hooks.forceMissingPort.get then
    releaseQueued rt ev
    discard <| requirePort rt 0

private def teardownStarted (rt : Runtime) : BaseIO Bool :=
  rt.teardownStarted.get

/-- Store EOF or a reader fault when complete frames remain. The caller
does not pump after a `true` result. -/
private def deferTerminal (rt : Runtime) (ev : Event) : Async Bool := do
  let s ← (rt.state.get : BaseIO State)
  let closing ← (rt.closing.get : BaseIO Bool)
  let hold := s.cause.isRunning && s.parser.hasComplete && !closing
  match ev with
  | .ended =>
    if hold then
      rt.deferredTerminal.set (some .ended)
      return true
    return false
  | .readerFault e =>
    if hold then
      rt.deferredTerminal.set (some (.readerFault e))
      return true
    return false
  | _ => return false

/-- The event step's effect on the rest of this turn. -/
private structure TurnBudget where
  /-- `feed` already took the parser budget. -/
  spent : Bool
  /-- A terminal observation forbids the outbound chunk. -/
  suppressChunk : Bool

/-- Apply one event. A byte slice that `feed` accepts spends the budget.
Deferring EOF or a reader fault does not, and it forbids the chunk. -/
private def applyEvent (rt : Runtime) (ev : Event) : Async TurnBudget := do
  if ← deferTerminal rt ev then
    return { spent := false, suppressChunk := true }
  takeTestFault rt ev
  let mayPump ← dispatch rt ev
  let spent :=
    match ev with
    | .bytes _ => mayPump
    | _ => false
  return { spent, suppressChunk := !mayPump }

/-- The budget and the chunk that follow the event. A spent budget is
not taken again. A suppressed chunk is not sent. -/
private def completeTurn (rt : Runtime) (turn : TurnBudget) : Async Unit := do
  if ← (teardownStarted rt : BaseIO Bool) then return
  if !(← (rt.state.get : BaseIO State)).cause.isRunning then return
  if ← (rt.closing.get : BaseIO Bool) then return
  if !turn.spent && (← (rt.state.get : BaseIO State)).parser.hasComplete then
    pullOnce rt
  if turn.suppressChunk || (← rt.deferredTerminal.get).isSome then return
  if ← (teardownStarted rt : BaseIO Bool) then return
  if !(← (rt.state.get : BaseIO State)).cause.isRunning then return
  if ← (rt.closing.get : BaseIO Bool) then return
  if (← rt.deferredTerminal.get).isSome then return
  discard <| pumpOne rt

/-- Claim the stored cause once no complete frame remains. A close
request that is already set claims owner close instead. -/
private def applyDeferred (rt : Runtime) : Async Unit := do
  let some d ← rt.deferredTerminal.get | return
  rt.deferredTerminal.set none
  let s ← (rt.state.get : BaseIO State)
  if !s.cause.isRunning then return
  if ← (rt.closing.get : BaseIO Bool) then
    performClose rt
    return
  match d with
  | .ended => enact rt (State.inboundEnd s)
  | .readerFault e => enact rt (State.claim s (.readerFault e))

/-- One deferred turn. Answer one caller event and take one budget.
`feed` of a queued byte slice is that budget. No chunk is sent. The
first stored cause stays until no complete frame remains. -/
private def runDeferredTurn (rt : Runtime) : Async Unit := do
  if !(← (rt.state.get : BaseIO State)).parser.hasComplete then
    applyDeferred rt
    return
  if ← (rt.closing.get : BaseIO Bool) then
    rt.deferredTerminal.set none
    performClose rt
    return
  let spent ← match ← (rt.events.tryRecv : BaseIO (Option Event)) with
    | none => pure false
    | some ev =>
      match ev with
      | .bytes chunk =>
        feed rt chunk
        pure true
      | .ended | .readerFault _ =>
        -- The first terminal stays in the cell.
        pure false
      | _ =>
        releaseQueued rt ev
        noteOpenFrames rt
        pure false
  if ← (teardownStarted rt : BaseIO Bool) then return
  if !(← (rt.state.get : BaseIO State)).cause.isRunning then return
  if ← (rt.closing.get : BaseIO Bool) then
    rt.deferredTerminal.set none
    performClose rt
    return
  if !spent && (← (rt.state.get : BaseIO State)).parser.hasComplete then
    pullOnce rt

/-- Run the event step, then the same turn's budget and chunk. -/
private def turnOn (rt : Runtime) (ev : Option Event) : Async Unit := do
  match ev with
  | some ev => completeTurn rt (← applyEvent rt ev)
  | none => completeTurn rt { spent := false, suppressChunk := false }

private def ownerLoop (rt : Runtime) : Async Unit := do
  repeat
    if ← (teardownStarted rt : BaseIO Bool) then break
    let s ← (rt.state.get : BaseIO State)
    if !s.cause.isRunning then
      if !(← (teardownStarted rt : BaseIO Bool)) then
        throw <| IO.userError "mux: session ended without teardown"
      break
    if (← rt.deferredTerminal.get).isSome then
      runDeferredTurn rt
      continue
    match ← (rt.events.tryRecv : BaseIO (Option Event)) with
    | some ev => turnOn rt (some ev)
    | none =>
      if ← (rt.events.isClosed : BaseIO Bool) then
        if ← (rt.closing.get : BaseIO Bool) then
          performClose rt
        else if (← (rt.state.get : BaseIO State)).cause.isRunning then
          throw <| IO.userError "mux: reader ended without a terminal event"
        break
      else if ← (rt.closing.get : BaseIO Bool) then
        performClose rt
      else if s.parser.hasComplete then
        turnOn rt none
      else if ← pumpOne rt then
        pure ()
      else
        match ← rt.events.recv with
        | none => continue
        | some ev => turnOn rt (some ev)

/-- Keep the first owner error. Cleanup runs after this store, and
the rethrow uses the same `IO.Error`. -/
private def keepOwnerFault (rt : Runtime) (e : IO.Error) : BaseIO Unit := do
  rt.ownerFault.update fun kept => kept <|> some e

private def owner (rt : Runtime) : Async Unit := do
  try
    ownerLoop rt
  catch e =>
    keepOwnerFault rt e
    teardownOnExit rt
    throw e

/-! ## Reader -/

private def postSlices (rt : Runtime) (chunk : ByteArray) : Async Bool := do
  let mut i := 0
  while i < chunk.size do
    let j := min chunk.size (i + testPayloadCap)
    match ← rt.events.send (.bytes (chunk.extract i j)) with
    | .ok () =>
      noteAccepted rt
      i := j
    | .error _ => return false
  return true

private def reader (rt : Runtime) (leftover : ByteArray) : Async Unit := do
  try
    if !(← postSlices rt leftover) then return
    repeat
      match ← rt.conn.read with
      | none =>
        match ← rt.events.send .ended with
        | .ok () => noteAccepted rt
        | .error _ => pure ()
        break
      | some chunk =>
        if !(← postSlices rt chunk) then break
  catch e =>
    match ← rt.events.send (.readerFault e) with
    | .ok () => noteAccepted rt
    | .error _ => pure ()

/-! ## Session surface -/

private def openStream (rt : Runtime) (_id : ProtocolId) :
    ExceptT Error Async Streams.Stream := do
  match ← rt.livePermits.recv with
  | none => throw closedError
  | some _ =>
    let reply ← Chan.new 1
    match ← rt.events.send (.openLocal reply) with
    | .error _ =>
      returnLivePermit rt
      throw closedError
    | .ok () =>
      noteAccepted rt
      match ← reply.recv with
      | some (.ok stream) => return stream
      | some (.error e) => throw e
      | none => throw closedError

private def accept (rt : Runtime) : Async (Option Streams.Stream) := do
  match ← rt.acceptQ.recv with
  | none => return none
  | some stream =>
    returnAcceptPermit rt
    return some stream

private def close (rt : Runtime) : IO Unit := do
  -- The flag is the request. `markClosing` waits until owner close wins.
  rt.closing.set true
  rt.conn.closeQuietly
  rt.events.close

/-- `TaskSet.joinAll` hands its task error to one join. The stored
owner error stays, so every join throws that same `IO.Error`. A
connection fault and a protocol error still come from `Outcome`. -/
private def join (rt : Runtime) : Async (Except Error Unit) := do
  let fromTasks ← try
    rt.tasks.joinAll
    pure (none : Option IO.Error)
  catch e =>
    pure (some e)
  match ← (rt.ownerFault.get : BaseIO (Option IO.Error)) with
  | some e => throw e
  | none =>
    match fromTasks with
    | some e => throw e
    | none => rt.outcome.answer

private def startRuntime (role : Role) (conn : Streams.Connection)
    (leftover : ByteArray) (hooks : Option TestHooks) : Async MuxSession := do
  let livePermits ← Chan.new State.liveStreamCap
  preload livePermits State.liveStreamCap
  let acceptPermits ← Chan.new State.acceptBacklogCap
  preload acceptPermits State.acceptBacklogCap
  let events ← Chan.new eventChannelCap
  let acceptQ ← Chan.new State.acceptBacklogCap
  let writes ← Streams.Completions.new
  let rt : Runtime := {
    conn
    events
    livePermits
    acceptPermits
    acceptQ
    writes
    ports := ← OnceRef.new ({} : Std.HashMap UInt32 Port)
    state := ← OnceRef.new (State.empty role)
    outcome := ← Outcome.new
    tasks := ← TaskSet.new
    closing := ← OnceRef.new false
    teardownStarted := ← OnceRef.new false
    ownerFault := ← OnceRef.new (none : Option IO.Error)
    deferredTerminal := ← OnceRef.new (none : Option DeferredTerminal)
    pendingOpen := ← OnceRef.new none
    hooks }
  rt.tasks.spawn (reader rt leftover)
  rt.tasks.spawn (owner rt)
  return {
    openStream := openStream rt
    accept := accept rt
    close := close rt
    join := join rt }

/-- The reader and the owner for `role` on `conn`. `leftover` is the
negotiation suffix. The tasks belong to the session `TaskSet`. -/
def start (role : Role) (conn : Streams.Connection) (leftover : ByteArray := .empty) :
    Async MuxSession :=
  startRuntime role conn leftover none

/-- `start` with test refs. `Libp2p.Mux` does not import this function.
The owner reads a hook only through this entry. -/
def startWithHooks (role : Role) (conn : Streams.Connection)
    (leftover : ByteArray := .empty) (hooks : TestHooks) : Async MuxSession :=
  startRuntime role conn leftover (some hooks)

end Libp2p.Mux.Test.Session
