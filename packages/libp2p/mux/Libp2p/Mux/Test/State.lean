import Libp2p.Mux.Test.Wire
import Libp2p.Core
import Streams

/-!
# Pure test-session state

The owner loop is the only stepper of this state
(`packages/libp2p/mux/docs/ARCHITECTURE.md`, stream ids, stream
lifetime, scheduling and writes, terminal causes). The state is pure.
It holds the parser, the two id counters, the live table, one
unacknowledged send, the admitted writes, and the terminal cause.

A transition returns the next state and an ordered list of actions.
`sendFrame` and `sendChunk` are intents. `ackSend` commits a successful
connection write. `failSend` claims the writer fault with the caught
`IO.Error` and releases that send's resources once. `setPort` precedes
`closeWritePermits` for the same id. `closeInbox` stays a separate
action. An acknowledgement or a scheduler step that breaks an
internal invariant returns `InvariantError` and leaves the caller's
state in place. The shell throws `InvariantError.toIOError`.

This module does not read or write a connection. It stores no channel,
task, atomic cell, waiting caller, or `Stream`.

A local open already holds one live permit. A nonempty write already
holds one write permit and its completion tag. An empty write has a
tag and no write permit. A remote open is classified before either
permit is reserved. `pull` returns frames and does not admit them.
The counters below name the caps the runtime preloads. This state
does not keep the callers that are still waiting for a permit.

`UInt32.size` is `2^32`, the exclusive bound of `UInt32.ofNatLT`.
The last initiator id is `UInt32.size - 1`. The last responder id is
`UInt32.size - 2`. Those values are not `UInt32.size`.
-/

set_option autoImplicit false

namespace Libp2p.Mux.Test.State

open Libp2p.Core
open Libp2p.Mux.Test.Wire

/-! ## Caps and ids -/

/-- Live streams held at one time. The runtime permit channel preloads
this many tokens. -/
def liveStreamCap : Nat := 32

/-- Inbound streams waiting for `accept`. The runtime accept channel
and its permit source use this capacity. This state enqueues only
when the shell has reserved an accept permit. -/
def acceptBacklogCap : Nat := 16

/-- Writes already admitted on one stream. The fifth writer waits
outside this state. A call past this cap is an invariant guard. -/
def admittedWriteCap : Nat := 4

/-- `true` when `n` is odd. -/
def oddNat (n : Nat) : Bool :=
  n % 2 == 1

/-- Initiator local ids are odd. Responder local ids are even. -/
def localIsOdd (role : Role) : Bool :=
  match role with
  | .initiator => true
  | .responder => false

/-- Remote ids use the other parity. -/
def remoteIsOdd (role : Role) : Bool :=
  !localIsOdd role

/-- The first local id of `role`. -/
def firstLocal (role : Role) : Nat :=
  match role with
  | .initiator => 1
  | .responder => 2

/-- The first remote id of `role`. -/
def firstRemote (role : Role) : Nat :=
  match role with
  | .initiator => 2
  | .responder => 1

/-- Convert `next` only when it is below `UInt32.size`, nonzero, and of
the requested parity. The caller adds two in `Nat` after a `some`. -/
def issueId (next : Nat) (odd : Bool) : Option UInt32 :=
  if h : next < UInt32.size ∧ next ≠ 0 then
    if oddNat next == odd then
      some (UInt32.ofNatLT next h.left)
    else
      none
  else
    none

/-! ## Terminal cause -/

/-- The first cause that leaves `running`. A reader or writer fault
stores the `IO.Error` the shell passes to `Outcome.recordFault`. -/
inductive Cause where
  | running
  | ownerClose
  | connectionEnd
  | readerFault (error : IO.Error)
  | writerFault (error : IO.Error)
  | protocol (error : Error)

namespace Cause

/-- `true` while no claim has won. -/
def isRunning : Cause → Bool
  | .running => true
  | _ => false

/-- The `IO.Error` a winning fault gives to `Outcome.recordFault`.
Owner close, connection end, and protocol failure carry none. -/
def fault? : Cause → Option IO.Error
  | .readerFault e | .writerFault e => some e
  | _ => none

/-- `true` when `c` is the protocol error `e`. -/
def isProtocol (c : Cause) (e : Error) : Bool :=
  match c with
  | .protocol err => err == e
  | _ => false

end Cause

/-- Protocol details this state produces. The wording is local. -/
def protocolZero : Error := .protocol "zero id"

/-- A remote id uses the local parity. -/
def protocolParity : Error := .protocol "wrong parity"

/-- The id is already live, or it is retired. -/
def protocolDuplicate : Error := .protocol "duplicate open"

/-- The id is above the next remote id. -/
def protocolFuture : Error := .protocol "future open"

/-- A data, fin, or reset id was never opened. -/
def protocolUnknown : Error := .protocol "unknown id"

/-- The connection ended inside a partial header or body. -/
def protocolPartial : Error := .protocol "partial frame"

/-- `Parser.drain` rejected the buffered bytes. -/
def protocolMalformed : Error := .protocol "malformed frame"

/-- The next local id does not fit in `UInt32`. The session stays up. -/
def protocolExhausted : Error := .protocol "id exhausted"

/-- Owner close, connection end, or an IO fault ended the open. -/
def closedError : Error := .closed "closed"

/-! ## Write mode -/

/-- The local write direction of one stream.

`applyReset` replaces `open` and `halfClosed`. `reset` stays `reset`.
`sessionClosed` stays `sessionClosed`, so a later reset does not
replace a session close. `applySessionClose` does the opposite:
a reset handle stays reset when the session closes. -/
inductive WriteMode where
  | open
  | halfClosed
  | reset
  | sessionClosed
  deriving DecidableEq, Repr, BEq

namespace WriteMode

/-- Reset replaces an open or half-closed write. A repeated reset stays
reset. A session close is terminal. -/
def applyReset : WriteMode → WriteMode
  | .open | .halfClosed => .reset
  | .reset => .reset
  | .sessionClosed => .sessionClosed

/-- Session closure replaces an open or half-closed write. A reset
handle continues to report reset. -/
def applySessionClose : WriteMode → WriteMode
  | .open | .halfClosed => .sessionClosed
  | .reset => .reset
  | .sessionClosed => .sessionClosed

/-- Bytes and fin may still leave this direction. -/
def sends : WriteMode → Bool
  | .open | .halfClosed => true
  | .reset | .sessionClosed => false

end WriteMode

/-- The remote write direction, as this session observes it. -/
inductive ReadMode where
  | open
  | fin
  deriving DecidableEq, Repr, BEq

/-- The completion-table answer for one write. This is the value
`Streams.Completions.resolve` stores. -/
def writeAnswer (mode : WriteMode) : Except Streams.Error Unit :=
  match mode with
  | .open => .ok ()
  | .reset => .error .reset
  | .halfClosed | .sessionClosed => .error .closed

/-- One admitted logical write. `tag` is the `Nat` from
`Streams.Completions.register`. `sent` counts bytes whose send has
been acknowledged. Chunks of one tag stay in order. -/
structure Admitted where
  tag : Nat
  bytes : ByteArray
  sent : Nat
  deriving Inhabited

/-! ## Actions and send intents -/

/-- A writer-visible port mode the shell publishes before it closes
the write-permit channel. `Streams.Error` also admits `timeout`, and
it uses one `closed` arm for every non-reset end, so half-close and
session close stay distinct here. A clean close and a capacity
refusal emit no `setPort`. -/
inductive PortEnd where
  | halfClosed
  | reset
  | sessionClosed
  deriving DecidableEq, Repr, BEq

/-- A connection write the shell has not acknowledged.
The rest of the state stays at its pre-send values until `ackSend`
or `failSend`. `failSend` stores the caught `IO.Error` and releases
the resources of this write once. -/
inductive Outbound where
  | openStream (id : UInt32) (frame : Frame)
  | refuse (id : UInt32) (frame : Frame) (gotLive : Bool) (gotAccept : Bool)
  | reset (id : UInt32) (frame : Frame)
  | fin (id : UInt32) (frame : Frame) (turn : Nat)
  | chunk (id : UInt32) (tag : Nat) (raw : ByteArray) (turn : Nat)

/-- Work the shell performs, in list order.
`sendFrame` and `sendChunk` are intents. `ackSend` emits the
success-only resolutions and permit returns. `enqueueAccept` transfers
one accept reservation into the runtime accept envelope. The consumer
of that envelope returns the permit. `setPort` precedes
`closeWritePermits` for the same id. `closeInbox` is the read side.
The `terminal` cause's `Cause.fault?` is the `IO.Error` passed to
`Outcome.recordFault`. -/
inductive Action where
  /-- Send one control frame. The loop is the only connection writer. -/
  | sendFrame (frame : Frame)
  /-- Send the next chunk of the write named by `tag`. The chunk is
  nonempty and at most `testPayloadCap` bytes. -/
  | sendChunk (id : UInt32) (tag : Nat) (bytes : ByteArray)
  /-- Complete a local open. `.ok` carries the issued id. -/
  | resolveOpen (result : Except Error UInt32)
  /-- Complete the write named by `tag`. -/
  | resolveWrite (tag : Nat) (result : Except Streams.Error Unit)
  /-- Return one live-stream permit. Each token is returned once. -/
  | returnLivePermit
  /-- Return one write permit to `id`. -/
  | returnWritePermit (id : UInt32)
  /-- Return one accept-backlog permit reserved for `id`. -/
  | returnAcceptPermit (id : UInt32)
  /-- Publish the writer-visible mode of `id`. This precedes
  `closeWritePermits` for the same id. -/
  | setPort (id : UInt32) (reason : PortEnd)
  /-- Close the write-permit channel of `id`. A repeat emits nothing. -/
  | closeWritePermits (id : UInt32)
  /-- Queue one inbound payload. -/
  | deliver (id : UInt32) (bytes : ByteArray)
  /-- Transfer one accepted stream into the runtime accept envelope.
  The envelope owns the accept reservation. -/
  | enqueueAccept (id : UInt32)
  /-- Close one stream inbox. -/
  | closeInbox (id : UInt32)
  /-- Close the accept channel. Queued envelopes stay readable. This
  step does not return their reservations. -/
  | closeAccept
  /-- The claim that left `running`. The runtime applies `Outcome`. -/
  | terminal (cause : Cause)

/-! ## Live streams and session state -/

/-- One live stream. Retirement is not stored. An id is retired when
it has its opener's parity, lies below that opener's high water, and
is absent from the live table. Zero is never retired, because zero is
never issued. The accept reservation is not a field of this record. -/
structure Live where
  write : WriteMode
  read : ReadMode
  admitted : Array Admitted
  finPending : Bool
  finSent : Bool
  livePermitHeld : Bool
  inboxOpen : Bool
  /-- `true` until the first `closeWritePermits` for this stream. -/
  writePermitsOpen : Bool

/-- A new local stream. It holds its live permit. Its write-permit
channel is still open. -/
def freshLive : Live where
  write := .open
  read := .open
  admitted := #[]
  finPending := false
  finSent := false
  livePermitHeld := true
  inboxOpen := true
  writePermitsOpen := true

/-- The owner-loop state. `nextLocal` and `nextRemote` are `Nat` high
water marks. They step by two and do not wrap through `UInt32`.
`outbound` is the one unacknowledged connection write. The accept
backlog lives in the runtime channel, not in this record. -/
structure State where
  role : Role
  parser : Parser
  nextLocal : Nat
  nextRemote : Nat
  live : Std.HashMap UInt32 Live
  outbound : Option Outbound
  cause : Cause
  order : Array UInt32
  turnIndex : Nat

/-- The result of one transition. -/
structure Step where
  state : State
  actions : List Action

/-- An internal invariant failure. The shell throws `toIOError`.
A peer protocol error is `Core.Error`. A connection fault is the
`IO.Error` stored on the terminal cause. -/
inductive InvariantError where
  | noOutbound
  | sendAfterTerminal
  | missingStream (id : UInt32)
  | emptyWriteQueue (id : UInt32)
  | writeTagMismatch (id : UInt32) (intentTag : Nat) (queueTag : Nat)
  | noRemainingChunk (id : UInt32)
  | openAlreadyLive (id : UInt32)
  | resetUnchanged (id : UInt32)
  | sendInFlight
  deriving DecidableEq, Repr, BEq

/-- The diagnostic the shell throws. The text names the case and any
stream id or completion tag the case carries. -/
def InvariantError.message : InvariantError → String
  | .noOutbound => "mux: no outbound send"
  | .sendAfterTerminal => "mux: send completion after the session ended"
  | .missingStream id => s!"mux: missing stream {id}"
  | .emptyWriteQueue id => s!"mux: empty write queue {id}"
  | .writeTagMismatch id intentTag queueTag =>
    s!"mux: write tag mismatch {id} intent {intentTag} queue {queueTag}"
  | .noRemainingChunk id => s!"mux: no remaining chunk {id}"
  | .openAlreadyLive id => s!"mux: open already live {id}"
  | .resetUnchanged id => s!"mux: reset unchanged {id}"
  | .sendInFlight => "mux: send in flight"

/-- The `IO.Error` the shell throws for `e`. -/
def InvariantError.toIOError (e : InvariantError) : IO.Error :=
  IO.userError e.message

namespace State

/-- A session with empty tables and the first id of `role`. -/
def empty (role : Role) : State where
  role := role
  parser := Parser.empty
  nextLocal := firstLocal role
  nextRemote := firstRemote role
  live := {}
  outbound := none
  cause := .running
  order := #[]
  turnIndex := 0

/-- Replace the parser. The runtime feeds slices before it stores one. -/
def setParser (s : State) (p : Parser) : State :=
  { s with parser := p }

private def setLive (s : State) (id : UInt32) (st : Live) : State :=
  { s with live := s.live.insert id st }

private def insertLive (s : State) (id : UInt32) (st : Live) : State :=
  let s := s.setLive id st
  if s.order.any (· == id) then
    s
  else
    { s with order := s.order.push id }

private def eraseLive (s : State) (id : UInt32) : State :=
  { s with
    live := s.live.erase id
    order := s.order.filter (· != id)
    turnIndex := 0 }

/-- `true` when `id` is retired. Zero is not retired. -/
def retired (s : State) (id : UInt32) : Bool :=
  if id == 0 then
    false
  else if (s.live.get? id).isSome then
    false
  else
    let n := id.toNat
    let odd := oddNat n
    (odd == localIsOdd s.role && n < s.nextLocal) ||
      (odd == remoteIsOdd s.role && n < s.nextRemote)

/-- The local write mode of a live id. Absence is not a mode. A retired
id has no write mode here. The port cell answers an old handle. -/
def writeMode? (s : State) (id : UInt32) : Option WriteMode :=
  (s.live.get? id).map fun st => st.write

/-- The remote write mode of a live id. -/
def readMode? (s : State) (id : UInt32) : Option ReadMode :=
  (s.live.get? id).map fun st => st.read

/-- Admitted writes stored for `id`. -/
def admittedCount (s : State) (id : UInt32) : Nat :=
  match s.live.get? id with
  | some st => st.admitted.size
  | none => 0

/-- Admitted payloads, oldest first. -/
def admittedBytes (s : State) (id : UInt32) : List ByteArray :=
  match s.live.get? id with
  | some st => st.admitted.toList.map fun a => a.bytes
  | none => []

/-! ## Frames -/

private def control (k : Kind) (id : UInt32) : Option Frame :=
  if hk : k = Kind.data then
    none
  else if hid : id = 0 then
    none
  else
    some (Frame.ofControl k id hk hid)

private def chunkOf (a : Admitted) : Option (ByteArray × Admitted) :=
  if a.sent < a.bytes.size then
    -- `size - sent` is at least one, and the cap is at least one,
    -- so the extracted chunk is nonempty.
    let n := min testPayloadCap (a.bytes.size - a.sent)
    let raw := a.bytes.extract a.sent (a.sent + n)
    some (raw, { a with sent := a.sent + n })
  else
    none

/-! ## Session seal -/

private def sealOne (id : UInt32) (st : Live) : Live × List Action :=
  let mode := WriteMode.applySessionClose st.write
  let admission :=
    if mode == .sessionClosed then
      [Action.setPort id .sessionClosed] ++
        (if st.writePermitsOpen then [Action.closeWritePermits id] else [])
    else
      []
  let writeActions :=
    if mode == .sessionClosed then
      st.admitted.toList.map (fun a => Action.resolveWrite a.tag (.error .closed)) ++
        st.admitted.toList.map (fun _ => Action.returnWritePermit id)
    else
      []
  let inbox := if st.inboxOpen then [Action.closeInbox id] else []
  let permit := if st.livePermitHeld then [Action.returnLivePermit] else []
  let st : Live := {
    st with
    write := mode
    admitted := if mode == .sessionClosed then #[] else st.admitted
    finPending := false
    livePermitHeld := false
    inboxOpen := false
    writePermitsOpen := false }
  (st, admission ++ writeActions ++ inbox ++ permit)

private def sealAll (s : State) : State × List Action :=
  s.order.foldl (fun acc id =>
    let (s, acts) := acc
    match s.live.get? id with
    | none => (s, acts)
    | some st =>
      let (st, more) := sealOne id st
      (s.setLive id st, acts ++ more)) (s, [])

/-- Permits acquired for one remote open and not yet transferred. -/
private def releaseOpen (id : UInt32) (gotLive gotAccept : Bool) : List Action :=
  (if gotLive then [Action.returnLivePermit] else []) ++
    (if gotAccept then [Action.returnAcceptPermit id] else [])

/-- Release a send that never entered the live table. A chunk, fin, or
local reset still sits on its live stream, and seal releases that
stream. -/
private def releaseOutbound (s : State) : State × List Action :=
  match s.outbound with
  | none => (s, [])
  | some (.openStream _ _) =>
    ({ s with outbound := none },
      [Action.resolveOpen (.error closedError), Action.returnLivePermit])
  | some (.refuse id _ gotLive gotAccept) =>
    ({ s with outbound := none }, releaseOpen id gotLive gotAccept)
  | some (.reset ..) | some (.fin ..) | some (.chunk ..) =>
    ({ s with outbound := none }, [])

/-- The first claim out of `running` wins. A later claim leaves the
winner and the action list unchanged. An in-flight open or refusal is
released here. `closeAccept` does not return a reservation that
`enqueueAccept` already transferred. -/
def claim (s : State) (c : Cause) : Step :=
  match s.cause, c with
  | .running, .running => ⟨s, []⟩
  | .running, c =>
    let (s, extra) := releaseOutbound s
    let (s, acts) := sealAll s
    ⟨{ s with cause := c }, extra ++ acts ++ [Action.closeAccept, Action.terminal c]⟩
  | _, _ => ⟨s, []⟩

/-! ## Send acknowledgement -/

private def advanceTurn (s : State) (i : Nat) : State :=
  let n := s.order.size
  if n = 0 then
    { s with turnIndex := 0 }
  else
    { s with turnIndex := (i + 1) % n }

private def commitChunk (s : State) (id : UInt32) (tag : Nat) (turn : Nat) :
    Except InvariantError Step :=
  match s.live.get? id with
  | none => .error (.missingStream id)
  | some st =>
    if st.admitted.isEmpty then
      .error (.emptyWriteQueue id)
    else
      let a := st.admitted[0]!
      if a.tag != tag then
        .error (.writeTagMismatch id tag a.tag)
      else
        match chunkOf a with
        | none => .error (.noRemainingChunk id)
        | some (_, a') =>
          let done := a'.bytes.size ≤ a'.sent
          let rest := st.admitted.extract 1 st.admitted.size
          let admitted := if done then rest else #[a'] ++ rest
          let st := { st with admitted }
          let s := advanceTurn ({ s with outbound := none }.setLive id st) turn
          let tail :=
            if done then
              [Action.resolveWrite tag (.ok ()), Action.returnWritePermit id]
            else
              []
          .ok ⟨s, tail⟩

/-- Finish a reset whose frame has succeeded, or a received reset,
which sends nothing. The accept envelope is left with its consumer.
A missing stream, or a mode that cannot change, returns
`InvariantError` and leaves `s` unchanged. -/
private def commitReset (s : State) (id : UInt32) : Except InvariantError Step :=
  match s.live.get? id with
  | none => .error (.missingStream id)
  | some st =>
    let mode := WriteMode.applyReset st.write
    if mode == st.write then
      .error (.resetUnchanged id)
    else
      let s :=
        match s.outbound with
        | some (.reset i _) => if i == id then { s with outbound := none } else s
        | _ => s
      let resolves := st.admitted.toList.map fun a =>
        Action.resolveWrite a.tag (.error .reset)
      let permits := st.admitted.toList.map fun _ => Action.returnWritePermit id
      let admission :=
        [Action.setPort id .reset] ++
          (if st.writePermitsOpen then [Action.closeWritePermits id] else [])
      let inbox := if st.inboxOpen then [Action.closeInbox id] else []
      let live := if st.livePermitHeld then [Action.returnLivePermit] else []
      .ok ⟨eraseLive s id, admission ++ resolves ++ permits ++ inbox ++ live⟩

private def commitFin (s : State) (id : UInt32) (turn : Nat) :
    Except InvariantError Step :=
  match s.live.get? id with
  | none => .error (.missingStream id)
  | some st =>
    let s := { s with outbound := none }
    let st : Live := { st with finPending := false, finSent := true }
    if st.read == .fin then
      let permit := if st.livePermitHeld then [Action.returnLivePermit] else []
      .ok ⟨eraseLive (s.setLive id st) id, permit⟩
    else
      .ok ⟨advanceTurn (s.setLive id st) turn, []⟩

private def commit (s : State) (intent : Outbound) : Except InvariantError Step :=
  match intent with
  | .openStream id _ =>
    match s.live.get? id with
    | some _ => .error (.openAlreadyLive id)
    | none =>
      let s := insertLive { s with outbound := none, nextLocal := s.nextLocal + 2 } id freshLive
      .ok ⟨s, [Action.resolveOpen (.ok id)]⟩
  | .refuse id _ gotLive gotAccept =>
    .ok ⟨{ s with outbound := none, nextRemote := s.nextRemote + 2 },
      releaseOpen id gotLive gotAccept⟩
  | .reset id _ => commitReset s id
  | .fin id _ turn => commitFin s id turn
  | .chunk id tag _ turn => commitChunk s id tag turn

/-- Commit the in-flight send. The connection write has succeeded.
No send in flight, and a send that outlives `running`, return
`InvariantError`. The caller keeps `s`. -/
def ackSend (s : State) : Except InvariantError Step :=
  match s.outbound with
  | none => .error .noOutbound
  | some intent =>
    if s.cause.isRunning then
      commit s intent
    else
      .error .sendAfterTerminal

/-- The connection write threw `e`. The writer fault wins if the
session is still running, and this step releases the in-flight send
once. A later claim adds no second release. No send in flight, and a
send that outlives `running`, return `InvariantError`. The caller
keeps `s`. -/
def failSend (s : State) (e : IO.Error) : Except InvariantError Step :=
  match s.outbound, s.cause.isRunning with
  | none, _ => .error .noOutbound
  | some _, false => .error .sendAfterTerminal
  | some _, true => .ok (claim s (.writerFault e))

/-! ## Opens -/

private def openError (s : State) : Error :=
  match s.cause with
  | .protocol e => e
  | _ => closedError

/-- Returned to the opener when `openLocal` runs during a send. -/
def busyOpen : Error :=
  .closed "send in flight"

/-- Issue one local id. The live permit is already held. The open
frame is an intent: `nextLocal` and the live table change in `ackSend`.
No id is taken when the session is finished or `nextLocal` does not
convert. A call during a send already holds that opener's permit, so
it returns the permit and completes the opener with `busyOpen`. The
in-flight send stays. -/
def openLocal (s : State) : Step :=
  if !s.cause.isRunning then
    ⟨s, [Action.resolveOpen (.error (openError s)), Action.returnLivePermit]⟩
  else if s.outbound.isSome then
    ⟨s, [Action.resolveOpen (.error busyOpen), Action.returnLivePermit]⟩
  else
    match issueId s.nextLocal (localIsOdd s.role) with
    | none =>
      ⟨s, [Action.resolveOpen (.error protocolExhausted), Action.returnLivePermit]⟩
    | some id =>
      match control Kind.open id with
      | none =>
        ⟨s, [Action.resolveOpen (.error protocolExhausted), Action.returnLivePermit]⟩
      | some frame =>
        ⟨{ s with outbound := some (.openStream id frame) }, [Action.sendFrame frame]⟩

/-- Whether `id` may be admitted. The shell calls this before it reserves
a live permit or an accept permit. A failure here consumes neither. -/
def classifyRemote (s : State) (id : UInt32) : Except Error Unit :=
  if id == 0 then
    .error protocolZero
  else if oddNat id.toNat != remoteIsOdd s.role then
    .error protocolParity
  else if (s.live.get? id).isSome then
    .error protocolDuplicate
  else if retired s id then
    .error protocolDuplicate
  else if id.toNat > s.nextRemote then
    .error protocolFuture
  else
    .ok ()

private def failRemote (s : State) (id : UInt32) (e : Error) (gotLive gotAccept : Bool) : Step :=
  let sealed := claim s (.protocol e)
  ⟨sealed.state, releaseOpen id gotLive gotAccept ++ sealed.actions⟩

/-- Commit one remote open that `classifyRemote` has already accepted.
`gotLive` and `gotAccept` are the permits the shell reserved. The
shell passes `gotAccept` only when the accept channel has a free
slot. Both install the stream and transfer the accept reservation
into the accept envelope. Any other valid open is a reset intent.
`ackSend` retires that id and returns the permits the refusal still
holds. An id that fails classification advances nothing. A call
while a send is open returns `sendInFlight` and does not take
`gotLive` or `gotAccept`. A correct shell does not make that call.
If it does, the caller still owns those permits and releases them
while the shell throws `InvariantError.toIOError`. -/
def openRemote (s : State) (id : UInt32) (gotLive gotAccept : Bool) :
    Except InvariantError Step :=
  if !s.cause.isRunning then
    .ok ⟨s, releaseOpen id gotLive gotAccept⟩
  else if s.outbound.isSome then
    .error .sendInFlight
  else
    match classifyRemote s id with
    | .error e => .ok (failRemote s id e gotLive gotAccept)
    | .ok () =>
      if gotLive && gotAccept then
        let s := insertLive { s with nextRemote := s.nextRemote + 2 } id freshLive
        .ok ⟨s, [Action.enqueueAccept id]⟩
      else
        match control Kind.reset id with
        | none => .ok ⟨s, releaseOpen id gotLive gotAccept⟩
        | some frame =>
          .ok ⟨{ s with outbound := some (.refuse id frame gotLive gotAccept) },
            [Action.sendFrame frame]⟩

/-! ## Inbound frames -/

/-- Deliver or ignore one remote data payload. A call while a send is
open returns `sendInFlight`. A correct shell does not make that call. -/
def dataRemote (s : State) (id : UInt32) (payload : List Nat) :
    Except InvariantError Step :=
  if s.outbound.isSome then
    .error .sendInFlight
  else if !s.cause.isRunning then
    .ok ⟨s, []⟩
  else
    match s.live.get? id with
    | some st =>
      if st.read == .fin || !st.inboxOpen then
        .ok ⟨s, []⟩
      else
        .ok ⟨s, [Action.deliver id (Bytes.ofNatList payload)]⟩
    | none =>
      if retired s id then
        .ok ⟨s, []⟩
      else
        .ok (claim s (.protocol protocolUnknown))

/-- A received fin closes the remote write only. A second fin is ignored.
The live entry remains while the local fin is still unsent. An
accept reservation already transferred stays with its envelope. A
call while a send is open returns `sendInFlight`. A correct shell
does not make that call. -/
def finRemote (s : State) (id : UInt32) : Except InvariantError Step :=
  if s.outbound.isSome then
    .error .sendInFlight
  else if !s.cause.isRunning then
    .ok ⟨s, []⟩
  else
    match s.live.get? id with
    | some st =>
      if st.read == .fin then
        .ok ⟨s, []⟩
      else
        let close := if st.inboxOpen then [Action.closeInbox id] else []
        let st : Live := { st with read := .fin, inboxOpen := false }
        if st.finSent then
          let permit := if st.livePermitHeld then [Action.returnLivePermit] else []
          .ok ⟨eraseLive (s.setLive id st) id, close ++ permit⟩
        else
          .ok ⟨s.setLive id st, close⟩
    | none =>
      if retired s id then
        .ok ⟨s, []⟩
      else
        .ok (claim s (.protocol protocolUnknown))

/-- A local reset. The reset frame is an intent. Admitted writes, the
live permit, and the port cell change in `ackSend`. A second reset,
and a reset of `sessionClosed`, send nothing. A reset while a send
is open returns `sendInFlight`. A correct shell does not make that
call. The reset event stays queued until the send finishes. -/
def resetLocal (s : State) (id : UInt32) : Except InvariantError Step :=
  if s.outbound.isSome then
    .error .sendInFlight
  else
    match s.live.get? id with
    | none => .ok ⟨s, []⟩
    | some st =>
      if WriteMode.applyReset st.write == st.write then
        .ok ⟨s, []⟩
      else
        match control Kind.reset id with
        | none => .ok ⟨s, []⟩
        | some frame =>
          .ok ⟨{ s with outbound := some (.reset id frame) }, [Action.sendFrame frame]⟩

/-- A received reset. The id retires when it is live. No reset frame is
sent back, so the reset commits in this step. A retired id is ignored.
An unknown id is a protocol failure. The accept envelope stays with
its consumer. A reset while a send is open returns `sendInFlight`.
A correct shell does not make that call. -/
def resetRemote (s : State) (id : UInt32) : Except InvariantError Step :=
  if s.outbound.isSome then
    .error .sendInFlight
  else if !s.cause.isRunning then
    .ok ⟨s, []⟩
  else if (s.live.get? id).isSome then
    commitReset s id
  else if retired s id then
    .ok ⟨s, []⟩
  else
    .ok (claim s (.protocol (if id == 0 then protocolZero else protocolUnknown)))

/-- Apply one decoded data, fin, or reset frame. An open frame is not
admitted here. The shell classifies it, reserves permits, and calls
`openRemote`. A call while a send is open returns `sendInFlight`.
A correct shell does not make that call. -/
def apply (s : State) (f : Frame) : Except InvariantError Step :=
  if s.outbound.isSome then
    .error .sendInFlight
  else
    match f.kind with
    | .open => .ok ⟨s, []⟩
    | .data => dataRemote s f.streamId f.payload
    | .fin => finRemote s f.streamId
    | .reset => resetRemote s f.streamId

/-! ## Parser -/

/-- One parser budget. `frames` are not admitted. `actions` is empty,
or the single protocol claim when `drain` fails. A complete frame kept
past the budget stays in `state.parser`. -/
structure Pull where
  state : State
  frames : List Frame
  actions : List Action

/-- Take one parser budget. This does not read capacity and does not
commit a remote open. -/
def pull (s : State) : Pull :=
  if !s.cause.isRunning then
    { state := s, frames := [], actions := [] }
  else
    match s.parser.drain with
    | .error _ =>
      let step := claim s (.protocol protocolMalformed)
      { state := step.state, frames := [], actions := step.actions }
    | .ok (frames, p) =>
      { state := { s with parser := p }, frames, actions := [] }

/-- Select the end cause after the shell has pulled every complete frame.
A parser that still has a complete frame stays `running`. An empty gap
selects connection end. A partial header or body selects a protocol
failure. -/
def inboundEnd (s : State) : Step :=
  if !s.cause.isRunning || s.parser.hasComplete then
    ⟨s, []⟩
  else
    match s.parser.gap with
    | .empty => claim s .connectionEnd
    | .partialHeader | .partialBody => claim s (.protocol protocolPartial)

/-! ## Writes -/

/-- An empty write. `Stream.write` has already registered `tag`.
The write takes no write permit and enters no admitted queue.
`mode` is the port-cell mode the shell just read, so a retired reset
handle still resolves `reset`. -/
def writeEmpty (s : State) (tag : Nat) (mode : WriteMode) : Step :=
  ⟨s, [Action.resolveWrite tag (writeAnswer mode)]⟩

private def refuseWrite (s : State) (id : UInt32) (tag : Nat)
    (result : Except Streams.Error Unit) : Step :=
  ⟨s, [Action.resolveWrite tag result, Action.returnWritePermit id]⟩

/-- Store one nonempty write that already holds a write permit.
`tag` is that write's completion tag. An empty buffer is not a queued
write and takes no permit: the shell uses `writeEmpty` with the port
mode. The queue stops at `admittedWriteCap`. A further call is an
invariant guard. It is not stored, its tag resolves `closed`, and its
permit returns once. -/
def admitWrite (s : State) (id : UInt32) (tag : Nat) (bytes : ByteArray) : Step :=
  if bytes.isEmpty then
    match writeMode? s id with
    | some mode => ⟨s, [Action.resolveWrite tag (writeAnswer mode)]⟩
    | none => ⟨s, [Action.resolveWrite tag (.error .closed)]⟩
  else
    match s.live.get? id with
    | none =>
      refuseWrite s id tag (.error .closed)
    | some st =>
      if !s.cause.isRunning || st.write ≠ .open then
        let result :=
          match st.write with
          | .reset => writeAnswer .reset
          | .open | .halfClosed | .sessionClosed => writeAnswer .halfClosed
        refuseWrite s id tag result
      else if st.admitted.size ≥ admittedWriteCap then
        refuseWrite s id tag (.error .closed)
      else
        let st := { st with admitted := st.admitted.push { tag, bytes, sent := 0 } }
        ⟨s.setLive id st, []⟩

/-- Stop local admission. Admitted bytes stay queued. Fin is not sent
in this step. `pump` sends it after those bytes are gone. This step
publishes `halfClosed` and then closes the write-permit channel.
A second half-close emits neither. A fifth writer is not stored here.
The shell wakes it by performing those two actions in order. -/
def halfClose (s : State) (id : UInt32) : Step :=
  if !s.cause.isRunning then
    ⟨s, []⟩
  else
    match s.live.get? id with
    | none => ⟨s, []⟩
    | some st =>
      if st.write ≠ .open then
        ⟨s, []⟩
      else
        let permits :=
          if st.writePermitsOpen then [Action.closeWritePermits id] else []
        let st := {
          st with
          write := .halfClosed
          finPending := !st.finSent
          writePermitsOpen := false }
        ⟨s.setLive id st, [Action.setPort id .halfClosed] ++ permits⟩

/-! ## Outbound turn -/

private def queueDrained (st : Live) : Bool :=
  st.admitted.all fun a => a.bytes.size ≤ a.sent

private def emitData (s : State) (i : Nat) (id : UInt32) (st : Live) : Option Step :=
  if st.admitted.isEmpty then
    none
  else
    let a := st.admitted[0]!
    match chunkOf a with
    | none => none
    | some (raw, _) =>
      some ⟨{ s with outbound := some (.chunk id a.tag raw i) },
        [Action.sendChunk id a.tag raw]⟩

private def emitFin (s : State) (i : Nat) (id : UInt32) (st : Live) : Option Step :=
  if st.finPending && !st.finSent && queueDrained st && st.write == .halfClosed then
    match control Kind.fin id with
    | none => none
    | some frame =>
      some ⟨{ s with outbound := some (.fin id frame i) }, [Action.sendFrame frame]⟩
  else
    none

private def tryEmit (s : State) (i : Nat) : Option Step :=
  if hi : i < s.order.size then
    let id := s.order[i]
    match s.live.get? id with
    | none => none
    | some st =>
      if !WriteMode.sends st.write then
        none
      else
        match emitData s i id st with
        | some step => some step
        | none => emitFin s i id st
  else
    none

private def scan (s : State) (seen : Nat) : Step :=
  if seen < s.order.size then
    let n := s.order.size
    let i := (s.turnIndex + seen) % n
    match tryEmit s i with
    | some step => step
    | none => scan s (seen + 1)
  else
    ⟨s, []⟩
termination_by s.order.size - seen

/-- Emit one outbound intent, or one fin intent when that stream's
admitted queue is empty. The state does not record the send as
finished. `ackSend` advances the turn, so streams with admitted bytes
take turns. A session with an unacknowledged send emits nothing. -/
def pump (s : State) : Step :=
  if !s.cause.isRunning || s.outbound.isSome || s.order.isEmpty then
    ⟨s, []⟩
  else
    scan s 0

end State

end Libp2p.Mux.Test.State