import Tests.Support
import Tests.Gossipsub.Identity
import Libp2p.Protocols.Gossipsub.Node

/-!
# Gossipsub node loop checks

The suite observes RPCs, deliveries, writer streams and close signals. A
receipt marker provides a queue barrier. TestClock timers belong to the
alarm and track deadlines. The suite never counts timer arms as core events.
Every receive has a real deadline. Stop checks reset their test stream on
expiry, so a failed check can still release its owned tasks.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Node

open Conc
open Libp2p.Protocols
open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Node
open Libp2p.Protocols.Mock.Host (Switch HostSeam)

private def pa : Peer := Identity.peer 1
private def pb : Peer := Identity.peer 2
private def pc : Peer := Identity.peer 3
private def pd : Peer := Identity.peer 4
private def px : Peer := Identity.peer 9
private def topic : TopicId := ⟨"t"⟩
private def patience : Nat := 5000

private def message (data : List Nat) : Message :=
  { «from» := none, data := some data, seqno := none, topic,
    signature := none, key := none }

private def frame (rpc : Rpc.RPC) : ByteArray :=
  Bytes.ofNatList ((Rpc.encodeFrame? rpc).getD [])

/-- A receive that fails at a real deadline instead of hanging the suite. -/
private def receive {α : Type} (c : Chan α) : Async (Option α) := do
  let timer ← (Park.sleep patience none : BaseIO (Park (Option α)))
  select #[Park.recv c id, timer]

/-- Wait for one matching value while preserving unrelated observations. -/
private partial def receiveWhere {α : Type} (c : Chan α) (wanted : α → Bool) :
    Async (Option α) := do
  match ← receive c with
  | some value => if wanted value then some value else receiveWhere c wanted
  | none => none

private def marker : Rpc.RPC := subOptRpc ⟨"node-suite-barrier"⟩ false

/-- A clock with a signal for the absolute time of each armed deadline. -/
private structure ClockProbe where
  test : TestClock
  armed : Chan Nat

private def ClockProbe.new : BaseIO ClockProbe :=
  return ⟨← TestClock.new, ← Chan.new 512⟩

private def ClockProbe.clock (c : ClockProbe) : Clock where
  nowMs := c.test.clock.nowMs
  after ms := do
    let timer ← c.test.clock.after ms
    discard <| c.armed.trySend ((← c.test.clock.nowMs) + ms)
    return timer

/-- Wait for one exact deadline. Earlier recorded arms may still be queued. -/
private def armedAt (c : ClockProbe) (due : Nat) : Async Bool := do
  for _ in [0:512] do
    match ← receive c.armed with
    | some t => if t = due then return true
    | none => return false
  return false

private structure Seen where
  receiver : Peer
  peer : Peer
  rpc : Rpc.RPC

/-- A probe reads many frames on one persistent inbound stream. It also
records the end of each handler, so tests can distinguish close from open. -/
private def probe (sw : Switch) (me : Peer) (seen : Chan Seen)
    (ended : Chan Unit) : BaseIO HostSeam := do
  let (host, _) ← sw.host me
  host.setHandler {
    id := Constants.meshsubId
    handle := fun sender stream => ExceptT.lift do
      let mut buf : List Nat := []
      let mut done := false
      repeat
        match Rpc.decodeFrame? buf with
        | .ok (some (body, rest)) =>
          buf := rest
          if let .ok rpc := Core.decodeRpc body then
            discard (seen.trySend { receiver := me, peer := sender, rpc } : BaseIO Bool)
        | .error _ => break
        | .ok none =>
          match ← stream.read with
          | .ok (some bytes) => buf := buf ++ Bytes.toNatList bytes
          | _ => done := true
        if done then break
      stream.close
      discard (ended.trySend () : BaseIO Bool) }
  return host

private def openStream (host : HostSeam) (peer : Peer) : Async Streams.Stream := do
  match ← host.newStream peer [Constants.meshsubId] with
  | .ok (_, stream) => return stream
  | .error e => throw <| IO.userError s!"open: {repr e}"

/-- Each fixture has a raw control stream and a receipt marker. Sending the
marker after seam posts puts its receipt behind those posts in the queue. -/
private structure Fixture where
  node : Node
  clock : ClockProbe
  control : Streams.Stream
  barriers : Chan Unit
  receipts : Chan (Peer × List Nat)
  deliveries : Chan Message
  hostTasks : TaskSet
  opens : OnceRef Nat

private def fixture (sw : Switch) (me : Peer) (config : Config := {}) : Async Fixture := do
  let clock ← (ClockProbe.new : BaseIO ClockProbe)
  let (host, hostTasks) ← (sw.host me : BaseIO (HostSeam × TaskSet))
  let opens ← (OnceRef.new 0 : BaseIO (OnceRef Nat))
  let barriers ← (Chan.new 64 : BaseIO (Chan Unit))
  let receipts ← (Chan.new 2048 : BaseIO (Chan (Peer × List Nat)))
  let deliveries ← (Chan.new 2048 : BaseIO (Chan Message))
  let controlPeer := Identity.peer (100 + me.hash.digest.headD 0)
  let cfg := { config with
    clock := clock.clock
    order := fun tick peers => config.order tick (peers.filter (· != controlPeer))
    onRpc := fun p bytes => do
      config.onRpc p bytes
      if bytes == Pb.encodeMessage marker then discard <| barriers.trySend ()
      else discard <| receipts.trySend (p, bytes) }
  let counted : HostSeam := { host with newStream := fun p ids => do
    if p != controlPeer then (opens.update (· + 1) : BaseIO Unit)
    host.newStream p ids }
  let node ← (start counted cfg : BaseIO Node)
  -- A raw control peer consumes its hello and has no router of its own.
  let seen ← (Chan.new 2048 : BaseIO (Chan Seen))
  let ended ← (Chan.new 64 : BaseIO (Chan Unit))
  let controlHost ← (probe sw controlPeer seen ended : BaseIO HostSeam)
  let control ← openStream controlHost me
  return { node, clock, control, barriers, receipts, deliveries, hostTasks, opens }

private def barrier (f : Fixture) : Async Bool := do
  discard <| f.control.write (frame marker)
  return (← receive f.barriers).isSome

private def subscribe (f : Fixture) : BaseIO Bool :=
  f.node.subscribe topic (fun m => discard <| f.deliveries.trySend m)

private def finish (sw : Switch) (fs : List Fixture) : Async Unit := do
  for f in fs do
    f.control.close
    f.node.stop
    (f.clock.test.close : BaseIO Unit)
  sw.close

private def delivered (f : Fixture) (data : List Nat) : Async Bool := do
  return (← receive f.deliveries) == some (message data)

/-- The switch serves handlers by peer and protocol. Half-close preserves the
read direction, and reset wakes a parked read. -/
private def switchChecks (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let (a, _) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let (b, _) ← (sw.host pb : BaseIO (HostSeam × TaskSet))
  let sender ← (Chan.new 8 : BaseIO (Chan Peer))
  let id : Mock.Core.ProtocolId := ⟨"/node-test-echo"⟩
  (b.setHandler { id, handle := fun peer s => ExceptT.lift do
    discard (sender.trySend peer : BaseIO Bool)
    repeat
      match ← s.read with
      | .ok (some bytes) => discard <| s.write bytes
      | _ => break
    s.close } : BaseIO Unit)
  r.check "switch.unknown-peer"
    (match ← a.newStream pc [id] with | .error (.protocol _) => true | _ => false)
  r.check "switch.no-common-protocol"
    (match ← a.newStream pb [⟨"/missing"⟩] with | .error (.protocol _) => true | _ => false)
  r.check "switch.handler-belongs-to-its-peer"
    (match ← b.newStream pa [id] with | .error (.protocol _) => true | _ => false)
  match ← a.newStream pb [⟨"/missing"⟩, id] with
  | .error _ => r.check "switch.negotiates-first-served-protocol" false
  | .ok (chosen, s) =>
    r.check "switch.negotiates-first-served-protocol" (chosen == id)
    discard <| s.write (Bytes.ofNatList [1,2,3])
    s.close
    r.check "switch.handler-gets-sender" ((← receive sender) == some pa)
    r.check "switch.half-close-keeps-read"
      (match ← s.read with | .ok (some bytes) => Bytes.toNatList bytes == [1,2,3] | _ => false)
    r.check "switch.write-after-close-fails"
      (match ← s.write (Bytes.ofNatList [4]) with | .error _ => true | _ => false)
  sw.close
  sw.close
  r.check "switch.repeated-close-returns" true
  r.check "switch.no-open-after-close"
    (match ← a.newStream pb [id] with | .error (.closed _) => true | _ => false)

/-- A local publish has no deliver action in the core. The loop serves queued
inputs before stop, without a separate drain loop. -/
private def localChecks (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let f ← fixture sw pa
  discard (subscribe f : BaseIO Bool)
  r.check "node.local.publish-accepted" (← (f.node.publish topic (Bytes.ofNatList [1]) : BaseIO Bool))
  r.check "node.local.publish-unsubscribed-accepted"
    (← (f.node.publish ⟨"other"⟩ (Bytes.ofNatList [2]) : BaseIO Bool))
  r.check "node.local.barrier" (← barrier f)
  r.check "node.local.no-delivery" ((← (f.deliveries.tryRecv : BaseIO (Option Message))).isNone)
  r.check "node.local.no-stream" ((← (f.opens.get : BaseIO Nat)) == 0)
  finish sw [f]

/-- The system-clock alarm ends when the node stops, without an advance of a
test clock. A real heartbeat grafts its known peer. -/
private def systemClockChecks (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let seen ← (Chan.new 64 : BaseIO (Chan Seen))
  let ended ← (Chan.new 16 : BaseIO (Chan Unit))
  discard (probe sw pb seen ended : BaseIO HostSeam)
  let (host, _) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let n ← (start host { params := { Core.defaults with heartbeatInterval := 20 } } : BaseIO Node)
  discard (n.subscribe topic (fun _ => pure ()) : BaseIO Bool)
  discard (n.peerJoined pb .meshsub : BaseIO Bool)
  discard <| receive seen
  let graft ← receive seen
  r.check "node.system.alarm-sends-graft"
    (graft.any (fun s => s.rpc.control.any (fun c => !c.graft.isEmpty)))
  let result ← withinDeadline Clock.system patience (pure ()) n.stop
  r.check "node.system.stop-closes-alarm" (match result with | .ok () => true | _ => false)
  sw.close

/-- A sender's first frame registers its peer before the core sees the RPC.
The same bytes twice reach the observer twice and deliver once. -/
private def inboundChecks (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let f ← fixture sw pb
  r.check "node.inbound.subscribe" (← (subscribe f : BaseIO Bool))
  r.check "node.inbound.setup-barrier" (← barrier f)
  let seen ← (Chan.new 32 : BaseIO (Chan Seen))
  let ended ← (Chan.new 32 : BaseIO (Chan Unit))
  let source ← (probe sw pa seen ended : BaseIO HostSeam)
  let stream ← openStream source pb
  let bytes := frame (Core.publishRpc (message [7]))
  discard <| stream.write (bytes ++ bytes ++ frame marker)
  r.check "node.inbound.two-frames-with-one-id" (← delivered f [7])
  r.check "node.inbound.frames-before-marker" ((← receive f.barriers).isSome)
  let first ← receive f.receipts
  let second ← receive f.receipts
  r.check "node.receipt.sees-both-identical-rpcs"
    (first == some (pa, Pb.encodeMessage (Core.publishRpc (message [7]))) && first == second)
  r.check "node.receipt.delivery-deduplicates" ((← (f.deliveries.tryRecv : BaseIO (Option Message))).isNone)
  r.check "node.inbound.first-rpc-needs-no-notifiee" first.isSome
  -- A split frame stays one RPC. The stream remains open for more frames.
  for byte in Bytes.toNatList (frame (Core.publishRpc (message [8]))) do
    discard <| stream.write (Bytes.ofNatList [byte])
  r.check "node.inbound.single-byte-chunks" (← delivered f [8])
  discard <| stream.write (Bytes.ofNatList [1, 255] ++ frame (Core.publishRpc (message [9])))
  r.check "node.inbound.bad-protobuf-keeps-the-loop" (← delivered f [9])
  -- Distinct messages in one chunk both deliver, in order.
  discard <| stream.write (frame (Core.publishRpc (message [10])) ++
    frame (Core.publishRpc (message [11])))
  r.check "node.inbound.distinct-frames-first" (← delivered f [10])
  r.check "node.inbound.distinct-frames-second" (← delivered f [11])
  -- The empty frame is legal and does not end the stream.
  discard <| stream.write (Bytes.ofNatList [0] ++ frame (Core.publishRpc (message [12])))
  r.check "node.inbound.zero-length-frame-keeps-stream-open" (← delivered f [12])
  stream.close
  -- Drain the successful handler before testing a framing fault.
  r.check "node.inbound.barrier-before-fault" (← barrier f)
  let bad ← openStream source pb
  discard <| bad.write (Bytes.ofNatList (Streams.Framing.encodeLength .uvarint (Constants.rpcCap + 1)))
  -- Closing the successful streams lets the host join report this fault.
  f.control.close
  let failed ← try
    f.hostTasks.joinAll
    pure false
    catch _ => pure true
  r.check "node.inbound.over-cap-fails-handler" failed
  r.check "node.inbound.over-cap-reset" (match ← bad.write (Bytes.ofNatList [1]) with
    | .error _ => true | .ok _ => false)
  f.control.close
  f.node.stop
  -- A bad handler error is reported by the host owner.
  try sw.close catch _ => pure ()
  (f.clock.test.close : BaseIO Unit)

/-- The core emits no local delivery for publish. These 20 trials use a peer
RPC immediately after subscribe, so they exercise callback registration
against a real delivery. -/
private def subscribeRace (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let f ← fixture sw pb
  let seen ← (Chan.new 64 : BaseIO (Chan Seen))
  let ended ← (Chan.new 16 : BaseIO (Chan Unit))
  let source ← (probe sw pa seen ended : BaseIO HostSeam)
  let stream ← openStream source pb
  let deliveries ← (Chan.new 32 : BaseIO (Chan Message))
  let mut successes := 0
  for i in [0:20] do
    let t : TopicId := ⟨s!"subscribe-race-{i}"⟩
    let accepted ← (f.node.subscribe t (fun m => discard <| deliveries.trySend m) : BaseIO Bool)
    let m := { message [i] with topic := t }
    discard <| stream.write (frame (Core.publishRpc m))
    if accepted && (← receive deliveries) == some m then
      successes := successes + 1
  r.check "node.surface.subscribe-then-publish-reaches-callback" (successes == 20)
  stream.close
  finish sw [f]

/-- Direct handler boundary cases preserve the framing error channel. The
fake stream returns finite chunks and records reset without a parked task. -/
private def frameBoundaryChecks (r : Tests.Runner) : Async Unit := do
  let cases : List (String × List ByteArray) :=
    [ ("bad-prefix", [Bytes.ofNatList (List.replicate 12 128)])
    , ("eof-inside-prefix", [Bytes.ofNatList [128]])
    , ("eof-inside-body", [Bytes.ofNatList [5,1]])
    , ("large-malformed-chunk", [Bytes.ofNatList (List.replicate (Constants.rpcCap + 6) 128)]) ]
  for (name, chunks) in cases do
    let remaining ← (OnceRef.new chunks : BaseIO (OnceRef (List ByteArray)))
    let reset ← (OnceRef.new false : BaseIO (OnceRef Bool))
    let events ← (Chan.new 16 : BaseIO (Chan Input))
    let stream : Streams.Stream :=
      { read := do
          let next ← (remaining.updateGet (fun xs => (xs.head?, xs.drop 1)) : BaseIO (Option ByteArray))
          return .ok next
        write := fun _ => pure (.ok ())
        close := pure ()
        reset := (reset.set true : BaseIO Unit) }
    let result ← ((handler events).handle pa stream).run
    r.check s!"node.framing.{name}"
      ((match result with | .error (.protocol _) => true | _ => false) &&
        (← (reset.get : BaseIO Bool)))

/-- A failed outbound write retires only its writer. The existing inbound
stream can still publish, and a later send opens a new outbound writer. -/
private def outboundFailureChecks (r : Tests.Runner) : Async Unit := do
  let deliveries ← (Chan.new 8 : BaseIO (Chan Message))
  let receipts ← (Chan.new 8 : BaseIO (Chan Unit))
  let closed ← (Chan.new 8 : BaseIO (Chan Unit))
  let inbound ← (Pipe.new 16 : BaseIO Pipe)
  let opens ← (OnceRef.new 0 : BaseIO (OnceRef Nat))
  let saved ← (OnceRef.new (none : Option Mock.Core.StreamHandler) : BaseIO (OnceRef (Option Mock.Core.StreamHandler)))
  let host : HostSeam := {
    setHandler := fun h => saved.set (some h)
    newStream := fun _ _ => do
      (opens.update (· + 1) : BaseIO Unit)
      return .ok (Constants.meshsubId, {
        read := pure (.ok none)
        write := fun _ => pure (.error .closed)
        close := discard (closed.trySend () : BaseIO Bool)
        reset := pure () }) }
  let tc ← (TestClock.new : BaseIO TestClock)
  let n ← (start host { clock := tc.clock, onRpc := fun _ _ => discard (receipts.trySend ()) } : BaseIO Node)
  discard (n.subscribe topic (fun m => discard <| deliveries.trySend m) : BaseIO Bool)
  let some h ← (saved.get : BaseIO (Option Mock.Core.StreamHandler))
    | throw <| IO.userError "missing node handler"
  let owner ← (TaskSet.new : BaseIO TaskSet)
  let stream : Streams.Stream := {
    read := return .ok (← inbound.read)
    write := fun _ => pure (.ok ())
    close := pure ()
    reset := (inbound.close : BaseIO Unit) }
  owner.spawn do
    discard <| (h.handle pa stream).run
  discard <| inbound.write (frame (Core.publishRpc (message [31])))
  r.check "node.failure.first-inbound-publish-delivers"
    ((← receive deliveries) == some (message [31]))
  r.check "node.failure.outbound-write-failed" ((← receive closed).isSome)
  -- The close signal follows retirement, so the second publish sees the
  -- post-failure peer state while using the same inbound stream.
  discard <| inbound.write (frame (Core.publishRpc (message [32])))
  r.check "node.failure.second-inbound-publish-survives-outbound-failure"
    ((← receive deliveries) == some (message [32]))
  discard (n.subscribe ⟨"reopen"⟩ (fun _ => pure ()) : BaseIO Bool)
  r.check "node.failure.next-send-opens-fresh-writer" ((← receive closed).isSome)
  r.check "node.failure.two-outbound-opens" ((← (opens.get : BaseIO Nat)) == 2)
  (inbound.close : BaseIO Unit)
  owner.joinAll
  n.stop
  (tc.close : BaseIO Unit)

/-- A legal body arrives one byte per read. The direct handler queue records
all frame bodies in order, without a router changing or deduplicating them. -/
private def readerCopyChecks (r : Tests.Runner) : Async Unit := do
  let first := Core.publishRpc (message (List.replicate 8192 17))
  let second := Core.publishRpc (message [18])
  let third := Core.publishRpc (message [19])
  let all := frame first ++ frame second ++ frame third
  let cursor ← (OnceRef.new 0 : BaseIO (OnceRef Nat))
  let events ← (Chan.new 16 : BaseIO (Chan Input))
  let dribble : Streams.Stream := {
    read := do
      let i ← (cursor.updateGet (fun i => (i, i + 1)) : BaseIO Nat)
      return .ok (if i < all.size then some (all.extract i (i + 1)) else none)
    write := fun _ => pure (.ok ())
    close := pure ()
    reset := pure () }
  let result ← ((handler events).handle pa dribble).run
  let inputs ← (events.drain : BaseIO (List Input))
  let bodies := inputs.filterMap fun
    | .event (.rpc _ bytes) => some bytes
    | _ => none
  r.check "node.reader.many-one-byte-chunks-preserve-all-frames"
    ((match result with | .ok () => true | _ => false) &&
      bodies == [Pb.encodeMessage first, Pb.encodeMessage second, Pb.encodeMessage third])
  let split := frame third
  let chunks := [frame first ++ frame second ++ split.extract 0 1,
    split.extract 1 3, split.extract 3 split.size]
  let pending ← (OnceRef.new chunks : BaseIO (OnceRef (List ByteArray)))
  let mixedEvents ← (Chan.new 16 : BaseIO (Chan Input))
  let mixed := { dribble with read := do
    let bytes ← (pending.updateGet (fun xs => (xs.head?, xs.drop 1)) : BaseIO (Option ByteArray))
    return .ok bytes }
  let mixedResult ← ((handler mixedEvents).handle pa mixed).run
  let mixedInputs ← (mixedEvents.drain : BaseIO (List Input))
  let mixedBodies := mixedInputs.filterMap fun
    | .event (.rpc _ bytes) => some bytes
    | _ => none
  r.check "node.reader.two-frames-then-split-frame-preserve-order"
    ((match mixedResult with | .ok () => true | _ => false) && mixedBodies == bodies)

/-- Two real nodes learn subscriptions and deliver a publish without a
heartbeat or an explicit peerJoined call at the receiver. -/
private def pairChecks (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let a ← fixture sw pa
  let b ← fixture sw pb
  discard (subscribe a : BaseIO Bool)
  r.check "node.pair.subscribe-barrier" (← barrier a)
  discard (b.node.peerJoined pa .meshsub : BaseIO Bool)
  -- Wait for A's hello at B through its receipt observer.
  r.check "node.pair.hello-reaches-publisher" ((← receive b.receipts).isSome)
  discard (b.node.publish topic (Bytes.ofNatList [1]) : BaseIO Bool)
  r.check "node.pair.publish-delivers" (← delivered a [1])
  discard (a.node.unsubscribe topic : BaseIO Bool)
  r.check "node.pair.unsubscribe-barrier" (← barrier a)
  discard (b.node.publish topic (Bytes.ofNatList [2]) : BaseIO Bool)
  r.check "node.pair.publisher-barrier" (← barrier b)
  r.check "node.pair.no-local-delivery" ((← (b.deliveries.tryRecv : BaseIO (Option Message))).isNone)
  finish sw [a, b]

/-- The loop announces the topic before grafting its already announced peer.
Repeat joins emit no hello. Multiple callbacks preserve registration order. -/
private def surfaceChecks (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let f ← fixture sw pa
  let seen ← (Chan.new 32 : BaseIO (Chan Seen))
  let ended ← (Chan.new 16 : BaseIO (Chan Unit))
  let source ← (probe sw pb seen ended : BaseIO HostSeam)
  let stream ← openStream source pa
  discard <| stream.write (frame (Core.helloRpc [topic]) ++ frame marker)
  r.check "node.surface.remote-topic-ready" ((← receive f.barriers).isSome)
  let hello ← receive seen
  r.check "node.surface.initial-hello" (hello.any (fun s => s.rpc.subscriptions.isEmpty))
  discard (f.node.peerJoined pb .meshsub : BaseIO Bool)
  r.check "node.surface.repeat-join-barrier" (← barrier f)
  r.check "node.surface.repeat-join-emits-no-hello" ((← (seen.tryRecv : BaseIO (Option Seen))).isNone)
  let tags ← (Chan.new 16 : BaseIO (Chan Nat))
  discard (f.node.subscribe topic (fun _ => discard <| tags.trySend 1) : BaseIO Bool)
  let record ← receive seen
  let graft ← receive seen
  r.check "node.surface.announcement-precedes-graft"
    (record.any (fun s => s.rpc == subOptRpc topic true) &&
      graft.any (fun s => s.rpc.control.any (fun c => !c.graft.isEmpty)))
  discard (f.node.subscribe topic (fun _ => discard <| tags.trySend 2) : BaseIO Bool)
  discard (f.node.subscribe ⟨"other"⟩ (fun _ => discard <| tags.trySend 9) : BaseIO Bool)
  r.check "node.surface.callback-registration-barrier" (← barrier f)
  discard <| stream.write (frame (Core.publishRpc (message [20])) ++ frame marker)
  r.check "node.surface.callback-rpc-barrier" ((← receive f.barriers).isSome)
  let first ← receive tags
  let second ← receive tags
  r.check "node.surface.callbacks-in-registration-order" (first == some 1 && second == some 2)
  r.check "node.surface.other-topic-callback-silent" ((← (tags.tryRecv : BaseIO (Option Nat))).isNone)
  discard (seen.drain : BaseIO (List Seen))
  discard (f.node.unsubscribe topic : BaseIO Bool)
  r.check "node.surface.unsubscribe-barrier" (← barrier f)
  let off ← receiveWhere seen (fun s => s.rpc == subOptRpc topic false)
  r.check "node.surface.negative-subscription-record" off.isSome
  discard <| stream.write (frame (Core.publishRpc (message [21])) ++ frame marker)
  r.check "node.surface.post-unsubscribe-barrier" ((← receive f.barriers).isSome)
  r.check "node.surface.unsubscribe-removes-callbacks" ((← (tags.tryRecv : BaseIO (Option Nat))).isNone)
  stream.close
  discard (f.node.peerLeft pb : BaseIO Bool)
  r.check "node.surface.leave-barrier" (← barrier f)
  r.check "node.surface.leave-ends-peer-handler" ((← receive ended).isSome)
  finish sw [f]

private def gossipParams : Core.Params :=
  { Core.defaults with
    heartbeatInterval := 100
    mesh := { d := 0, dLow := 0, dHigh := 0, dScore := 0, dLazy := 2 } }

private def ihave (s : Seen) : Bool := hasIhave s.rpc

/-- Explicit delays pin both sides of a deadline and cross a heartbeat.
The run-wide index makes the second heartbeat's first delay 30 ms. -/
private def trickleChecks (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let seen ← (Chan.new 64 : BaseIO (Chan Seen))
  let ended ← (Chan.new 16 : BaseIO (Chan Unit))
  discard (probe sw pc seen ended : BaseIO HostSeam)
  discard (probe sw pd seen ended : BaseIO HostSeam)
  let f ← fixture sw pa { params := gossipParams, trickle := fun i => (i + 1) * 10 }
  discard (subscribe f : BaseIO Bool)
  discard (f.node.peerJoined pc .meshsub : BaseIO Bool)
  discard (f.node.peerJoined pd .meshsub : BaseIO Bool)
  discard (f.node.publish topic (Bytes.ofNatList [7]) : BaseIO Bool)
  r.check "node.trickle.setup" (← barrier f)
  discard <| receive seen
  discard <| receive seen
  r.check "node.trickle.initial-deadline" (← armedAt f.clock 100)
  (f.clock.test.advance 100 : BaseIO Unit)
  r.check "node.trickle.first-deadline" (← armedAt f.clock 110)
  r.check "node.trickle.no-send-at-tick" ((← (seen.tryRecv : BaseIO (Option Seen))).isNone)
  (f.clock.test.advance 9 : BaseIO Unit)
  r.check "node.trickle.no-send-at-9" ((← (seen.tryRecv : BaseIO (Option Seen))).isNone)
  (f.clock.test.advance 1 : BaseIO Unit)
  let one ← receive seen
  r.check "node.trickle.first-at-10" (one.any ihave)
  r.check "node.trickle.second-deadline" (← armedAt f.clock 120)
  (f.clock.test.advance 11 : BaseIO Unit)
  let two ← receive seen
  r.check "node.trickle.advance-11-serves-second" (two.any ihave)
  r.check "node.trickle.two-distinct-receivers"
    (match one, two with | some x, some y => x.receiver != y.receiver | _, _ => false)
  r.check "node.trickle.next-heartbeat" (← armedAt f.clock 200)
  (f.clock.test.advance 79 : BaseIO Unit)
  r.check "node.trickle.run-wide-first-index" (← armedAt f.clock 230)
  r.check "node.trickle.second-heartbeat-waits" ((← (seen.tryRecv : BaseIO (Option Seen))).isNone)
  (f.clock.test.advance 29 : BaseIO Unit)
  r.check "node.trickle.no-send-at-29" ((← (seen.tryRecv : BaseIO (Option Seen))).isNone)
  (f.clock.test.advance 1 : BaseIO Unit)
  r.check "node.trickle.second-heartbeat-first-at-30" ((← receive seen).any ihave)
  r.check "node.trickle.second-heartbeat-second-deadline" (← armedAt f.clock 240)
  (f.clock.test.advance 10 : BaseIO Unit)
  r.check "node.trickle.cross-heartbeat-order" ((← receive seen).any ihave)
  finish sw [f]

private def defaultAndOrderChecks (r : Tests.Runner) : Async Unit := do
  r.check "node.trickle.default-zero" ((List.range 16).all (fun i => ({} : Config).trickle i == 0))
  r.check "node.trickle.spread-below-one-second" ((List.range 1000).all (fun i => spread i < 1000))
  r.check "node.tick.order-changes" (defaultOrder 0 [pa,pb,pc,pd] != defaultOrder 1 [pa,pb,pc,pd])
  r.check "node.tick.order-replays" (defaultOrder 7 [pa,pb,pc,pd] == defaultOrder 7 [pa,pb,pc,pd])
  let sw ← (Switch.new : BaseIO Switch)
  let seen ← (Chan.new 64 : BaseIO (Chan Seen))
  let ended ← (Chan.new 16 : BaseIO (Chan Unit))
  discard (probe sw pc seen ended : BaseIO HostSeam)
  let f ← fixture sw pa { params := gossipParams }
  discard (subscribe f : BaseIO Bool)
  discard (f.node.peerJoined pc .meshsub : BaseIO Bool)
  discard (f.node.publish topic (Bytes.ofNatList [4]) : BaseIO Bool)
  r.check "node.default.setup" (← barrier f)
  discard <| receive seen
  r.check "node.default.timer" (← armedAt f.clock 100)
  (f.clock.test.advance 100 : BaseIO Unit)
  r.check "node.default.gossip-at-tick" ((← receive seen).any ihave)
  finish sw [f]

/-- Long delays reach the pending bound across heartbeats. Excess entries
increase the same drop counter as full writer queues. -/
private def pendingBound (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let seen ← (Chan.new 64 : BaseIO (Chan Seen))
  let ended ← (Chan.new 16 : BaseIO (Chan Unit))
  discard (probe sw pc seen ended : BaseIO HostSeam)
  discard (probe sw pd seen ended : BaseIO HostSeam)
  let params := { gossipParams with window := { historyLength := 300, historyGossip := 300, valid := by decide } }
  let f ← fixture sw pa { params, trickle := fun _ => 1000000 }
  discard (subscribe f : BaseIO Bool)
  discard (f.node.peerJoined pc .meshsub : BaseIO Bool)
  discard (f.node.peerJoined pd .meshsub : BaseIO Bool)
  discard (f.node.publish topic (Bytes.ofNatList [5]) : BaseIO Bool)
  r.check "node.pending.setup" (← barrier f)
  r.check "node.pending.initial-alarm" (← armedAt f.clock 100)
  let mut armed := true
  for i in [0:130] do
    (f.clock.test.advance 100 : BaseIO Unit)
    if !(← armedAt f.clock ((i + 2) * 100)) then armed := false
  r.check "node.pending.every-heartbeat-ran" armed
  r.check "node.pending.bound-256-drops-four" ((← (f.node.dropped : BaseIO Nat)) == 4)
  finish sw [f]

/-- A parked writer leaves the loop free. Sixty offers fill the remaining
slots of its 32-frame queue. Stop resets the stream and returns on deadline. -/
private def stalledAndDrops (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let reached ← (Chan.new 1 : BaseIO (Chan Unit))
  let parked ← (Chan.new 1 : BaseIO (Chan Unit))
  let opened ← (OnceRef.new 0 : BaseIO (OnceRef Nat))
  let resets ← (OnceRef.new 0 : BaseIO (OnceRef Nat))
  let receipts ← (Chan.new 128 : BaseIO (Chan Unit))
  let (_, controlTasks) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let (base, _) ← (sw.host pb : BaseIO (HostSeam × TaskSet))
  let host : HostSeam := { base with newStream := fun peer ids => do
    if peer = pc then
      (opened.update (· + 1) : BaseIO Unit)
      return .ok (Constants.meshsubId, {
        read := pure (.ok none)
        write := fun _ => do
          discard (reached.trySend () : BaseIO Bool)
          discard parked.recv
          return .error .closed
        close := pure ()
        reset := do
          (resets.update (· + 1) : BaseIO Unit)
          (parked.close : BaseIO Unit) })
    base.newStream peer ids }
  let tc ← (TestClock.new : BaseIO TestClock)
  let n ← (start host { clock := tc.clock, onRpc := fun _ _ => discard (receipts.trySend ()) } : BaseIO Node)
  discard (n.peerJoined pc .meshsub : BaseIO Bool)
  r.check "node.stall.writer-reached-write" ((← receive reached).isSome)
  -- The first hello is parked in write. Each new subscription adds one frame.
  for i in [0:60] do
    discard (n.subscribe ⟨s!"topic-{i}"⟩ (fun _ => pure ()) : BaseIO Bool)
  -- A raw marker is ordered after the 60 offers.
  let seen ← (Chan.new 16 : BaseIO (Chan Seen))
  let ended ← (Chan.new 16 : BaseIO (Chan Unit))
  let control ← (probe sw pa seen ended : BaseIO HostSeam)
  let stream ← openStream control pb
  discard <| stream.write (frame marker)
  r.check "node.stall.loop-serves-marker" ((← receive receipts).isSome)
  let drops ← (n.dropped : BaseIO Nat)
  r.check "node.queue.capacity-32-drops-28" (drops == 28)
  IO.println s!"node.measure.full-queue drops={drops}"
  let stopped ← withinDeadline Clock.system patience parked.close n.stop
  r.check "node.stall.stop-returns-before-deadline" (match stopped with | .ok () => true | _ => false)
  r.check "node.stall.stop-reset-the-stream" (0 < (← (resets.get : BaseIO Nat)))
  n.stop
  n.stop
  n.stop
  r.check "node.stop.repeated-calls-return" true
  r.check "node.stop.publish-refused" (!(← (n.publish topic (Bytes.ofNatList [1]) : BaseIO Bool)))
  r.check "node.stop.subscribe-refused" (!(← (n.subscribe topic (fun _ => pure ()) : BaseIO Bool)))
  r.check "node.stop.unsubscribe-refused" (!(← (n.unsubscribe topic : BaseIO Bool)))
  r.check "node.stop.join-refused" (!(← (n.peerJoined pc .meshsub : BaseIO Bool)))
  r.check "node.stop.leave-refused" (!(← (n.peerLeft pc : BaseIO Bool)))
  stream.close
  sw.close
  controlTasks.joinAll
  (tc.close : BaseIO Unit)

/-- Count adjacent sequence inversions in one publisher's received messages. -/
private def inversions : List Nat → Nat
  | a :: b :: rest => (if b < a then 1 else 0) + inversions (b :: rest)
  | _ => 0

/-- Two publishers run at once in bursts of 16 messages. Each waits for the
burst's callbacks before its next burst, so the 32-slot peer queue has room.
Both writers keep one stream and preserve their peer order. -/
private def publisherOrder (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let a ← fixture sw pa
  let b ← fixture sw pb
  let sink ← fixture sw pc
  let ackA ← (Chan.new 32 : BaseIO (Chan Unit))
  let ackB ← (Chan.new 32 : BaseIO (Chan Unit))
  let rows ← (OnceRef.new ([] : List (Nat × Nat)) : BaseIO (OnceRef (List (Nat × Nat))))
  discard (sink.node.subscribe topic (fun m => do
    let data := m.data.getD []
    let from_ := data[0]?.getD 0
    let seq := data[1]?.getD 0 + 256 * data[2]?.getD 0
    rows.update (· ++ [(from_, seq)])
    discard <| (if from_ = 1 then ackA else ackB).trySend ()) : BaseIO Bool)
  r.check "node.order.sink-ready" (← barrier sink)
  discard (a.node.peerJoined pc .meshsub : BaseIO Bool)
  discard (b.node.peerJoined pc .meshsub : BaseIO Bool)
  -- Each publisher must see the sink's hello before its first publish.
  r.check "node.order.a-has-subscription" ((← receive a.receipts).isSome)
  r.check "node.order.b-has-subscription" ((← receive b.receipts).isSome)
  let owner ← (TaskSet.new : BaseIO TaskSet)
  let produce (f : Fixture) (id : Nat) (ack : Chan Unit) : Async Unit := do
    for batch in [0:32] do
      let count := Nat.min 16 (500 - batch * 16)
      for j in [0:count] do
        let i := batch * 16 + j
        if !(← (f.node.publish topic (Bytes.ofNatList [id, i % 256, i / 256]) : BaseIO Bool)) then
          throw <| IO.userError "publisher event refused"
      for _ in [0:count] do
        if (← receive ack).isNone then throw <| IO.userError "publisher delivery timeout"
  owner.spawn (produce a 1 ackA)
  owner.spawn (produce b 2 ackB)
  owner.joinAll
  let data ← (rows.get : BaseIO (List (Nat × Nat)))
  let seqA := (data.filter (·.1 == 1)).map (·.2)
  let seqB := (data.filter (·.1 == 2)).map (·.2)
  let ia := inversions seqA
  let ib := inversions seqB
  let oa ← (a.opens.get : BaseIO Nat)
  let ob ← (b.opens.get : BaseIO Nat)
  r.check "node.order.both-publishers-deliver-500" (seqA.length == 500 && seqB.length == 500)
  r.check "node.order.zero-adjacent-inversions-per-peer" (ia == 0 && ib == 0)
  r.check "node.order.one-stream-per-publisher" (oa == 1 && ob == 1)
  r.check "node.order.bursts-drop-no-frames"
    ((← (a.node.dropped : BaseIO Nat)) == 0 && (← (b.node.dropped : BaseIO Nat)) == 0)
  IO.println s!"node.measure.publishers countA={seqA.length} countB={seqB.length} streamsA={oa} streamsB={ob} inversionsA={ia} inversionsB={ib}"
  finish sw [a,b,sink]

/-- Run the node regressions and print the measured queue and ordering counts. -/
def run (r : Tests.Runner) : IO Unit := do
  r.section "gossipsub Node" "packages/libp2p/protocols/docs/PLAN.md, unit 3"
  Async.run do
    -- Inbound reset checks use a separate host task owner below.
    switchChecks r
    localChecks r
    systemClockChecks r
    inboundChecks r
    frameBoundaryChecks r
    outboundFailureChecks r
    readerCopyChecks r
    pairChecks r
    surfaceChecks r
    subscribeRace r
    trickleChecks r
    defaultAndOrderChecks r
    pendingBound r
    stalledAndDrops r
    publisherOrder r

end Tests.Gossipsub.Node
