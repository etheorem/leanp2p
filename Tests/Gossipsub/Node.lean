import Tests.Support
import Libp2p.Protocols.Gossipsub.Node

/-!
# Gossipsub suite: the node loop

The checks of unit 3b at the seam of the loop: two nodes over the in-memory
switch, the inbound handler, the heartbeat, the gossip spread, and the stop.
No check reads the router state. A check watches what the seam shows: a
delivery callback, or the RPCs that a probe peer decodes.

## How a check waits

Each node takes its own `TestClock`. The loop arms one timer in each pass, so
`settle tc n` returns after the loop has served `n - 1` events since its start
and parked again. A pass holds no other park, so the count gives an exact
order with no sleep. A wait for a timer or a delivery has a real deadline of
`patience` milliseconds, so a missing event fails its check. `stop` and
`Switch.close` have no deadline. Each one wakes what it joins with a close.

A node posts an event per inbound RPC, so each count below names its events
in a comment.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Node

open Conc
open Libp2p.Protocols
open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Node
open Libp2p.Protocols.Mock.Host (Switch HostSeam)

/-! ## Fixtures -/

private def ta : TopicId := ⟨"t"⟩

private def pa : Peer := ⟨[1], "a"⟩
private def pb : Peer := ⟨[2], "b"⟩
private def pc : Peer := ⟨[3], "c"⟩
private def pd : Peer := ⟨[4], "d"⟩
private def px : Peer := ⟨[9], "x"⟩

/-- The real deadline of every wait of this suite, in milliseconds. A
passing run never reaches it. -/
private def patience : Nat := 5000

private def hello (t : TopicId) : Rpc.RPC := Core.helloRpc [t]

private def msgOf (topic : TopicId) (payload : List Nat) : Message :=
  { «from» := none, data := some payload, seqno := none, topic := topic,
    signature := none, key := none }

/-- The bytes of one RPC frame. -/
private def frameOf (rpc : Rpc.RPC) : List Nat :=
  (Rpc.encodeFrame? rpc).getD []

/-- A frame around a body that does not decode as an RPC. -/
private def badBody : List Nat := [255]

/-- The configuration of a node on a test clock. -/
private def configOn (tc : TestClock) (params : Core.Params := Core.defaults)
    (trickle : Nat → Millis := defaultTrickle) : Config :=
  { params, clock := tc.clock, trickle }

/-- A delivery callback that keeps the message for the check. -/
private def keep (inbox : Chan Message) : Message → BaseIO Unit :=
  fun m => discard (inbox.trySend m)

/-- Wait until the loop has armed `n` more timers. `false` at the deadline. The
expiry closes the clock, and the close wakes `nextTimer`. -/
private def settle (tc : TestClock) (n : Nat) : Async Bool := do
  for _ in [0:n] do
    match ← withinDeadline Clock.system patience tc.close tc.nextTimer with
    | .ok true => pure ()
    | _ => return false
  return true

/-- The next value of the channel, or `none` at the deadline. -/
private def within {α : Type} (c : Chan α) : Async (Option α) := do
  let timer ← (Park.sleep patience none : BaseIO (Park (Option α)))
  select #[Park.recv c id, timer]

/-- True when the channel holds no value now. -/
private def quiet {α : Type} (c : Chan α) : Async Bool := do
  return (← (c.tryRecv : BaseIO (Option α))).isNone

/-- True when the task set fails: its handler answered an error. -/
private def joinFails (ts : TaskSet) : Async Bool := do
  try
    ts.joinAll
    return false
  catch _ =>
    return true

/-- Stop the nodes, close the switch, and close the clocks. -/
private def teardown (sw : Switch) (nodes : List Node) (clocks : List TestClock) : Async Unit := do
  for n in nodes do
    n.stop
  sw.close
  for c in clocks do
    (c.close : BaseIO Unit)

/-! ## The probe peer -/

/-- One RPC that a probe decoded. -/
private structure Seen where
  /-- The probe that decoded it. -/
  receiver : Peer
  /-- The opener of the stream. -/
  sender : Peer
  /-- The RPC. -/
  rpc : Rpc.RPC

/-- Every byte of a stream. -/
private partial def readAll (s : Streams.Stream) (acc : ByteArray) : Async ByteArray := do
  match ← s.read with
  | .ok (some chunk) => readAll s (acc ++ chunk)
  | .ok none => return acc
  | .error _ => return acc

/-- A raw peer on the switch: its handler decodes each stream as one RPC and
keeps it for the check. A probe has no router, so a check sees exactly what
the node sent. -/
private def probe (sw : Switch) (me : Peer) (seen : Chan Seen) : Async HostSeam := do
  let (seam, _) ← (sw.host me : BaseIO (HostSeam × TaskSet))
  (seam.setHandler
    { id := Constants.meshsubId
      handle := fun sender stream => ExceptT.lift do
        let bytes ← readAll stream ByteArray.empty
        match Rpc.decodeFrame? (Bytes.toNatList bytes) with
        | .ok (some (payload, _)) =>
          match Core.decodeRpc payload with
          | .ok rpc => discard (seen.trySend { receiver := me, sender, rpc } : BaseIO Bool)
          | .error _ => pure ()
        | _ => pure () } : BaseIO Unit)
  return seam

/-- Open a stream, write the chunks one by one, and half-close it. -/
private def send (seam : HostSeam) (to : Peer) (chunks : List (List Nat)) :
    Async (Option Streams.Stream) := do
  match ← seam.newStream to [Constants.meshsubId] with
  | .error _ => return none
  | .ok (_, stream) =>
    for chunk in chunks do
      discard <| stream.write (Bytes.ofNatList chunk)
    stream.close
    return some stream

private def isGraftOf (t : TopicId) (rpc : Rpc.RPC) : Bool :=
  rpc.control.any (fun c => c.graft.any (fun g => g.topicId == t.name))

/-! ## The switch -/

/-- The switch contract: the handler table of each peer, the protocol choice,
the half-close, the reset, and the close. -/
private def switchChecks (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let (seamA, _) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let (seamB, tasksB) ← (sw.host pb : BaseIO (HostSeam × TaskSet))
  let echoId : Mock.Core.ProtocolId := ⟨"/echo"⟩
  let sender : OnceRef (Option Peer) ← (OnceRef.new none : BaseIO (OnceRef (Option Peer)))
  (seamB.setHandler
    { id := echoId
      handle := fun from_ stream => ExceptT.lift do
        (sender.set (some from_) : BaseIO Unit)
        let bytes ← readAll stream ByteArray.empty
        discard <| stream.write bytes
        stream.close } : BaseIO Unit)
  let unknownPeer ← seamA.newStream px [echoId]
  r.check "switch.unknown-peer" (match unknownPeer with | .error (.protocol _) => true | _ => false)
  let noProtocol ← seamA.newStream pb [⟨"/other"⟩]
  r.check "switch.no-common-protocol"
    (match noProtocol with | .error (.protocol _) => true | _ => false)
  let otherSide ← seamB.newStream pa [echoId]
  r.check "switch.a-handler-serves-its-own-peer"
    (match otherSide with | .error (.protocol _) => true | _ => false)
  match ← seamA.newStream pb [⟨"/other"⟩, echoId] with
  | .error _ => r.check "switch.first-served-protocol" false
  | .ok (id, stream) =>
    r.check "switch.first-served-protocol" (id == echoId)
    discard <| stream.write (Bytes.ofNatList [1, 2, 3])
    stream.close
    let echoed ← readAll stream ByteArray.empty
    r.check "switch.half-close-keeps-the-read-direction" (Bytes.toNatList echoed == [1, 2, 3])
    tasksB.joinAll
    r.check "switch.handler-gets-the-opener" ((← (sender.get : BaseIO (Option Peer))) == some pa)
    let afterClose ← stream.write (Bytes.ofNatList [4])
    r.check "switch.write-after-close-fails"
      (match afterClose with | .error .closed => true | _ => false)
  -- A handler that parks on a read ends when the switch closes.
  (seamA.setHandler
    { id := echoId
      handle := fun _ stream => ExceptT.lift do
        discard <| readAll stream ByteArray.empty } : BaseIO Unit)
  discard <| seamB.newStream pa [echoId]
  sw.close
  r.check "switch.close-ends-a-parked-handler" true
  let afterSwitchClose ← seamB.newStream pa [echoId]
  r.check "switch.no-stream-after-close"
    (match afterSwitchClose with | .error (.closed _) => true | _ => false)
  sw.close
  r.check "switch.second-close-does-nothing" true

/-! ## Two nodes -/

/-- Test 1: the whole path of one publish. The path covers `newStream`, the
handler, the frame decode, `Event.rpc`, the acceptance of the core, and the
delivery. -/
private def twoNodes (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let tcA ← (TestClock.new : BaseIO TestClock)
  let tcB ← (TestClock.new : BaseIO TestClock)
  let (seamA, _) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let (seamB, _) ← (sw.host pb : BaseIO (HostSeam × TaskSet))
  let a ← (start seamA (configOn tcA) : BaseIO Node)
  let b ← (start seamB (configOn tcB) : BaseIO Node)
  let inbox : Chan Message ← (Chan.new 8 : BaseIO (Chan Message))
  r.check "node.two.join-b" (← (b.peerJoined pa .meshsub : BaseIO Bool))
  -- B: the start, and the join. B knows A before the hello of A arrives.
  r.check "node.two.b-knows-a" (← settle tcB 2)
  r.check "node.two.subscribe" (← (a.subscribe ta (keep inbox) : BaseIO Bool))
  r.check "node.two.join-a" (← (a.peerJoined pb .meshsub : BaseIO Bool))
  -- A: the start, the hello of B, the subscribe, and the join.
  r.check "node.two.a-settles" (← settle tcA 4)
  -- B: the hello of A, which names the topic.
  r.check "node.two.b-reads-the-hello" (← settle tcB 1)
  r.check "node.two.publish" (← (b.publish ta (Bytes.ofNatList [7, 8, 9]) : BaseIO Bool))
  let got ← within inbox
  r.check "node.two.delivery-has-the-payload" (got == some (msgOf ta [7, 8, 9]))
  r.check "node.two.one-delivery" (← quiet inbox)
  teardown sw [a, b] [tcA, tcB]

/-- Test 2: a subscribe after the join reaches the peer, and a later
unsubscribe sends the negative record. -/
private def announcement (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let tcA ← (TestClock.new : BaseIO TestClock)
  let tcB ← (TestClock.new : BaseIO TestClock)
  let (seamA, _) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let (seamB, _) ← (sw.host pb : BaseIO (HostSeam × TaskSet))
  let a ← (start seamA (configOn tcA) : BaseIO Node)
  let b ← (start seamB (configOn tcB) : BaseIO Node)
  let inbox : Chan Message ← (Chan.new 8 : BaseIO (Chan Message))
  discard (b.peerJoined pa .meshsub : BaseIO Bool)
  -- B: the start, and the join.
  r.check "node.announce.b-knows-a" (← settle tcB 2)
  discard (a.peerJoined pb .meshsub : BaseIO Bool)
  -- A: the start, the hello of B, and the join.
  r.check "node.announce.a-knows-b" (← settle tcA 3)
  -- B: the empty hello of A.
  r.check "node.announce.b-reads-the-empty-hello" (← settle tcB 1)
  discard (a.subscribe ta (keep inbox) : BaseIO Bool)
  -- B: the record of the subscribe. The hello carried no topic.
  r.check "node.announce.b-reads-the-record" (← settle tcB 1)
  discard (b.publish ta (Bytes.ofNatList [1]) : BaseIO Bool)
  let got ← within inbox
  r.check "node.announce.subscribe-after-join-reaches-the-peer" (got == some (msgOf ta [1]))
  -- The fanout of B keeps A, so a later publish still reaches A. The callback
  -- is gone.
  discard (a.unsubscribe ta : BaseIO Bool)
  discard (b.publish ta (Bytes.ofNatList [2]) : BaseIO Bool)
  -- A: the subscribe, the first publish, the unsubscribe, and the second
  -- publish.
  r.check "node.announce.a-serves-the-leave" (← settle tcA 4)
  r.check "node.announce.unsubscribe-drops-the-callback" (← quiet inbox)
  teardown sw [a, b] [tcA, tcB]
  -- The records at the seam: one positive, one negative.
  let sw ← (Switch.new : BaseIO Switch)
  let tc ← (TestClock.new : BaseIO TestClock)
  let seen : Chan Seen ← (Chan.new 16 : BaseIO (Chan Seen))
  discard <| probe sw pc seen
  let (seam, _) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let n ← (start seam (configOn tc) : BaseIO Node)
  discard (n.peerJoined pc .meshsub : BaseIO Bool)
  let first ← within seen
  r.check "node.announce.hello-has-no-topic"
    (first.any (fun s => s.rpc.subscriptions.isEmpty))
  discard (n.subscribe ta (keep inbox) : BaseIO Bool)
  let on ← within seen
  r.check "node.announce.positive-record" (on.any (fun s => s.rpc == subOptRpc ta true))
  discard (n.unsubscribe ta : BaseIO Bool)
  let off ← within seen
  r.check "node.announce.negative-record" (off.any (fun s => s.rpc == subOptRpc ta false))
  r.check "node.announce.opener-is-the-node" (off.any (fun s => s.sender == pa && s.receiver == pc))
  teardown sw [n] [tc]

/-! ## The inbound handler -/

/-- Test 3: a bad frame fails its handler and resets its stream, and a body
that does not decode leaves the loop running. The other checks pin the read
loop of the handler. -/
private def handlerChecks (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let tc ← (TestClock.new : BaseIO TestClock)
  let seen : Chan Seen ← (Chan.new 16 : BaseIO (Chan Seen))
  let seamA ← probe sw pa seen
  let (seamB, tasksB) ← (sw.host pb : BaseIO (HostSeam × TaskSet))
  let b ← (start seamB (configOn tc) : BaseIO Node)
  let inbox : Chan Message ← (Chan.new 8 : BaseIO (Chan Message))
  discard (b.subscribe ta (keep inbox) : BaseIO Bool)
  discard (b.peerJoined pa .meshsub : BaseIO Bool)
  -- B: the start, the subscribe, and the join.
  r.check "node.handler.setup" (← settle tc 3)
  -- A length over the cap: the handler fails before any body arrives.
  let overCap := Streams.Framing.encodeLength .uvarint (Constants.rpcCap + 1)
  let stream? ← send seamA pb [overCap]
  r.check "node.handler.over-cap-fails" (← joinFails tasksB)
  match stream? with
  | none => r.check "node.handler.over-cap-resets" false
  | some stream =>
    let written ← stream.write (Bytes.ofNatList [1])
    r.check "node.handler.over-cap-resets"
      (match written with | .error .closed => true | _ => false)
  -- A prefix that never ends.
  discard <| send seamA pb [List.replicate 12 0x80]
  r.check "node.handler.long-prefix-fails" (← joinFails tasksB)
  -- The stream ends inside a frame.
  discard <| send seamA pb [Streams.Framing.encodeLength .uvarint 5 ++ [1]]
  r.check "node.handler.end-inside-a-frame-fails" (← joinFails tasksB)
  -- The stream ends inside a prefix.
  discard <| send seamA pb [[0x80]]
  r.check "node.handler.end-inside-a-prefix-fails" (← joinFails tasksB)
  -- A stream with no frame ends clean.
  discard <| send seamA pb []
  r.check "node.handler.empty-stream-is-clean" (!(← joinFails tasksB))
  -- A frame whose body does not decode: the handler is clean, and the core
  -- answers the error to the loop.
  r.check "node.handler.body-does-not-decode"
    (match Core.decodeRpc badBody with | .error _ => true | .ok _ => false)
  discard <| send seamA pb [Streams.Framing.encodeLength .uvarint badBody.length ++ badBody]
  r.check "node.handler.bad-body-reaches-the-loop" (← settle tc 1)
  r.check "node.handler.bad-body-is-clean" (!(← joinFails tasksB))
  -- The loop survives: a later RPC gets delivered.
  discard <| send seamA pb [frameOf (Core.publishRpc (msgOf ta [1]))]
  let got ← within inbox
  r.check "node.handler.loop-survives-a-bad-body" (got == some (msgOf ta [1]))
  -- Two frames in one chunk are two RPCs.
  discard <| send seamA pb
    [frameOf (Core.publishRpc (msgOf ta [2])) ++ frameOf (Core.publishRpc (msgOf ta [3]))]
  let two ← within inbox
  let three ← within inbox
  r.check "node.handler.two-frames-in-one-chunk"
    (two == some (msgOf ta [2]) && three == some (msgOf ta [3]))
  -- One frame in single bytes is one RPC.
  discard <| send seamA pb ((frameOf (Core.publishRpc (msgOf ta [4]))).map (fun x => [x]))
  let four ← within inbox
  r.check "node.handler.one-frame-in-single-bytes" (four == some (msgOf ta [4]))
  r.check "node.handler.split-frame-is-clean" (!(← joinFails tasksB))
  -- A frame of a peer that left is ignored. The event of the leave comes
  -- first, so the order holds.
  discard (b.peerLeft pa : BaseIO Bool)
  -- B: the four RPC frames since the bad body, and the leave.
  r.check "node.handler.peer-left" (← settle tc 5)
  discard <| send seamA pb [frameOf (Core.publishRpc (msgOf ta [5]))]
  r.check "node.handler.unknown-peer-reaches-the-loop" (← settle tc 1)
  r.check "node.handler.unknown-peer-delivers-nothing" (← quiet inbox)
  teardown sw [b] [tc]

/-- The send path: an RPC over the cap opens no stream, and a peer with no
handler does not fault the caller. -/
private def sendChecks (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let seen : Chan Seen ← (Chan.new 4 : BaseIO (Chan Seen))
  let seam ← probe sw pa seen
  let opened : OnceRef Nat ← (OnceRef.new 0 : BaseIO (OnceRef Nat))
  let counting : HostSeam :=
    { seam with
      newStream := fun peer protocols => do
        (opened.update (· + 1) : BaseIO Unit)
        seam.newStream peer protocols }
  sendRpc counting pa (Core.publishRpc (msgOf ta (List.replicate Constants.rpcCap 7)))
  r.check "node.send.over-cap-opens-no-stream" ((← (opened.get : BaseIO Nat)) == 0)
  sendRpc counting px (subOptRpc ta true)
  r.check "node.send.no-peer-is-no-fault" ((← (opened.get : BaseIO Nat)) == 1)
  sendRpc counting pa (subOptRpc ta true)
  let got ← within seen
  r.check "node.send.one-frame-round-trips" (got.any (fun s => s.rpc == subOptRpc ta true))
  sw.close

/-! ## The heartbeat -/

/-- Test 4: a heartbeat fills the mesh. The probe sees the graft at the
seam, and a later publish of a real pair reaches the peer through the mesh. -/
private def tickGrafts (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let tc ← (TestClock.new : BaseIO TestClock)
  let seen : Chan Seen ← (Chan.new 16 : BaseIO (Chan Seen))
  discard <| probe sw pc seen
  let (seam, _) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let n ← (start seam (configOn tc) : BaseIO Node)
  let inbox : Chan Message ← (Chan.new 8 : BaseIO (Chan Message))
  discard (n.subscribe ta (keep inbox) : BaseIO Bool)
  discard (n.peerJoined pc .meshsub : BaseIO Bool)
  -- The start, the subscribe, and the join.
  r.check "node.tick.setup" (← settle tc 3)
  let first ← within seen
  r.check "node.tick.hello-names-the-topic" (first.any (fun s => s.rpc == hello ta))
  r.check "node.tick.no-graft-before-the-heartbeat" (← quiet seen)
  (tc.advance Core.defaults.heartbeatInterval : BaseIO Unit)
  let graft ← within seen
  r.check "node.tick.heartbeat-sends-the-graft" (graft.any (fun s => isGraftOf ta s.rpc))
  -- The next heartbeat comes one interval later. The mesh is full, so it
  -- sends nothing new.
  r.check "node.tick.loop-rearms" (← settle tc 1)
  teardown sw [n] [tc]
  -- A real pair.
  let sw ← (Switch.new : BaseIO Switch)
  let tcA ← (TestClock.new : BaseIO TestClock)
  let tcB ← (TestClock.new : BaseIO TestClock)
  let (seamA, _) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let (seamB, _) ← (sw.host pb : BaseIO (HostSeam × TaskSet))
  let a ← (start seamA (configOn tcA) : BaseIO Node)
  let b ← (start seamB (configOn tcB) : BaseIO Node)
  let inbox : Chan Message ← (Chan.new 8 : BaseIO (Chan Message))
  discard (b.subscribe ta (keep inbox) : BaseIO Bool)
  discard (b.peerJoined pa .meshsub : BaseIO Bool)
  -- B: the start, the subscribe, and the join.
  r.check "node.tick.pair-b" (← settle tcB 3)
  discard (a.subscribe ta (fun _ => pure ()) : BaseIO Bool)
  discard (a.peerJoined pb .meshsub : BaseIO Bool)
  discard (a.publish ta (Bytes.ofNatList [1]) : BaseIO Bool)
  -- A: the start, the hello of B, the subscribe, the join, and the publish.
  r.check "node.tick.pair-a" (← settle tcA 5)
  r.check "node.tick.empty-mesh-sends-nothing" (← quiet inbox)
  (tcA.advance Core.defaults.heartbeatInterval : BaseIO Unit)
  -- The pass that runs the heartbeat arms the next timer after it.
  r.check "node.tick.pair-heartbeat" (← settle tcA 1)
  discard (a.publish ta (Bytes.ofNatList [2]) : BaseIO Bool)
  let got ← within inbox
  r.check "node.tick.publish-reaches-the-mesh" (got == some (msgOf ta [2]))
  teardown sw [a, b] [tcA, tcB]

/-- The parameters of the spread check: an empty mesh, so each peer takes the
gossip of the topic. -/
private def gossipParams : Core.Params :=
  { Core.defaults with mesh := { d := 0, dLow := 0, dHigh := 0, dScore := 0, dLazy := 2 } }

/-- Test 5: the trickle regression. The `i`-th IHAVE of one heartbeat leaves at
the time of the heartbeat plus `trickle i`, and no earlier. -/
private def trickleSpread (r : Tests.Runner) : Async Unit := do
  r.check "node.trickle.default-is-below-one-second"
    ((List.range 64).all (fun i => defaultTrickle i < 1000))
  r.check "node.trickle.default-spreads" (defaultTrickle 0 != defaultTrickle 1)
  let sw ← (Switch.new : BaseIO Switch)
  let tc ← (TestClock.new : BaseIO TestClock)
  let seen : Chan Seen ← (Chan.new 16 : BaseIO (Chan Seen))
  discard <| probe sw pc seen
  discard <| probe sw pd seen
  let (seam, _) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let spread : Nat → Millis := fun i => (i + 1) * 10
  let n ← (start seam (configOn tc gossipParams spread) : BaseIO Node)
  discard (n.subscribe ta (fun _ => pure ()) : BaseIO Bool)
  discard (n.peerJoined pc .meshsub : BaseIO Bool)
  discard (n.peerJoined pd .meshsub : BaseIO Bool)
  discard (n.publish ta (Bytes.ofNatList [1]) : BaseIO Bool)
  -- The start, the subscribe, two joins, and the publish.
  r.check "node.trickle.setup" (← settle tc 5)
  let hello1 ← within seen
  let hello2 ← within seen
  r.check "node.trickle.hellos"
    (hello1.any (fun s => !hasIhave s.rpc) && hello2.any (fun s => !hasIhave s.rpc))
  (tc.advance gossipParams.heartbeatInterval : BaseIO Unit)
  -- The heartbeat ran, and the loop armed the timer of the first send.
  r.check "node.trickle.heartbeat" (← settle tc 1)
  r.check "node.trickle.no-send-at-the-heartbeat" (← quiet seen)
  (tc.advance 9 : BaseIO Unit)
  r.check "node.trickle.no-send-before-its-time" (← quiet seen)
  (tc.advance 1 : BaseIO Unit)
  let first ← within seen
  r.check "node.trickle.first-send-at-10-ms" (first.any (fun s => hasIhave s.rpc))
  -- The loop sent the first, and armed the timer of the second.
  r.check "node.trickle.first-pass" (← settle tc 1)
  r.check "node.trickle.second-waits-for-the-clock" (← quiet seen)
  (tc.advance 9 : BaseIO Unit)
  r.check "node.trickle.second-not-before-its-time" (← quiet seen)
  (tc.advance 1 : BaseIO Unit)
  let second ← within seen
  r.check "node.trickle.second-send-at-20-ms" (second.any (fun s => hasIhave s.rpc))
  r.check "node.trickle.two-receivers"
    (match first, second with
     | some x, some y => x.receiver != y.receiver
     | _, _ => false)
  teardown sw [n] [tc]

/-- The production clock: a real heartbeat sends the graft, and `stop` wakes a
loop that parks on a real timer. `Config` defaults to this clock. -/
private def systemClock (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let seen : Chan Seen ← (Chan.new 16 : BaseIO (Chan Seen))
  discard <| probe sw pc seen
  let (seam, _) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let n ← (start seam { params := { Core.defaults with heartbeatInterval := 20 } } : BaseIO Node)
  discard (n.subscribe ta (fun _ => pure ()) : BaseIO Bool)
  discard (n.peerJoined pc .meshsub : BaseIO Bool)
  let first ← within seen
  r.check "node.system.hello" (first.any (fun s => s.rpc == hello ta))
  let graft ← within seen
  r.check "node.system.real-heartbeat-sends-the-graft" (graft.any (fun s => isGraftOf ta s.rpc))
  n.stop
  r.check "node.system.stop-wakes-a-timer-park" true
  sw.close

/-! ## The callbacks and the queue -/

/-- The callbacks of a topic run in registration order, and the callback of
another topic stays silent. -/
private def callbackOrder (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let tc ← (TestClock.new : BaseIO TestClock)
  let seen : Chan Seen ← (Chan.new 16 : BaseIO (Chan Seen))
  let seamA ← probe sw pa seen
  let (seamB, _) ← (sw.host pb : BaseIO (HostSeam × TaskSet))
  let b ← (start seamB (configOn tc) : BaseIO Node)
  let order : Chan Nat ← (Chan.new 8 : BaseIO (Chan Nat))
  let tag : Nat → Message → BaseIO Unit := fun n _ => discard (order.trySend n)
  discard (b.subscribe ta (tag 1) : BaseIO Bool)
  discard (b.subscribe ⟨"u"⟩ (tag 9) : BaseIO Bool)
  discard (b.subscribe ta (tag 2) : BaseIO Bool)
  discard (b.peerJoined pa .meshsub : BaseIO Bool)
  -- The start, three subscribes, and the join.
  r.check "node.callbacks.setup" (← settle tc 5)
  discard <| send seamA pb [frameOf (Core.publishRpc (msgOf ta [1]))]
  let one ← within order
  let two ← within order
  r.check "node.callbacks.registration-order" (one == some 1 && two == some 2)
  -- One more pass, for the RPC.
  r.check "node.callbacks.served" (← settle tc 1)
  r.check "node.callbacks.other-topic-stays-silent" (← quiet order)
  teardown sw [b] [tc]

/-- A full queue refuses a post, and a refused `subscribe` leaves no callback.
The first send of the loop parks on a gate, so the loop reads no event, and
the queue fills to its bound. -/
private def fullQueue (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let tc ← (TestClock.new : BaseIO TestClock)
  let seen : Chan Seen ← (Chan.new 16 : BaseIO (Chan Seen))
  let seamA ← probe sw pa seen
  let (seamB, _) ← (sw.host pb : BaseIO (HostSeam × TaskSet))
  let gate : Chan Unit ← (Chan.new 1 : BaseIO (Chan Unit))
  let reached : Chan Unit ← (Chan.new 1 : BaseIO (Chan Unit))
  let gated : HostSeam :=
    { seamB with
      newStream := fun peer protocols => do
        discard (reached.trySend () : BaseIO Bool)
        -- Park: the close of the gate wakes it, and later sends pass at once.
        discard gate.recv
        seamB.newStream peer protocols }
  let b ← (start gated (configOn tc) : BaseIO Node)
  let kept : Chan Message ← (Chan.new 8 : BaseIO (Chan Message))
  let refused : Chan Message ← (Chan.new 8 : BaseIO (Chan Message))
  discard (b.peerJoined pa .meshsub : BaseIO Bool)
  r.check "node.queue.loop-parks-on-the-gate" ((← within reached).isSome)
  r.check "node.queue.subscribe-takes-a-slot" (← (b.subscribe ta (keep kept) : BaseIO Bool))
  -- 63 slots remain of the 64.
  let mut taken := 0
  for i in [0:70] do
    if ← (b.publish ⟨"u"⟩ (Bytes.ofNatList [i]) : BaseIO Bool) then
      taken := taken + 1
  r.check "node.queue.bound-is-64" (taken == 63)
  r.check "node.queue.full-refuses-subscribe"
    (!(← (b.subscribe ta (keep refused) : BaseIO Bool)))
  (gate.close : BaseIO Unit)
  -- The start, the join, the subscribe, and 63 publishes.
  r.check "node.queue.loop-drains" (← settle tc 66)
  -- The default message id is the payload, so this payload differs from the
  -- 70 above.
  discard <| send seamA pb [frameOf (Core.publishRpc (msgOf ta [200]))]
  let got ← within kept
  r.check "node.queue.accepted-callback-runs" (got == some (msgOf ta [200]))
  r.check "node.queue.refused-callback-stays-silent" (← quiet refused)
  teardown sw [b] [tc]

/-! ## Local publish and stop -/

/-- Test 6: a publish with no peers opens no stream, and the core emits no
deliver action for a local publish, so the callback of the publisher stays
silent (`Core.publishLocal`). The loop keeps running. -/
private def localPublish (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let tc ← (TestClock.new : BaseIO TestClock)
  let (seam, _) ← (sw.host pa : BaseIO (HostSeam × TaskSet))
  let opened : OnceRef Nat ← (OnceRef.new 0 : BaseIO (OnceRef Nat))
  let counting : HostSeam :=
    { seam with
      newStream := fun peer protocols => do
        (opened.update (· + 1) : BaseIO Unit)
        seam.newStream peer protocols }
  let n ← (start counting (configOn tc) : BaseIO Node)
  let inbox : Chan Message ← (Chan.new 8 : BaseIO (Chan Message))
  discard (n.subscribe ta (keep inbox) : BaseIO Bool)
  r.check "node.local.publish-subscribed" (← (n.publish ta (Bytes.ofNatList [1]) : BaseIO Bool))
  r.check "node.local.publish-unsubscribed" (← (n.publish ⟨"u"⟩ (Bytes.ofNatList [2]) : BaseIO Bool))
  -- The start, the subscribe, and two publishes.
  r.check "node.local.loop-serves-the-publishes" (← settle tc 4)
  r.check "node.local.no-stream" ((← (opened.get : BaseIO Nat)) == 0)
  r.check "node.local.no-local-delivery" (← quiet inbox)
  teardown sw [n] [tc]

/-- Test 7: `stop` joins the loop, every later post answers `false`, an inbound
stream of a stopped node ends clean, and the switch closes without a hang. -/
private def stopChecks (r : Tests.Runner) : Async Unit := do
  let sw ← (Switch.new : BaseIO Switch)
  let tc ← (TestClock.new : BaseIO TestClock)
  let seen : Chan Seen ← (Chan.new 4 : BaseIO (Chan Seen))
  let seamA ← probe sw pa seen
  let (seamB, tasksB) ← (sw.host pb : BaseIO (HostSeam × TaskSet))
  let b ← (start seamB (configOn tc) : BaseIO Node)
  discard (b.peerJoined pa .meshsub : BaseIO Bool)
  -- A park on the queue wakes by the close, with no help from the clock.
  r.check "node.stop.setup" (← settle tc 2)
  b.stop
  r.check "node.stop.returns" true
  b.stop
  r.check "node.stop.second-stop-does-nothing" true
  r.check "node.stop.publish-answers-false" (!(← (b.publish ta (Bytes.ofNatList [1]) : BaseIO Bool)))
  r.check "node.stop.subscribe-answers-false" (!(← (b.subscribe ta (fun _ => pure ()) : BaseIO Bool)))
  r.check "node.stop.unsubscribe-answers-false" (!(← (b.unsubscribe ta : BaseIO Bool)))
  r.check "node.stop.join-answers-false" (!(← (b.peerJoined pa .meshsub : BaseIO Bool)))
  r.check "node.stop.leave-answers-false" (!(← (b.peerLeft pa : BaseIO Bool)))
  discard <| send seamA pb [frameOf (subOptRpc ta true)]
  r.check "node.stop.inbound-frame-is-clean" (!(← joinFails tasksB))
  sw.close
  r.check "node.stop.switch-closes" true
  (tc.close : BaseIO Unit)

/-- Run the checks of this module. -/
def run (r : Tests.Runner) : IO Unit := do
  r.section "gossipsub Node"
    "packages/libp2p/protocols/docs/PLAN.md, unit 3 test milestones"
  Conc.Async.run do
    switchChecks r
    twoNodes r
    announcement r
    handlerChecks r
    sendChecks r
    tickGrafts r
    trickleSpread r
    systemClock r
    callbackOrder r
    fullQueue r
    localPublish r
    stopChecks r

end Tests.Gossipsub.Node
