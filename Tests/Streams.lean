import Tests.Support
import Streams

/-!
# Streams suite (units W4.1 and W4.2)

The checks of `packages/net/streams/docs/PLAN.md`, "Test milestones"
of units 1 and 2, and the two contracts of ARCHITECTURE §4.7: close
wakes, and no reader strand. The sim transport holds them first, and
the TCP checks hold them again over loopback. The checks come from the
documents.

The TCP checks open real sockets on `127.0.0.1` only, so no packet
leaves the machine. A few of them wait a bounded time on the real
clock, because the kernel decides when a reset or a released port
takes effect. Each one says why at its site.

No answer depends on the order in which the scheduler runs the tasks.
The suite follows the rules of `Tests.Concurrency`: a check on a parked
task arranges the events so that one answer is possible in every order,
and the deadlines run on the test clock.
-/

set_option autoImplicit false

namespace Tests

open Conc Streams Streams.Framing Bytes Multiformats

/-- The bytes of a string. -/
private def b (s : String) : ByteArray := s.toUTF8

/-- True when the bytes equal the bytes of the string. -/
private def eqStr (x : ByteArray) (s : String) : Bool :=
  x.toList == s.toUTF8.toList

/-- A multiaddr from its text form. -/
private def ma (s : String) : Async Multiaddr := do
  match Multiaddr.parse? s with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"test address {s} does not parse"

/-- A connected pair over a new sim net: the dialer's end and the
listener's end. The listener closes before the answer, and the pair
stays open. -/
private def pair (split : Bool := false) : Async (Connection × Connection) := do
  let net ← Sim.Net.new split
  let l ← net.transport.listen (← ma "/ip4/127.0.0.1/tcp/4001")
  let some client ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
  let some server ← l.accept | throw <| IO.userError "accept failed"
  l.close
  return (client, server)

/-! ## The sim -/

/-- Sim: dial, listen, echo, and the hostile mode. -/
private def simChecks (r : Runner) : Async Unit := do
  -- An echo exchange across the two pipes, with the write boundaries kept
  -- and with every write split into single bytes.
  for split in [false, true] do
    let net ← Sim.Net.new split
    let l ← net.transport.listen (← ma "/ip4/127.0.0.1/tcp/4001")
    let owner ← TaskSet.new
    owner.spawn (Sim.serveEcho l owner)
    let some c ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
    c.write (b "hello")
    let echoed ← c.readExactly 5
    r.check s!"sim echo returns the bytes (split {split})"
      (echoed.any fun (x, rest) => eqStr x "hello" && rest.isEmpty)
    r.check s!"the dialer's remote address is the listener's (split {split})"
      (c.remoteAddr == l.addr)
    r.check s!"the dialer's own address is a /memory address (split {split})"
      (c.localAddr.components.map (·.proto) == [.«memory»])
    c.close
    l.close
    owner.joinAll

  -- A client that closes before its echo: the echo writes before the
  -- close or fails after it, and in both orders the owner joins clean.
  do
    let net ← Sim.Net.new
    let l ← net.transport.listen (← ma "/ip4/127.0.0.1/tcp/4006")
    let owner ← TaskSet.new
    owner.spawn (Sim.serveEcho l owner)
    let some c ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
    c.write (b "ping")
    c.close
    l.close
    let joined ← try owner.joinAll; pure true catch _ => pure false
    r.check "echo ends quietly when its peer closes first" joined

  -- In the hostile mode, a read sees one byte for any length of write.
  do
    let (client, server) ← pair (split := true)
    client.write (b "abcdef")
    let first ← server.read
    r.check "the hostile mode delivers a write one byte at a time"
      (first.any fun x => eqStr x "a")
    client.close
    server.close

  -- An empty write to a closed connection fails in both modes. The
  -- hostile mode is not weaker than the plain one.
  for split in [false, true] do
    let (client, server) ← pair split
    client.close
    let thrown ← try
        client.write .empty
        pure false
      catch _ => pure true
    r.check s!"an empty write after close throws (split {split})" thrown
    server.close

  -- A dial to an address with no listener returns none, and so does a
  -- dial after the listener closed.
  do
    let net ← Sim.Net.new
    let addr ← ma "/ip4/127.0.0.1/tcp/4002"
    r.check "a dial with no listener returns none" ((← net.transport.dial addr).isNone)
    let l ← net.transport.listen addr
    l.close
    r.check "a dial after the listener closed returns none" ((← net.transport.dial addr).isNone)
    -- The address is free again after the close.
    let l2 ← net.transport.listen addr
    l2.close

  -- A second listener on one address is a fault.
  do
    let net ← Sim.Net.new
    let addr ← ma "/ip4/127.0.0.1/tcp/4003"
    let l ← net.transport.listen addr
    let thrown ← try
        discard <| net.transport.listen addr
        pure false
      catch _ => pure true
    r.check "a listen on an address in use throws" thrown
    l.close

  -- The sim takes the place of the whole network, so it handles every
  -- address shape that a suite uses.
  do
    let net ← Sim.Net.new
    for text in ["/memory/7", "/ip4/127.0.0.1/tcp/4001", "/ip6/::1/tcp/9000", "/ip4/10.0.0.1"] do
      r.check s!"the sim handles {text}" (net.transport.handles (← ma text))

  -- The backlog: `simBacklog` dials queue with no accept, one more dial
  -- parks, and an accept lets it through. In every order the parked
  -- dial ends with a connection.
  do
    let net ← Sim.Net.new
    let l ← net.transport.listen (← ma "/memory/900")
    let mut queued : Array Connection := #[]
    for _ in [0:simBacklog] do
      let some c ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
      queued := queued.push c
    let late : OnceRef (Option Bool) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do late.set (some (← net.transport.dial l.addr).isSome)
    -- Each accept frees one slot of the queue.
    for _ in [0:simBacklog + 1] do
      discard l.accept
    ts.joinAll
    r.check s!"a dial past the backlog of {simBacklog} waits for an accept, and connects"
      ((← late.get) == some true)
    l.close
    for c in queued do c.close

  -- Back-pressure: a writer of more chunks than the pipe holds parks,
  -- and the reader lets it go on. All the bytes arrive, in order.
  do
    let (client, server) ← pair
    let n := simPipeChunks * 3
    let ts ← TaskSet.new
    ts.spawn do
      for i in [0:n] do client.write (ByteArray.mk #[UInt8.ofNat (i % 256)])
    let got ← server.readExactly n
    ts.joinAll
    r.check s!"{n} writes through a pipe of {simPipeChunks} chunks arrive in order"
      (got.any fun (x, _) => x.toList == (List.range n).map (UInt8.ofNat ∘ (· % 256)))
    client.close
    server.close

/-- The close rules of §4.7, over the sim. -/
private def closeChecks (r : Runner) : Async Unit := do
  -- `close` wakes our own parked read with EOF, and the peer reads EOF.
  -- Nothing is ever written, so only the close can end the read.
  do
    let (client, server) ← pair
    let got : OnceRef (Option (Option ByteArray)) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do got.set (some (← client.read))
    client.close
    ts.joinAll
    r.check "close wakes a parked read with EOF" ((← got.get).any (·.isNone))
    r.check "the peer reads EOF after a close" ((← server.read).isNone)
    client.close
    r.check "a second close does nothing" ((← client.read).isNone)
    server.close

  -- The peer reads the queued bytes, then EOF.
  do
    let (client, server) ← pair
    client.write (b "ab")
    client.close
    let got ← server.readExactly 2
    r.check "queued bytes drain before EOF" (got.any fun (x, _) => eqStr x "ab")
    r.check "EOF follows the drained bytes" ((← server.read).isNone)
    server.close

  -- A failed write tears the connection down: it throws, and the local
  -- read then sees EOF.
  do
    let (client, server) ← pair
    server.close
    let thrown ← try
        client.write (b "late")
        pure false
      catch _ => pure true
    r.check "a write to a closed peer throws" thrown
    r.check "a failed write leaves the local read at EOF" ((← client.read).isNone)

  -- A listener close wakes a parked accept, and closes the connections
  -- that are still in the queue, so their dialers read EOF.
  do
    let net ← Sim.Net.new
    let l ← net.transport.listen (← ma "/ip4/127.0.0.1/tcp/4004")
    let some queued ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
    l.close
    r.check "a queued dial reads EOF after the listener closes" ((← queued.read).isNone)
    let l2 ← net.transport.listen (← ma "/ip4/127.0.0.1/tcp/4005")
    let woke : OnceRef (Option Bool) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do woke.set (some (← l2.accept).isNone)
    l2.close
    ts.joinAll
    r.check "close wakes a parked accept with none" ((← woke.get) == some true)

  -- A dial that waits on a full backlog when the listener closes answers
  -- none. In one order the close wakes the parked send. In the other
  -- order the dial starts after the close and finds no listener.
  do
    let net ← Sim.Net.new
    let l ← net.transport.listen (← ma "/memory/901")
    let mut queued : Array Connection := #[]
    for _ in [0:simBacklog] do
      let some c ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
      queued := queued.push c
    let late : OnceRef (Option Bool) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do late.set (some (← net.transport.dial l.addr).isNone)
    l.close
    ts.joinAll
    r.check "a dial past the backlog answers none when the listener closes"
      ((← late.get) == some true)
    let mut allEnded := true
    for c in queued do
      allEnded := allEnded && (← c.read).isNone
    r.check "the listener close ends every queued dial with EOF" allEnded

/-! ## The readers -/

/-- `readExactly`, `BufReader`, and the hand-over between stages. -/
private def readerChecks (r : Runner) : Async Unit := do
  -- `readExactly` returns the over-read with the bytes.
  do
    let (client, server) ← pair
    client.write (b "abcdef")
    let got ← server.readExactly 2
    r.check "readExactly answers the bytes and the over-read"
      (got.any fun (x, rest) => eqStr x "ab" && eqStr rest "cdef")
    let zero ← server.readExactly 0 (b "xy")
    r.check "readExactly of 0 bytes keeps the pending bytes"
      (zero.any fun (x, rest) => x.isEmpty && eqStr rest "xy")
    client.close
    r.check "readExactly answers none when the stream ends first"
      ((← server.readExactly 10).isNone)
    server.close

  -- No reader strand: stage 1 reads a frame and reads the start of
  -- stage 2 too far. Stage 2 builds its reader from the leftover and
  -- reads its bytes whole. The check runs with the boundaries kept and
  -- split.
  for split in [false, true] do
    let (client, server) ← pair split
    -- One write: a `u16be` frame "ab", then 6 bytes of stage 2.
    client.write (ByteArray.mk #[0, 2] ++ b "ab" ++ b "stage2")
    let stage1 := BufReader.new server
    match ← Framing.read stage1 .u16be 16 with
    | .ok (some (payload, rest)) =>
      r.check s!"stage 1 reads its frame (split {split})" (eqStr payload "ab")
      let stage2 := BufReader.new server rest.leftover
      let got ← stage2.readExactly 6
      r.check s!"stage 2 reads the bytes that stage 1 read too far (split {split})"
        (got.any fun (x, _) => eqStr x "stage2")
    | _ => r.check s!"stage 1 reads its frame (split {split})" false
    client.close
    server.close

  -- `BufReader.read` gives the buffer first, then the connection.
  do
    let (client, server) ← pair
    client.write (b "next")
    let seeded := BufReader.new server (b "seed")
    match ← seeded.read with
    | some (first, after) =>
      r.check "BufReader.read gives the seed first" (eqStr first "seed")
      r.check "BufReader.read leaves nothing in the buffer" (after.available == 0)
      let second ← after.read
      r.check "BufReader.read then reads the connection"
        (second.any fun (x, _) => eqStr x "next")
    | none => r.check "BufReader.read gives the seed first" false
    client.close
    server.close

/-- Many frames out of one chunk: the reader serves them from its buffer
by offset, in order. The second half arrives in a later write, so one
frame crosses a `fill`. -/
private def manyFramesChecks (r : Runner) : Async Unit := do
  let (client, server) ← pair
  let frame (i : Nat) : ByteArray :=
    (encodeB? .uvarint 64 (b s!"frame {i}")).getD .empty
  let wire := (List.range 1000).foldl (fun acc i => acc ++ frame i) ByteArray.empty
  -- Cut inside a frame, so the reader must fill in the middle of it.
  let cut := wire.size / 2 + 3
  client.write (wire.extract 0 cut)
  let rest := wire.extract cut wire.size
  let ts ← TaskSet.new
  ts.spawn do
    client.write rest
    client.close
  let mut reader := BufReader.new server
  let mut inOrder := true
  for i in [0:1000] do
    match ← Framing.read reader .uvarint 64 with
    | .ok (some (payload, next)) =>
      inOrder := inOrder && eqStr payload s!"frame {i}"
      reader := next
    | _ => inOrder := false
  let atEnd ← Framing.read reader .uvarint 64
  ts.joinAll
  r.check "1000 frames out of one chunk read back in order" inOrder
  r.check "the reader reads EOF after the last frame"
    (match atEnd with | .ok none => true | _ => false)
  server.close

/-! ## Framing -/

/-- Framing: the caps, the failures, and the headers that cross reads. -/
private def framingChecks (r : Runner) : Async Unit := do
  -- A length exactly at the cap passes. One over it is `malformed`
  -- before any payload read: the writer sends the header alone and
  -- closes, so a read that waited for the payload would answer EOF.
  for p in [Prefix.uvarint, Prefix.u16be] do
    let (client, server) ← pair
    let atCap := (encodeB? p 4 (b "wxyz")).getD .empty
    client.write atCap
    let ok ← Framing.read (BufReader.new server) p 4
    r.check s!"a frame at the cap passes ({repr p})"
      (match ok with | .ok (some (x, _)) => eqStr x "wxyz" | _ => false)
    client.write (ofNatList (encodeLength p 5))
    client.close
    let over ← Framing.read (BufReader.new server) p 4
    r.check s!"a length over the cap is malformed before the payload ({repr p})"
      (match over with | .error .malformed => true | _ => false)
    server.close
    r.check s!"encodeB? refuses a payload over the cap ({repr p})"
      ((encodeB? p 4 (b "vwxyz")).isNone)

  -- The `u16be` prefix carries 65535 at most, whatever the cap.
  do
    let full := ByteArray.mk (Array.replicate 65535 7)
    r.check "encodeB? takes a u16be payload of 65535 bytes"
      (encodeB? .u16be 70000 full).isSome
    r.check "encodeB? refuses a u16be payload of 65536 bytes"
      (encodeB? .u16be 70000 (full.push 7)).isNone

  -- A multi-byte varint header that the hostile mode splits across reads:
  -- the read fills until the header is whole.
  do
    let (client, server) ← pair (split := true)
    let payload := ByteArray.mk (Array.replicate 300 3)
    -- The hostile mode makes 302 one-byte writes, more than the pipe
    -- holds, so the writer runs in its own task while the read drains.
    let ts ← TaskSet.new
    ts.spawn (client.write ((encodeB? .uvarint 1024 payload).getD .empty))
    let got ← Framing.read (BufReader.new server) .uvarint 1024
    ts.joinAll
    r.check "a 2-byte varint header split across reads still reads the frame"
      (match got with | .ok (some (x, _)) => x == payload | _ => false)
    client.close
    server.close

  -- A connection that ends inside a frame ends the read as EOF, never as
  -- `truncated`.
  do
    let (client, server) ← pair
    client.write (ByteArray.mk #[0, 9] ++ b "abc")
    client.close
    let cut ← Framing.read (BufReader.new server) .u16be 16
    r.check "a stream that ends inside a frame reads EOF"
      (match cut with | .ok none => true | _ => false)
    server.close

  -- A connection that ends inside a header ends the read as EOF too.
  do
    let (client, server) ← pair
    client.write (ByteArray.mk #[0x80])
    client.close
    let cut ← Framing.read (BufReader.new server) .uvarint 16
    r.check "a stream that ends inside a varint header reads EOF"
      (match cut with | .ok none => true | _ => false)
    server.close

  -- A varint prefix past its budget is `malformed` on the IO path too.
  do
    let (client, server) ← pair
    client.write (ByteArray.mk (Array.replicate 10 0x80))
    client.close
    let long ← Framing.read (BufReader.new server) .uvarint 1024
    r.check "a varint prefix past its budget is malformed"
      (match long with | .error .malformed => true | _ => false)
    server.close

  -- The model answers: a short prefix is `truncated`.
  r.check "the model reports a short varint prefix as truncated"
    (failsWith .truncated (Frame.decode? .uvarint 4 [0x80]))
  r.check "the model reports a short u16be prefix as truncated"
    (failsWith .truncated (Frame.decode? .u16be 4 [0]))
  r.check "the model reports a short payload as truncated"
    (failsWith .truncated (Frame.decode? .u16be 4 [0, 3, 1]))
  r.check "the model reports a length over the cap as malformed"
    (failsWith .malformed (Frame.decode? .uvarint 4 [5, 1, 2, 3, 4, 5]))
  r.check "the model reports a non-byte in the payload as malformed"
    (failsWith .malformed (Frame.decode? .u16be 4 [0, 2, 1, 300]))

/-- Every byte array of length at most `n`, shortest first. `n = 2`
gives 65793 arrays. -/
private def allBytesUpTo : Nat → List ByteArray
  | 0 => [ByteArray.empty]
  | n + 1 =>
    let shorter := allBytesUpTo n
    let longest := shorter.filter (·.size == n)
    shorter ++ longest.flatMap fun b => (List.range 256).map fun x => b.push (UInt8.ofNat x)

/-- `count` pseudo-random byte arrays, each of length at most `maxLen`.
The generator is seeded, so a failed input comes back from the seed. -/
private def genBytesList (count maxLen : Nat) (g : StdGen) : List ByteArray × StdGen :=
  -- `Nat.fold` passes the generator from draw to draw.
  Nat.fold count (fun _ _ (acc, g) =>
    let (len, g) := randNat g 0 maxLen
    let (bytes, g) := Nat.fold len (fun _ _ (bs, g) =>
      let (x, g) := randNat g 0 255
      (bs.push (UInt8.ofNat x), g)) (ByteArray.emptyWithCapacity len, g)
    (bytes :: acc, g)) ([], g)

/-- The generic harness of `base/bytes` over one prefix and cap, and the
production encoder. The answer names the failed checks.

* The round trip on the samples (`checkRoundTrips`).
* The production encoder writes the model encoding of each sample.
* The model pin (`checkModelPins`) on every input up to 2 bytes, on the
  encodings with a rest after them, and on seeded random inputs. The
  adapter turns the rest of the production answer into its model
  view. -/
private def harnessFor (p : Prefix) (cap : Nat) (g : StdGen) : List String × StdGen :=
  let payloads : List (List Nat) := [[], [0], [255, 1], (List.range cap).map (· % 256)]
  let samples := payloads.filterMap (Frame.ofList? p cap)
  let encoded := samples.map fun f => ofNatList (Frame.encode f ++ [7, 7])
  let (random, g) := genBytesList 2000 12 g
  let decodeBytes (b : ByteArray) : Except DecodeError (Frame p cap × List Nat) :=
    (decodeB? p cap b).map fun (f, rest) => (f, toNatList rest)
  let encoderOk := samples.all fun f =>
    (encodeB? p cap (ofNatList f.payload)).map toNatList == some (Frame.encode f)
  let inputs := allBytesUpTo 2 ++ encoded ++ random
  -- The pin answers one `Bool` for a list, so the failed inputs are
  -- found one by one, to name them.
  let pinFails := inputs.filter fun b => !checkModelPins decodeBytes [b]
  ((if checkRoundTrips samples then [] else ["the round trip"]) ++
    (if encoderOk then [] else ["encodeB? writes Frame.encode"]) ++
    (pinFails.take 3).map fun b => s!"the pin on {toNatList b}", g)

private def harnessChecks (r : Runner) : IO Unit := do
  let mut g := mkStdGen 41
  for p in [Prefix.uvarint, Prefix.u16be] do
    for cap in [3, 300] do
      let (fails, g') := harnessFor p cap g
      g := g'
      r.check s!"the frame codec pins to the model ({repr p}, cap {cap}): {fails}"
        fails.isEmpty

/-! ## `Stream` -/

/-- `Stream` over a loop. The test plays the loop: it takes the events,
and it answers the tags through the `Completions` of the session. -/
private inductive Ev where
  | write (tag : Nat) (bytes : ByteArray)
  | consumed (n : Nat)
  | close
  | reset

/-- A port whose posts go to a channel of `capacity` events. -/
private def mkPort (capacity : Nat := 8) : Async (LoopPort × Chan Ev) := do
  -- `capacity + 1` is a successor, so `Nat.succ_pos` gives the proof
  -- that `decide` cannot give for a variable.
  let events : Chan Ev ← Chan.new (capacity + 1) (Nat.succ_pos _)
  let inbox : Chan (Except Streams.Error ByteArray) ← Chan.new 8
  let completions ← Completions.new
  return ({ inbox, completions
            postWrite := fun tag bytes => events.send (.write tag bytes)
            postConsumed := fun n => events.send (.consumed n)
            postClose := events.send .close
            postReset := events.send .reset }, events)

private def streamChecks (r : Runner) : Async Unit := do
  -- A write returns only after its tag resolves, with the answer of the
  -- loop.
  do
    let (port, events) ← mkPort
    let s ← Stream.ofPort port
    let answer : OnceRef (Option (Except Streams.Error Unit)) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do answer.set (some (← s.write (b "hi")))
    match ← events.recv with
    | some (.write tag bytes) =>
      r.check "the write posts its bytes under a tag" (eqStr bytes "hi")
      -- The tag has no answer yet, so the write cannot have returned.
      r.check "a write waits for its tag" ((← answer.get).isNone)
      port.completions.resolve tag (.ok ())
    | _ => r.check "the write posts its bytes under a tag" false
    ts.joinAll
    r.check "Action.done answers the write" (match ← answer.get with | some (.ok ()) => true | _ => false)

    -- A refusal reaches the writer.
    ts.spawn do answer.set (some (← s.write (b "no")))
    match ← events.recv with
    | some (.write tag _) => port.completions.resolve tag (.error .reset)
    | _ => pure ()
    ts.joinAll
    r.check "Action.refused answers the write with its error"
      (match ← answer.get with | some (.error .reset) => true | _ => false)

    -- The loop ends with a write parked: `closeAll` wakes it.
    ts.spawn do answer.set (some (← s.write (b "lost")))
    discard events.recv
    port.completions.closeAll
    ts.joinAll
    r.check "closeAll wakes a parked write with closed"
      (match ← answer.get with | some (.error .closed) => true | _ => false)
    r.check "a write after closeAll answers closed at once"
      (match ← s.write (b "late") with | .error .closed => true | _ => false)

  -- A write whose post fails answers closed: the loop has ended.
  do
    let (port, events) ← mkPort
    events.close
    let s ← Stream.ofPort port
    r.check "a write to an ended loop answers closed"
      (match ← s.write (b "x") with | .error .closed => true | _ => false)

  -- Many writers at once: each write gets its own tag, each answer
  -- reaches its own writer, and no tag waits after the answers.
  do
    let n := 200
    let (port, events) ← mkPort n
    let s ← Stream.ofPort port
    let tags : OnceRef (List Nat) ← OnceRef.new []
    let oks : OnceRef Nat ← OnceRef.new 0
    let writers ← TaskSet.new
    for i in [0:n] do
      writers.spawn do
        if let .ok () ← s.write (b s!"{i}") then oks.update (· + 1)
    -- The loop: one answer for each write it takes.
    for _ in [0:n] do
      match ← events.recv with
      | some (.write tag _) =>
        tags.update (tag :: ·)
        port.completions.resolve tag (.ok ())
      | _ => pure ()
    writers.joinAll
    let seen ← (tags.get : BaseIO (List Nat))
    r.check s!"{n} concurrent writes get {n} distinct tags" (seen.eraseDups.length == n)
    r.check s!"{n} concurrent writes each get their answer" ((← oks.get) == n)

  -- The reads: the deliveries in order, a reset as an error, then EOF.
  -- `close` and `reset` post their events.
  do
    let (port, events) ← mkPort
    let s ← Stream.ofPort port
    discard <| port.inbox.send (.ok (b "one"))
    discard <| port.inbox.send (.error .reset)
    -- A chunk after the reset, and the inbox stays open: the stream is
    -- dead after the error all the same, so the later read neither parks
    -- nor takes the chunk.
    discard <| port.inbox.send (.ok (b "stray"))
    let first ← s.read
    let second ← s.read
    let third ← s.read
    r.check "a read takes the delivered chunk"
      (match first with | .ok (some x) => eqStr x "one" | _ => false)
    r.check "a reset reads as an error, never as EOF"
      (match second with | .error .reset => true | _ => false)
    r.check "a read after an error answers EOF, with the inbox still open"
      (match third with | .ok none => true | _ => false)
    -- Only the chunk posts a count: the error and the EOF move no byte.
    r.check "a read posts the count of the bytes it took"
      (match ← events.tryRecv, ← events.tryRecv with
        | some (.consumed 3), none => true
        | _, _ => false)
    s.close
    s.reset
    let c ← events.recv
    let rs ← events.recv
    r.check "close and reset post their events"
      (match c, rs with | some .close, some .reset => true | _, _ => false)

  -- `endedBy`: a reset after the inbox closed reads as the reset.
  do
    let (port, _) ← mkPort
    port.inbox.close
    let s ← Stream.ofPort { port with endedBy := pure (some .reset) }
    let first ← s.read
    let second ← s.read
    r.check "a closed inbox with endedBy reads as its reason"
      (match first with | .error .reset => true | _ => false)
    r.check "the read after the reason answers EOF"
      (match second with | .ok none => true | _ => false)

  -- `prependBytes` puts the bytes it gets ahead of the bytes of the loop.
  do
    let (port, _) ← mkPort
    discard <| port.inbox.send (.ok (b "world"))
    let s ← (← Stream.ofPort port).prependBytes (b "hello ")
    let first ← s.read
    let second ← s.read
    r.check "prependBytes answers the bytes it got first"
      (match first, second with
        | .ok (some x), .ok (some y) => eqStr x "hello " && eqStr y "world"
        | _, _ => false)

  -- Two reads race on a prepended stream: exactly one of them answers
  -- the front bytes, and the other one takes the delivery of the loop.
  do
    let (port, _) ← mkPort
    discard <| port.inbox.send (.ok (b "loop"))
    let s ← (← Stream.ofPort port).prependBytes (b "front")
    let answers : OnceRef (List String) ← OnceRef.new []
    let ts ← TaskSet.new
    for _ in [0:2] do
      ts.spawn do
        if let .ok (some x) ← s.read then
          answers.update (String.fromUTF8! x :: ·)
    ts.joinAll
    let got ← (answers.get : BaseIO (List String))
    r.check "two racing reads answer the front bytes once and the loop's once"
      (got.mergeSort (· ≤ ·) == ["front", "loop"])

  -- An empty front gives the stream back as it is.
  do
    let (port, _) ← mkPort
    discard <| port.inbox.send (.ok (b "only"))
    let s ← (← Stream.ofPort port).prependBytes .empty
    r.check "prependBytes with no bytes leaves the reads alone"
      (match ← s.read with | .ok (some x) => eqStr x "only" | _ => false)

  -- An answer for a tag that waits no more does nothing: a second answer
  -- of one tag, and a tag that the table never gave. The next write
  -- still gets its own answer.
  do
    let (port, events) ← mkPort
    let s ← Stream.ofPort port
    let answer : OnceRef (Option (Except Streams.Error Unit)) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do answer.set (some (← s.write (b "one")))
    match ← events.recv with
    | some (.write tag _) =>
      port.completions.resolve tag (.ok ())
      port.completions.resolve tag (.error .reset)
      port.completions.resolve (tag + 1000) (.error .reset)
    | _ => pure ()
    ts.joinAll
    r.check "a second answer of one tag leaves the first answer"
      (match ← answer.get with | some (.ok ()) => true | _ => false)
    ts.spawn do answer.set (some (← s.write (b "two")))
    match ← events.recv with
    | some (.write tag _) => port.completions.resolve tag (.ok ())
    | _ => pure ()
    ts.joinAll
    r.check "after answers to retired tags, the next write still gets its answer"
      (match ← answer.get with | some (.ok ()) => true | _ => false)

/-! ## The deadline -/

/-- The deadline of §5.4 on the test clock. -/
private def deadlineChecks (r : Runner) : Async Unit := do
  -- A silent peer: the phase parks on a read that nothing feeds. The
  -- deadline closes the connection, the read ends, and the peer reads
  -- EOF.
  do
    let tc ← TestClock.new
    let (client, server) ← pair
    let answer : OnceRef (Option (Except Conc.Error (Option ByteArray))) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do answer.set (some (← client.withinUnauthDeadline tc.clock client.read))
    r.check "the unauthenticated phase arms its deadline" (← tc.nextTimer)
    tc.advance unauthDeadlineMs
    ts.joinAll
    r.check "a silent peer fails at the deadline"
      (match ← answer.get with | some (.error .deadlineExpired) => true | _ => false)
    r.check "the expiry closed the connection, and the peer reads EOF" ((← server.read).isNone)
    server.close
    tc.close

  -- The phase of a silent peer ends with a value after the expiry: the
  -- close makes its read answer EOF. No caller sees that value, so it
  -- goes to `release`, exactly once.
  do
    let tc ← TestClock.new
    let (client, server) ← pair
    let released : OnceRef Nat ← OnceRef.new 0
    let answer : OnceRef (Option (Except Conc.Error (Option ByteArray))) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do
      answer.set (some (← client.withinUnauthDeadline tc.clock client.read
        (fun _ => released.update (· + 1))))
    r.check "the phase with a release arms its deadline" (← tc.nextTimer)
    tc.advance unauthDeadlineMs
    ts.joinAll
    r.check "the late value of an expired phase goes to release once"
      ((match ← answer.get with | some (.error .deadlineExpired) => true | _ => false) &&
        (← released.get) == 1)
    server.close
    tc.close

  -- A phase that ends in time gives its value to the caller, and none to
  -- `release`.
  do
    let tc ← TestClock.new
    let (client, server) ← pair
    let released : OnceRef Nat ← OnceRef.new 0
    server.write (b "now")
    let got ← client.withinUnauthDeadline tc.clock client.read (fun _ => released.update (· + 1))
    r.check "a phase that ends in time calls no release"
      ((match got with | .ok (some x) => eqStr x "now" | _ => false) && (← released.get) == 0)
    client.close
    server.close
    tc.close

  -- One millisecond short of the deadline, the phase still waits. The
  -- bytes of the peer then end it with its value.
  do
    let tc ← TestClock.new
    let (client, server) ← pair
    let answer : OnceRef (Option (Except Conc.Error (Option ByteArray))) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do answer.set (some (← client.withinUnauthDeadline tc.clock client.read))
    r.check "the phase arms its deadline before the advance" (← tc.nextTimer)
    tc.advance (unauthDeadlineMs - 1)
    server.write (b "in time")
    ts.joinAll
    r.check "a phase that ends before the deadline returns its value"
      (match ← answer.get with | some (.ok (some x)) => eqStr x "in time" | _ => false)
    client.close
    server.close
    tc.close

  -- A phase that ends in time returns its answer, and the connection
  -- stays open.
  do
    let tc ← TestClock.new
    let (client, server) ← pair
    server.write (b "x")
    let got ← client.withinUnauthDeadline tc.clock client.read
    r.check "a phase that ends in time returns its value"
      (match got with | .ok (some x) => eqStr x "x" | _ => false)
    client.write (b "y")
    r.check "the connection stays open after the phase" ((← server.read).any (eqStr · "y"))
    client.close
    server.close
    tc.close

/-! ## TCP -/

/-- The TCP address mapping. -/
private def tcpAddressChecks (r : Runner) : Async Unit := do
  -- A TCP multiaddr maps to its socket address, and back.
  for (text, shown) in [("/ip4/127.0.0.1/tcp/4001", "127.0.0.1:4001"),
      ("/ip6/::1/tcp/9000", "[::1]:9000"), ("/ip6/2001:db8::7/tcp/65535", "[2001:db8::7]:65535")] do
    let m ← ma text
    let sa := Tcp.socketAddress? m
    r.check s!"{text} maps to {shown}" (sa.map toString == some shown)
    r.check s!"{text} maps back to itself" ((sa.bind Tcp.multiaddrOf) == some m)
    r.check s!"the TCP transport handles {text}" (Tcp.transport.handles m)
  -- Every other shape is not a TCP address for this transport: `handles`
  -- refuses it, and a dial or a listen of it throws.
  for text in ["/ip4/127.0.0.1", "/memory/7", "/tcp/4001/ip4/127.0.0.1",
      "/ip4/127.0.0.1/tcp/4001/tcp/4002", "/ip4/127.0.0.1/ip4/127.0.0.1"] do
    let m ← ma text
    r.check s!"{text} is not a TCP address" (Tcp.socketAddress? m).isNone
    r.check s!"the TCP transport does not handle {text}" (!Tcp.transport.handles m)
    let dialThrew ← try discard <| Tcp.transport.dial m; pure false catch _ => pure true
    let listenThrew ← try discard <| Tcp.transport.listen m; pure false catch _ => pure true
    r.check s!"a dial and a listen of {text} throw" (dialThrew && listenThrew)

/-- A connected TCP pair over loopback, on a port that the system picks:
the dialer's end and the listener's end. The listener closes before the
answer, and the pair stays open. -/
private def tcpPair (clock : Clock := Clock.system) : Async (Connection × Connection) := do
  let tcp := Tcp.transport clock
  let l ← tcp.listen (← ma "/ip4/127.0.0.1/tcp/0")
  let accepted : Chan (Option Connection) ← Chan.new 1
  let ts ← TaskSet.new
  -- The accept parks until the dial below connects.
  ts.spawn do discard <| accepted.send (← l.accept)
  let some client ← tcp.dial l.addr | throw <| IO.userError "tcp dial refused"
  ts.joinAll
  let some (some server) ← accepted.recv | throw <| IO.userError "tcp accept failed"
  l.close
  return (client, server)

/-- A TCP connection whose peer is gone with a reset: the peer's end
holds unread bytes when its last reference goes, so the runtime closes
its handle, and the kernel answers with an RST. Only the dialer's end
leaves this function. -/
private def tcpResetPeer : Async Connection := do
  let (client, server) ← tcpPair
  client.write (b "never read")
  -- The peer's end goes out of scope here, unread.
  let _ := server
  return client

/-- Wait for a native promise of the socket API of the runtime. -/
private def awaitRaw {α : Type} (p : IO.Promise (Except IO.Error α)) : Async (Except IO.Error α) :=
  try .ok <$> Std.Async.Async.ofPromise (pure p) catch e => pure (.error e)

/-- A TCP connection whose peer end is a raw socket of the runtime: the
dialer's `Connection`, and the accepted socket. The raw end reads below
the transport, so a check can see an RST that `Connection.read` answers
as EOF. -/
private def tcpRawPeer : Async (Connection × Tcp.Socket) := do
  let listener ← Std.Internal.UV.TCP.Socket.new
  listener.bind (.v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, 0⟩)
  listener.listen 1
  let some addr := Tcp.multiaddrOf (← listener.getSockName)
    | throw <| IO.userError "the raw listener has no multiaddr"
  let accepted ← listener.accept
  let some client ← Tcp.transport.dial addr | throw <| IO.userError "tcp dial refused"
  -- The dial has connected, so the accept resolves.
  match ← awaitRaw accepted with
  | .ok server => return (client, server)
  | .error e => throw e

/-- A loopback address where a connect hangs, and the sockets that keep
it so. A raw listener with a backlog of 0 never accepts, and the helper
fills its accept queue with raw connects until one stays pending. A
kernel drops the SYN of a connect to a full queue, so every connect
after that one hangs too, and no packet leaves the machine. The helper
counts the queue, since its length differs between kernels. `none` when
8 connects all complete: the platform does not stall a connect this
way.

The helper polls each connect for 500 ms of real time. A task parked on
a connect that never ends would have no close to wake it (PRINCIPLES
3.1), so the helper parks on nothing but its own timer. -/
private def stalledAddr : Async (Option (Multiaddr × Array Tcp.Socket)) := do
  let listener ← Std.Internal.UV.TCP.Socket.new
  listener.bind (.v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, 0⟩)
  listener.listen 0
  let sa ← listener.getSockName
  let some addr := Tcp.multiaddrOf sa | return none
  let mut held : Array Tcp.Socket := #[listener]
  for _ in [0:8] do
    let c ← Std.Internal.UV.TCP.Socket.new
    let p ← c.connect sa
    held := held.push c
    let mut pending := true
    for _ in [0:50] do
      if ← IO.hasFinished p.result? then
        pending := false
        break
      select #[← Park.sleep 10 ()]
    if pending then return some (addr, held)
  return none

/-- The TCP transport over loopback (unit 2 milestones). -/
private def tcpChecks (r : Runner) : Async Unit := do
  -- Dial, listen, and echo. The listener names the port that the system
  -- picked. 256 KiB crosses many reads and writes, and the echo writes
  -- back while the client still writes, so the back-pressure runs both
  -- ways.
  do
    let tcp := Tcp.transport
    let l ← tcp.listen (← ma "/ip4/127.0.0.1/tcp/0")
    r.check "a TCP listener on port 0 names the port it got"
      (l.addr != (← ma "/ip4/127.0.0.1/tcp/0"))
    let owner ← TaskSet.new
    owner.spawn (Sim.serveEcho l owner)
    let some c ← tcp.dial l.addr | throw <| IO.userError "tcp dial refused"
    r.check "the TCP dialer's remote address is the listener's" (c.remoteAddr == l.addr)
    let big := ByteArray.mk (Array.ofFn (n := 256 * 1024) fun i => UInt8.ofNat (i.val % 251))
    let writer ← TaskSet.new
    writer.spawn (c.write big)
    let echoed ← c.readExactly big.size
    writer.joinAll
    r.check "TCP echo returns 256 KiB whole" (echoed.any fun (x, _) => x == big)
    c.close
    l.close
    owner.joinAll

  -- Close wakes the parked read with EOF, a second close does nothing,
  -- and the peer reads the FIN as EOF.
  do
    let (client, server) ← tcpPair
    let got : OnceRef (Option (Option ByteArray)) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do got.set (some (← client.read))
    client.close
    ts.joinAll
    r.check "TCP close wakes a parked read with EOF" ((← got.get).any (·.isNone))
    client.close
    r.check "a second TCP close does nothing" ((← client.read).isNone)
    r.check "the TCP peer reads the FIN as EOF" ((← server.read).isNone)
    server.close

  -- A write after the teardown throws, and the read stays at EOF. The
  -- path of a failed write runs the same teardown as `close`.
  do
    let (client, server) ← tcpPair
    client.close
    let thrown ← try client.write (b "late"); pure false catch _ => pure true
    r.check "a TCP write after the teardown throws" thrown
    r.check "the TCP read stays at EOF after the teardown" ((← client.read).isNone)
    server.close

  -- A write that fails on the socket: the peer reset, so the kernel
  -- refuses our sends. The writes go on until one throws. On loopback
  -- the RST arrives at once, and the bound only stops a broken run from
  -- looping forever. The failed write tears the connection down, so the
  -- read then sees EOF.
  do
    let client ← tcpResetPeer
    let chunk := ByteArray.mk (Array.replicate 65536 0x5a)
    let mut failed := false
    for _ in [0:1000] do
      try client.write chunk catch _ => failed := true
      if failed then break
    r.check "a TCP write to a reset peer throws" failed
    r.check "the failed TCP write tore the connection down: the read sees EOF"
      ((← client.read).isNone)

  -- A connect that hangs fails at the dial deadline. The address is a
  -- loopback listener with a full accept queue (`stalledAddr`), so the
  -- kernel drops our SYN, and only the deadline can end the dial.
  match ← stalledAddr with
  | none =>
    r.skip "a TCP connect that hangs fails at the dial deadline"
      "8 connects to a full backlog-0 queue all completed: this platform does not stall them"
  | some (addr, held) =>
    let tc ← TestClock.new
    let answer : OnceRef (Option String) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do
      let res ← try
          discard <| (Tcp.transport tc.clock).dial addr
          pure "connected"
        catch
          | .timeExpired .. => pure "expired"
          | e => pure s!"other: {e}"
      answer.set (some res)
    r.check "the TCP dial arms its connect deadline" (← tc.nextTimer)
    tc.advance unauthDeadlineMs
    ts.joinAll
    -- `held` is named here, so the sockets that fill the queue live
    -- through the dial.
    r.check s!"a TCP connect that hangs fails at the dial deadline ({held.size} sockets fill the queue)"
      ((← answer.get) == some "expired")
    tc.close

  -- A teardown with a write in flight to a peer that stops reading. The
  -- write would never complete, and its request would hold the socket
  -- forever, so the teardown aborts it. The peer then drains what reached
  -- it and meets the reset. Without the abort, the drain would let the
  -- writes complete and end with the FIN, as EOF. The peer is a raw
  -- socket, since `Connection.read` answers the reset as EOF too. The
  -- writer gets 300 ms of real time to fill the buffers and park.
  do
    let (client, server) ← tcpRawPeer
    let chunk := ByteArray.mk (Array.replicate (1 <<< 20) 0x5a)
    let ts ← TaskSet.new
    ts.spawn do
      try
        for _ in [0:256] do client.write chunk
      catch _ => pure ()
    select #[← Park.sleep 300 ()]
    client.close
    ts.joinAll
    r.check "TCP close wakes a write parked on a peer that stops reading" true
    let mut reset := false
    for _ in [0:100000] do
      match ← awaitRaw (← server.recv? 65536) with
      | .ok (some _) => pure ()
      | .ok none => break
      | .error _ =>
        reset := true
        break
    r.check "the teardown aborted the stuck write: the peer meets a reset" reset

  -- The peer's reset ends the read as EOF (module doc of `Streams.Tcp`,
  -- "The peer's reset"). The peer of `tcpResetPeer` closes with unread
  -- bytes, so its kernel answers with an RST. The read gets one second
  -- of real time. Past it, the close wakes the read, and the check tells
  -- the two apart by the cell that the read fills before the close.
  do
    let client ← tcpResetPeer
    let got : OnceRef (Option (Except String (Option ByteArray))) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do
      let r ← try .ok <$> client.read catch e => pure (.error (toString e))
      got.set (some r)
    for _ in [0:100] do
      if (← got.get).isSome then break
      select #[← Park.sleep 10 ()]
    let answer ← got.get
    client.close
    ts.joinAll
    let seen := match answer with
      | none => "no answer within 1 s"
      | some (.ok none) => "EOF"
      | some (.ok (some b)) => s!"{b.size} bytes"
      | some (.error e) => s!"a fault: {e}"
    r.check s!"a TCP read that meets the peer's reset answers EOF (it answered {seen})"
      (match answer with | some (.ok none) => true | _ => false)
    r.check "the reset tore the connection down: the read stays at EOF"
      ((← client.read).isNone)

  -- A listener close wakes the parked accept with none.
  do
    let l ← Tcp.transport.listen (← ma "/ip4/127.0.0.1/tcp/0")
    let woke : OnceRef (Option Bool) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do woke.set (some (← l.accept).isNone)
    l.close
    ts.joinAll
    r.check "TCP listener close wakes a parked accept with none" ((← woke.get) == some true)

  -- A closed listener stops listening: a dial is refused, and the port
  -- takes a new listener. The runtime closes the released handle on the
  -- libuv loop, a moment after `close`, so the check tries again for up
  -- to one second in real time. The listener value stays in scope, so
  -- the release comes from `close` alone.
  do
    let l ← Tcp.transport.listen (← ma "/ip4/127.0.0.1/tcp/0")
    l.close
    let mut refused := false
    for _ in [0:100] do
      if (← Tcp.transport.dial l.addr).isNone then
        refused := true
        break
      select #[← Park.sleep 10 ()]
    r.check "a TCP dial with no listener (a closed one) returns none" refused
    let again ← try
        let l2 ← Tcp.transport.listen l.addr
        l2.close
        pure true
      catch _ => pure false
    r.check "the port of a closed TCP listener takes a new listener" again
    -- A use after the checks: the value is still held through them.
    r.check "the closed listener still names its address" (l.addr == l.addr)

  -- A silent peer: the read of the unauthenticated phase parks, the
  -- deadline closes the connection, the read ends, and the peer reads
  -- the FIN.
  do
    let tc ← TestClock.new
    let (client, server) ← tcpPair
    let answer : OnceRef (Option (Except Conc.Error (Option ByteArray))) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do answer.set (some (← client.withinUnauthDeadline tc.clock client.read))
    r.check "the TCP phase arms its deadline" (← tc.nextTimer)
    tc.advance unauthDeadlineMs
    ts.joinAll
    r.check "a silent TCP peer fails at the deadline"
      (match ← answer.get with | some (.error .deadlineExpired) => true | _ => false)
    r.check "the expiry sent the FIN, and the TCP peer reads EOF" ((← server.read).isNone)
    server.close
    tc.close

/-- Seeded random socket addresses, IPv4 and IPv6 in turns. -/
private def randomSockets (count : Nat) (g : StdGen) : List Std.Net.SocketAddress :=
  let draw (g : StdGen) (hi : Nat) : Nat × StdGen := randNat g 0 hi
  (Nat.fold count (fun i _ (acc, g) =>
    let (port, g) := draw g 65535
    if i % 2 == 0 then
      let (a, g) := draw g 255
      let (b, g) := draw g 255
      let (c, g) := draw g 255
      let (d, g) := draw g 255
      let ip := Std.Net.IPv4Addr.ofParts (UInt8.ofNat a) (UInt8.ofNat b) (UInt8.ofNat c)
        (UInt8.ofNat d)
      (.v4 ⟨ip, UInt16.ofNat port⟩ :: acc, g)
    else
      -- `Nat.fold` draws the 8 segments, and gives the generator to the
      -- next draw.
      let (segs, g) := Nat.fold 8 (fun _ _ (ss, g) =>
        let (s, g) := draw g 65535
        (ss.push (UInt16.ofNat s), g)) (#[], g)
      let seg (k : Nat) : UInt16 := segs.getD k 0
      let ip := Std.Net.IPv6Addr.ofParts (seg 0) (seg 1) (seg 2) (seg 3) (seg 4) (seg 5)
        (seg 6) (seg 7)
      (.v6 ⟨ip, UInt16.ofNat port⟩ :: acc, g)) ([], g)).1

/-- The TCP mapping on seeded random socket addresses: each one maps to
a multiaddr, and the multiaddr maps back to the same address. The check
compares the text forms, which the runtime prints in one canonical
form. -/
private def tcpMappingChecks (r : Runner) : IO Unit := do
  let socks := randomSockets 300 (mkStdGen 47)
  let fails := socks.filter fun sa =>
    match Tcp.multiaddrOf sa with
    | some m => (Tcp.socketAddress? m).map toString != some (toString sa) || !Tcp.handles m
    | none => true
  r.check s!"300 random socket addresses map to a multiaddr and back: {(fails.take 3).map toString}"
    fails.isEmpty

def Streams.run (r : Runner) : IO Unit := do
  r.section "streams" "(packages/net/streams/docs/PLAN.md, test milestones, units 1 and 2)"
  let all : Async Unit := do
    simChecks r
    closeChecks r
    readerChecks r
    manyFramesChecks r
    framingChecks r
    streamChecks r
    deadlineChecks r
    tcpAddressChecks r
    tcpChecks r
  all.run
  harnessChecks r
  tcpMappingChecks r

end Tests
