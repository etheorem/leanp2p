import Tests.Support
import Proto
import Bytes
import Varint
import Conc
import Streams.Error
import Streams.Framing
import Streams.Stream
import Libp2p.Protocols
import Libp2p.Protocols.Identity
import Libp2p.Core
import Libp2p.Host

/-!
# Identify and ping suite

Mirrors `vendor/specs/ping/ping.md` (32-byte echo, protocol id
`/ipfs/ping/1.0.0`) and the captured go-libp2p Identify protobuf
(`identify-go.json`). The suite replays the vector and drives the
pure `Identify.validate` and `Ping.checkEcho` checks. The real key
fixtures and the host stand-in run here, and the address checks run the
real Multiformats decoder, so every validate outcome appears in a
check.

The exchange cases cover the identify client against the responder
handler, the push handler against the in-memory peerstore double, the
client deadline on the test clock, and the ping echo, with the
initiator on end `a` and the handler on end `b`. The exchanges run over
a private pair of `Conc.Pipe` values, wired as two `Streams.Stream`
ends.
-/

set_option autoImplicit false

namespace Tests.Protocols

open Libp2p.Protocols
open Libp2p.Identity

/-- A real Ed25519 public key for the suite. A 32-byte key needs no
native call, and the key round trips through the wire form. -/
private def testKey (tag : UInt8) : PubKey :=
  PubKey.ofEd25519 ⟨ByteArray.mk (Array.replicate 32 tag), by simp [ByteArray.size]⟩

/-- A validated inline peer id, one per suite peer. -/
private def testPeer (tag : UInt8) : PeerId :=
  PeerId.inline (ByteArray.mk #[tag]) (by
    simp [ByteArray.size, Libp2p.Identity.maxInlineKeyBytes])

/-- The model decode over the byte list. -/
private def decodeModel (bs : List Nat) : Except Pb.Error (Identify × List Nat) :=
  Pb.decodeMessage? (α := Identify) bs

/-- The production decode over a byte array. -/
private def decodeByteArray (bs : ByteArray) : Except Pb.Error (Identify × Nat) :=
  Pb.decodeMessageB? (α := Identify) bs

/-- The all-absent identify message. -/
private def emptyIdentify : Identify := ⟨none, [], [], none, none, none, none⟩

/-- The encoding of a message, through the shared Proto encoder. -/
private def msgPayload (m : Identify) : List Nat :=
  Pb.encodeMessage m

private def testHost : IO Libp2p.Host.Host := do
  let key ← match PrivKey.ofData? .ed25519 (ByteArray.mk (Array.replicate 32 1)) with
    | .ok key => pure key
    | .error e => throw (IO.userError s!"test key: {repr e}")
  match ← Libp2p.Host.Host.new { identity := key, transports := [], security := [], muxers := [] } with
  | .ok host => pure host
  | .error e => throw (IO.userError s!"test host: {repr e}")

/-! ## The private stream pair

Two `Conc.Pipe` values wired like the spike's `mkSplit`
(`Tests/PingId.lean`): end `a` reads `ba` and writes `ab`, end `b`
reads `ab` and writes `ba`. The adapter's `close` is a no-op, so one
pair serves the swapped-role exchange; the cases that need an end
close the pipe directly. `reset` closes the pipe the end reads, so a
reset reaches the parked read. -/

/-- The pair: the two stream ends and the two pipes, for the cases
that close a pipe directly. -/
private structure Pair where
  a : Streams.Stream
  b : Streams.Stream
  ab : Conc.Pipe
  ba : Conc.Pipe

/-- One stream end over the two pipes. -/
private def mkEnd (readP writeP : Conc.Pipe) : Streams.Stream := {
  read := do
    match ← readP.read with
    | none => return .ok none
    | some chunk => return .ok (some chunk)
  write := fun bytes =>
    (Except.mapError (fun e => match e with
      | Conc.Error.closed => Streams.Error.closed
      | Conc.Error.deadlineExpired => Streams.Error.timeout)) <$> writeP.write bytes
  close := pure ()
  reset := readP.close }

/-- The pair: `a` reads `ba` and writes `ab`; `b` reads `ab` and
writes `ba`. -/
private def mkPair : BaseIO Pair := do
  let ab ← Conc.Pipe.new 4
  let ba ← Conc.Pipe.new 4
  return { a := mkEnd ba ab, b := mkEnd ab ba, ab, ba }

/-- True when the answer is `.ok (some _)`. -/
private def isOkSome {ε α : Type} (x : Except ε (Option α)) : Bool :=
  match x with
  | .ok (some _) => true
  | _ => false

/-- True when the answer is `.ok none`. -/
private def isOkNone {ε α : Type} (x : Except ε (Option α)) : Bool :=
  match x with
  | .ok none => true
  | _ => false

/-- True when the handler answer is a protocol error. -/
private def isProtocolError (x : Except Libp2p.Core.Error Unit) : Bool :=
  match x with
  | .error (.protocol _) => true
  | _ => false

/-- Run the handler on `s`, and fail the task when the handler
answers an error. -/
private def runHandler (h : Libp2p.Core.StreamHandler)
    (s : Streams.Stream) (peer : PeerId := testPeer 1) : Conc.Async Unit := do
  let res : Except Libp2p.Core.Error Unit ← h.handle { remotePeer := peer, remoteAddr := Multiformats.Multiaddr.empty } s
  match res with
  | .error e => throw (IO.userError s!"the handler answered {repr e}")
  | .ok () => pure ()

/-- The exchange cases, on the test clock and the private pair. -/
private def asyncChecks (r : Runner) : Conc.Async Unit := do
  -- identify: the responder round trip
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let key := testKey 1
    let pid : PeerId := peerIdOfPubKey key
    let addr := [4, 127, 0, 0, 1, 6, 138, 43]
    let agent := "leanp2p"
    let protocols := ["/ipfs/id/1.0.0"]
    let ts ← Conc.TaskSet.new
    ts.spawn do
      runHandler (Identify.respondHandler key [addr] protocols none agent none) pair.b
    let res ← Identify.client pair.a tc.clock 1000 (some pid)
    ts.joinAll
    r.check "identify e2e responder round trip accepted"
      (match res with
       | .ok (some (m, got)) =>
           decide (got = pid) && m.agentVersion == some agent && m.protocols == protocols
       | _ => false)
    tc.close

  -- identify: the same pair runs the exchange twice, roles swapped
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let key := testKey 3
    let pid : PeerId := peerIdOfPubKey key
    let agent := "leanp2p"
    let ts ← Conc.TaskSet.new
    ts.spawn do
      runHandler (Identify.respondHandler key [] [] none agent none) pair.b
    let first ← Identify.client pair.a tc.clock 1000 (some pid)
    ts.joinAll
    ts.spawn do
      runHandler (Identify.respondHandler key [] [] none agent none) pair.a
    let second ← Identify.client pair.b tc.clock 1000 (some pid)
    ts.joinAll
    r.check "identify e2e round trip both directions"
      (isOkSome first && isOkSome second)
    tc.close

  -- identify: the push handler updates the peerstore
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let store ← testHost
    let key := testKey 1
    let pid : PeerId := peerIdOfPubKey key
    let addr := [4, 127, 0, 0, 1, 6, 138, 43]
    let msg := Identify.respond key [addr] [] none "" none
    match Streams.Framing.encodeB? .uvarint Constants.identifyCap
        (Pb.encodeMessageB msg) with
    | none => r.check "identify e2e push updates the peerstore and reads back" false
    | some frame =>
        let ts ← Conc.TaskSet.new
        ts.spawn do
          runHandler (Identify.pushHandler store tc.clock 1000) pair.b pid
        discard <| pair.a.write frame
        ts.joinAll
        let stored ← store.addrsOf pid
        r.check "identify e2e push updates the peerstore and reads back"
          (stored.map Multiformats.Multiaddr.toBytes == [addr])
    tc.close

  -- identify: a second push of the same addresses grows nothing
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let store ← testHost
    let key := testKey 1
    let pid : PeerId := peerIdOfPubKey key
    let addr := [4, 127, 0, 0, 1, 6, 138, 43]
    let msg := Identify.respond key [addr] [] none "" none
    match Streams.Framing.encodeB? .uvarint Constants.identifyCap
        (Pb.encodeMessageB msg) with
    | none => r.check "identify e2e push redial adds no duplicate address" false
    | some frame =>
        let ts ← Conc.TaskSet.new
        ts.spawn do
          runHandler (Identify.pushHandler store tc.clock 1000) pair.b pid
        discard <| pair.a.write frame
        ts.joinAll
        let ts2 ← Conc.TaskSet.new
        ts2.spawn do
          runHandler (Identify.pushHandler store tc.clock 1000) pair.b pid
        discard <| pair.a.write frame
        ts2.joinAll
        let stored ← store.addrsOf pid
        r.check "identify e2e push redial adds no duplicate address"
          (stored.map Multiformats.Multiaddr.toBytes == [addr])
    tc.close

  -- identify: the push sender announces the record and the receiver stores it
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let store ← testHost
    let key := testKey 7
    let pid : PeerId := peerIdOfPubKey key
    let addr := [4, 127, 0, 0, 1, 6, 138, 43]
    let ts ← Conc.TaskSet.new
    ts.spawn do
      runHandler (Identify.pushHandler store tc.clock 1000) pair.b pid
    let sent ← Identify.pushTo key [addr] [] none "" none
      { pair.a with close := pair.ab.close }
    ts.joinAll
    let ended ← pair.b.read
    let stored ← store.addrsOf pid
    r.check "identify e2e push sender announces the record"
      ((match sent with
        | Except.ok _ => true
        | Except.error _ => false) && stored == [addr])
    r.check "identify e2e push sender half-closes the stream" (isOkNone ended)
    tc.close

  -- identify: the client rejects an over-cap frame before the body
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let overCapPrefix := Bytes.ofNatList (Streams.Framing.encodeLength .uvarint 65537)
    discard <| pair.b.write overCapPrefix
    pair.ba.close
    let res ← Identify.client pair.a tc.clock 1000 none
    r.check "identify client rejects an over-cap frame before the body"
      (failsWith (Identify.Error.badMessage (.framing .malformed)) res)
    tc.close

  -- identify: the client rejects a zero-length frame
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    discard <| pair.b.write (Bytes.ofNatList (Streams.Framing.encodeLength .uvarint 0))
    let res ← Identify.client pair.a tc.clock 1000 none
    r.check "identify client rejects a zero-length frame"
      (failsWith Identify.Error.emptyFrame res)
    tc.close

  -- identify: the client answers absent on a clean close in the header
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    pair.ba.close
    let res ← Identify.client pair.a tc.clock 1000 none
    r.check "identify client returns absent on a clean close in the header"
      (isOkNone res)
    tc.close

  -- identify: the client hits the deadline on a silent peer
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let answer : Conc.OnceRef (Option (Except Identify.Error (Option (Identify × PeerId)))) ←
      Conc.OnceRef.new none
    let ts ← Conc.TaskSet.new
    ts.spawn do
      answer.set (some (← Identify.client pair.a tc.clock 50 none))
    let armed ← tc.nextTimer
    tc.advance 50
    ts.joinAll
    let res ← answer.get
    r.check "identify client hits the deadline on a silent peer"
      (armed && res.any (failsWith Identify.Error.timeout))
    tc.close

  -- ping: the echo round trip measures the rtt
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let payload := Bytes.ofNatList (List.replicate 32 7)
    let ts ← Conc.TaskSet.new
    ts.spawn do
      runHandler Ping.pingHandler pair.b
    let res ← Ping.ping pair.a tc.clock payload
    pair.ab.close
    ts.joinAll
    r.check "ping e2e echo round trip measures the rtt" (isOkSome res)
    tc.close

  -- ping: an altered echo is rejected
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let payload := Bytes.ofNatList (List.replicate 32 7)
    let altered := Bytes.ofNatList (0 :: List.replicate 31 7)
    let ts ← Conc.TaskSet.new
    ts.spawn do
      discard <| pair.b.write altered
      discard <| pair.b.read
    let res ← Ping.ping pair.a tc.clock payload
    ts.joinAll
    r.check "ping e2e altered echo rejected" (failsWith Ping.Error.mismatch res)
    tc.close

  -- ping: a partial echo at the end of the stream is rejected
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let payload := Bytes.ofNatList (List.replicate 32 7)
    let ts ← Conc.TaskSet.new
    ts.spawn do
      discard <| pair.b.write (Bytes.ofNatList (List.replicate 31 7))
      pair.ba.close
    let res ← Ping.ping pair.a tc.clock payload
    ts.joinAll
    r.check "ping e2e partial echo at EOF rejected" (failsWith Ping.Error.truncated res)
    tc.close

  -- ping: an echo longer than one payload is rejected
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let payload := Bytes.ofNatList (List.replicate 32 7)
    let ts ← Conc.TaskSet.new
    ts.spawn do
      discard <| pair.b.write (Bytes.ofNatList (List.replicate 33 7))
    let res ← Ping.ping pair.a tc.clock payload
    ts.joinAll
    r.check "ping e2e 33-byte echo rejected"
      (failsWith (Ping.Error.wrongSize 33) res)
    tc.close

  -- ping: an echo whose last read crosses 32 bytes is rejected
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let payload := Bytes.ofNatList (List.replicate 32 7)
    let ts ← Conc.TaskSet.new
    ts.spawn do
      discard <| pair.b.write (Bytes.ofNatList (List.replicate 16 7))
      discard <| pair.b.write (Bytes.ofNatList (List.replicate 17 7))
    let res ← Ping.ping pair.a tc.clock payload
    ts.joinAll
    r.check "ping e2e 16+17-byte echo rejected"
      (failsWith (Ping.Error.wrongSize 33) res)
    tc.close

  -- ping: an echo split across chunks is accepted
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let payload := Bytes.ofNatList (List.replicate 32 7)
    let half := List.replicate 16 7
    let ts ← Conc.TaskSet.new
    ts.spawn do
      discard <| pair.b.write (Bytes.ofNatList half)
      discard <| pair.b.write (Bytes.ofNatList half)
      discard <| pair.b.read
    let res ← Ping.ping pair.a tc.clock payload
    ts.joinAll
    r.check "ping e2e echo split across chunks accepted" (isOkSome res)
    tc.close

  -- ping: the handler echoes a payload written in two chunks
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let payload := List.replicate 32 7
    let half := List.replicate 16 7
    let ts ← Conc.TaskSet.new
    ts.spawn do
      runHandler Ping.pingHandler pair.b
    discard <| pair.a.write (Bytes.ofNatList half)
    discard <| pair.a.write (Bytes.ofNatList half)
    let echo ← pair.a.read
    let ok := match echo with
      | .ok (some chunk) => succeedsWith () (Ping.checkEcho payload (Bytes.toNatList chunk))
      | _ => false
    pair.ab.close
    ts.joinAll
    r.check "ping e2e handler echoes a split write" ok
    tc.close

  -- ping: a partial payload at the end of the stream is a protocol error
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let answer : Conc.OnceRef (Option (Except Libp2p.Core.Error Unit)) ←
      Conc.OnceRef.new none
    let ts ← Conc.TaskSet.new
    ts.spawn do
      answer.set (some (← Ping.pingHandler.handle { remotePeer := testPeer 1, remoteAddr := Multiformats.Multiaddr.empty } pair.b))
    discard <| pair.a.write (Bytes.ofNatList (List.replicate 20 7))
    pair.ab.close
    ts.joinAll
    let res ← answer.get
    r.check "ping e2e handler partial payload at EOF is a protocol error"
      (res.any isProtocolError)
    tc.close

  -- ping: a wrong outgoing size is rejected before the write
  do
    let pair ← mkPair
    let tc ← Conc.TestClock.new
    let res ← Ping.ping pair.a tc.clock (Bytes.ofNatList (List.replicate 31 7))
    r.check "ping e2e wrong outgoing size rejected"
      (failsWith (Ping.Error.wrongSize 31) res)
    tc.close

def run (r : Runner) : IO Unit := do
  r.section "protocols"
    "libp2p/specs identify/README.md + ping/ping.md + captured go Identify protobuf"

  let j ← loadJson "identify-go.json"
  let respHex ← jStr "identify-go.json" j "responseHex"
  let pkHex ← jStr "identify-go.json" j "publicKeyHex"
  let wantProtocols ← jStrs "identify-go.json" j "protocols"
  let wantAgent ← jStr "identify-go.json" j "agentVersion"
  let jsonVersion ← jStr "identify-go.json" j "protocolVersion"
  let wantPeerId ← jStr "identify-go.json" j "peerId"

  match Bytes.ofHex? respHex with
  | none =>
      r.check "identify vector length prefix is 330" false
      r.check "identify vector decodes (model)" false
      r.check "identify vector decodes (bytearray)" false
      r.check "identify vector model equals bytearray" false
  | some respBytes =>
      match Varint.decode? (Bytes.toNatList respBytes) with
      | .error _ =>
          r.check "identify vector length prefix is 330" false
          r.check "identify vector decodes (model)" false
          r.check "identify vector decodes (bytearray)" false
          r.check "identify vector model equals bytearray" false
      | .ok (len, payload) =>
          -- the captured response carries a uvarint length prefix;
          -- the prefix must equal 330 and the remaining length
          r.check "identify vector length prefix is 330"
            (len.val == 330 && len.val == payload.length)
          match decodeModel payload with
          | .error _ =>
              r.check "identify vector decodes (model)" false
              r.check "identify vector decodes (bytearray)" false
              r.check "identify vector model equals bytearray" false
          | .ok (m, _) =>
              r.check "identify vector decodes (model)" true
              let mB := decodeByteArray (Bytes.ofNatList payload)
              r.check "identify vector decodes (bytearray)"
                (match mB with
                 | .ok (_, used) => used == payload.length
                 | .error _ => false)
              r.check "identify vector model equals bytearray"
                (match mB with
                 | .ok (m2, _) => m2 == m
                 | .error _ => false)
              r.check "identify vector re-encodes byte-exact"
                (Pb.encodeMessage m == payload)
              r.check "identify vector encodes deterministically"
                (Pb.encodeMessage m == Pb.encodeMessage m)
              match Bytes.ofHex? pkHex with
              | none =>
                  r.check "identify vector publicKey equals JSON publicKeyHex" false
              | some pkBytes =>
                  -- the wire carries the PublicKey protobuf: field 1 is
                  -- the ed25519 key type, field 2 holds the 32 key bytes
                  r.check "identify vector publicKey equals JSON publicKeyHex"
                    (m.publicKey == some ([8, 1, 18, 32] ++ Bytes.toNatList pkBytes))
                  -- the derivation runs the real identity package: parse the
                  -- serialized key, derive its peer id, compare the text form
                  match unmarshalPubKey? ([8, 1, 18, 32] ++ Bytes.toNatList pkBytes) with
                  | some k =>
                      r.check "identify vector peer id matches the JSON peerId"
                        ((peerIdOfPubKey k).toString == wantPeerId)
                  | none =>
                      r.check "identify vector peer id matches the JSON peerId" false
              r.check "identify vector protocols equal JSON protocols in order"
                (m.protocols == wantProtocols)
              r.check "identify vector agentVersion equals JSON agentVersion"
                (m.agentVersion == some wantAgent)
              -- the binary form of /ip4/127.0.0.1/tcp/35371; the wire
              -- carries bytes, not text
              r.check "identify vector listenAddrs has one entry, the binary form of JSON listenAddrs[0]"
                (m.listenAddrs == [[4, 127, 0, 0, 1, 6, 138, 43]])
              -- the full captured bytes, prefix and payload, through `clientCore`
              r.check "identify vector through the client core"
                (match Identify.clientCore (Bytes.toNatList respBytes) none with
                 | .ok (some (m2, _)) => m2 == m
                 | _ => false)
              -- the wire carries the empty string, the JSON says
              -- /ipfs/1.0.0; the suite asserts the wire value
              r.check "identify vector protocolVersion wire delta recorded"
                (m.protocolVersion == some "" && jsonVersion == "/ipfs/1.0.0")

  -- validate: rejection and acceptance, over a real key and the
  -- real address decoder
  r.check "identify over-cap payload rejected before decode"
    (failsWith Identify.Error.overCap
      (Identify.validate (List.replicate 65537 0) none))
  r.check "identify empty payload has no key"
    (failsWith Identify.Error.missingKey (Identify.validate [] none))
  let noKey := { emptyIdentify with agentVersion := some "leanp2p" }
  r.check "identify missing publicKey rejected"
    (failsWith Identify.Error.missingKey (Identify.validate (msgPayload noKey) none))
  let badKeyMsg := { emptyIdentify with publicKey := some [] }
  r.check "identify undecodable publicKey rejected"
    (failsWith Identify.Error.badKey (Identify.validate (msgPayload badKeyMsg) none))
  let otherId : PeerId := testPeer 9
  let mismatchMsg := { emptyIdentify with publicKey := some (marshalPubKey (testKey 1)) }
  r.check "identify key mismatch rejected"
    (failsWith Identify.Error.keyMismatch
      (Identify.validate (msgPayload mismatchMsg) (some otherId)))
  -- `[4]` is an ip4 tag with no address bytes: the real decoder
  -- rejects it. The empty list is a valid empty address, so it cannot
  -- stand in for a bad address.
  let badListen := { emptyIdentify with publicKey := some (marshalPubKey (testKey 1)), listenAddrs := [[4]] }
  r.check "identify invalid listen address rejected"
    (failsWith Identify.Error.badAddress (Identify.validate (msgPayload badListen) none))
  let badObs := { emptyIdentify with publicKey := some (marshalPubKey (testKey 1)), observedAddr := some [4] }
  r.check "identify invalid observed address rejected"
    (failsWith Identify.Error.badAddress (Identify.validate (msgPayload badObs) none))
  -- a continuation byte with no terminator: truncated framing
  r.check "identify malformed protobuf rejected"
    (failsWith (Identify.Error.badMessage (.framing .truncated))
      (Identify.validate [0x80] none))
  let good := { emptyIdentify with publicKey := some (marshalPubKey (testKey 1)) }
  let pid : PeerId := peerIdOfPubKey (testKey 1)
  r.check "identify accepted with matching derivation"
    (succeedsWith (good, pid) (Identify.validate (msgPayload good) (some pid)))
  r.check "identify accepted with no expected id"
    (succeedsWith (good, pid) (Identify.validate (msgPayload good) none))

  -- ping: the spec constants and the echo check
  r.check "ping protocol id constant" (Ping.protocolId.toString == "/ipfs/ping/1.0.0")
  r.check "ping payload size 32" (Ping.payloadSize == 32)
  let sent := List.replicate 32 7
  r.check "ping echo exact accepted" (succeedsWith () (Ping.checkEcho sent sent))
  r.check "ping echo short rejected"
    (failsWith (Ping.Error.wrongSize 31) (Ping.checkEcho sent (List.replicate 31 7)))
  r.check "ping echo long rejected"
    (failsWith (Ping.Error.wrongSize 33) (Ping.checkEcho sent (List.replicate 33 7)))
  let altered := 0 :: List.replicate 31 7
  r.check "ping echo altered rejected"
    (failsWith .mismatch (Ping.checkEcho sent altered))

  Conc.Async.run (asyncChecks r)

end Tests.Protocols
