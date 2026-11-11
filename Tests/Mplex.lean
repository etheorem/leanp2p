import Tests.Support
import Libp2p.Core.Mux
import Libp2p.Mux
import Libp2p.Mux.Mplex.Wire
import Libp2p.Mux.Mplex.State
import Conc
import Streams
import Multiformats

/-!
# Mplex suite (unit W5.10)

The unit 2 milestones of `packages/libp2p/mux/docs/PLAN.md`, over
`Mux.mplex` and its modules:

* the codec: the spec's header layout, the round trip, the 1 MiB cap,
  the 9-byte header bound, and the `ByteArray` decoder pinned to the
  model;
* the stream table: the identity rule, half-close, and reset, as pure
  transitions;
* the session over the in-memory sim pair: the identity rule between
  two sessions, the three half-close cases, reset in both directions,
  and the hostile inputs of a raw peer.
-/

set_option autoImplicit false

/-- Equality of answers, for the checks below. `Except` derives no
`BEq`, and the instance is private to this suite. -/
private instance exceptBEq {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e, .error f => e == f
    | _, _ => false

namespace Tests.Mplex.Wire

open Bytes
open Libp2p.Mux.Mplex.Wire

private def cap : Nat := Libp2p.Mux.mplexMessageCap

private def allFlags : List Flag :=
  [.newStream, .messageReceiver, .messageInitiator, .closeReceiver,
   .closeInitiator, .resetReceiver, .resetInitiator]

private def isTruncated {α : Type} : Except DecodeError α → Bool
  | .error .truncated => true
  | _ => false

private def isMalformed {α : Type} : Except DecodeError α → Bool
  | .error .malformed => true
  | _ => false

private def hello : Message := { flag := .messageInitiator, id := 9, payload := [104, 101, 108, 108, 111] }

private def emptyReceiver : Message := { flag := .messageReceiver, id := 127, payload := [] }

/-- The messages of the round-trip checks. -/
private def samples : List Message :=
  [ { flag := .newStream, id := 0, payload := (Bytes.ofString "/ipfs/ping/1.0.0").toList.map (·.toNat) }
  , hello
  , emptyReceiver
  , { flag := .closeInitiator, id := 128, payload := [] }
  , { flag := .resetReceiver, id := idLimit - 1, payload := [] }
  , { flag := .messageInitiator, id := 3, payload := List.replicate 300 255 } ]

/-- A deterministic byte stream: a linear congruential generator. -/
private def lcg (seed : Nat) : Nat := (seed * 1103515245 + 12345) % 2147483648

/-- `n` pseudo-random bytes, biased toward small values so that headers
and lengths decode often enough to reach the later branches. -/
private def fuzzBytes (seed n : Nat) : List Nat := Id.run do
  let mut s := seed
  let mut out : Array Nat := #[]
  for _ in [0:n] do
    s := lcg s
    let v := (s / 65536) % 256
    out := out.push (if v % 3 == 0 then v else v % 16)
  return out.toList

/-- The `ByteArray` decoder at offset 0 agrees with the model on `l`:
the same answer, the same message, and the same rest. -/
private def pinned (l : List Nat) : Bool :=
  let b := ofNatList l
  match decodeAtB? b 0, decode? l with
  | .ok (f, next), .ok (m, rest) => f.toMessage == m && next + rest.length == l.length
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

def run (r : Runner) : IO Unit := do
  r.section "mplex wire" "vendor/specs/mplex/README.md"
  -- The flag codes of "Flag Values".
  r.check "the seven flags take the codes 0 to 6"
    (allFlags.map Flag.code == [0, 1, 2, 3, 4, 5, 6])
  r.check "every flag code decodes back to its flag"
    (allFlags.all fun f => Flag.ofCode? f.code == some f)
  r.check "code 7 names no flag" (Flag.ofCode? 7 == none)
  -- The header layout: `id * 8 + flag`, as the spike's vectors pin it.
  r.check "NewStream id 5 named demo is 40 4 d e m o"
    (encode { flag := .newStream, id := 5, payload := [100, 101, 109, 111] }
      == [40, 4, 100, 101, 109, 111])
  r.check "MessageReceiver id 1 empty is 9 0"
    (encode { flag := .messageReceiver, id := 1, payload := [] } == [9, 0])
  r.check "CloseInitiator id 3 is 28 0"
    (encode { flag := .closeInitiator, id := 3, payload := [] } == [28, 0])
  r.check "ResetReceiver id 7 is 61 0"
    (encode { flag := .resetReceiver, id := 7, payload := [] } == [61, 0])
  r.check "the largest id takes a 9-byte header"
    ((encode { flag := .resetInitiator, id := idLimit - 1, payload := [] }).length == 10)
  -- The round trip, with and without a rest.
  r.check "every sample decodes back from its encoding"
    (samples.all fun m => decode? (encode m) == .ok (m, []))
  r.check "every sample decodes back with a rest after it"
    (samples.all fun m => decode? (encode m ++ [7, 7]) == .ok (m, [7, 7]))
  r.check "encodeB is encode on ByteArray"
    (samples.all fun m =>
      toNatList (encodeB m.flag m.id (ofNatList m.payload)) == encode m)
  -- The 1 MiB cap, checked straight after the length varint.
  let overCap := Varint.encodeNat (headerValue .messageInitiator 0) ++ Varint.encodeNat (cap + 1)
  r.check "a declared length of cap + 1 is malformed with no body sent"
    (isMalformed (decode? overCap))
  r.check "the ByteArray decoder rejects cap + 1 with no body sent"
    (isMalformed (decodeAtB? (ofNatList overCap) 0))
  let atCap : Message := { flag := .messageInitiator, id := 0, payload := List.replicate cap 1 }
  r.check "a message of exactly cap bytes decodes"
    (decode? (encode atCap) == .ok (atCap, []))
  r.check "a message of exactly cap bytes decodes on ByteArray"
    (match decodeAtB? (ofNatList (encode atCap)) 0 with
      | .ok (f, next) => f.payload.size == cap && next == (encode atCap).length
      | .error _ => false)
  r.check "a cap-sized message missing its last byte is truncated"
    (isTruncated (decode? (encode atCap).dropLast))
  -- The 9-byte varint bound, on the header and on the length.
  r.check "nine continuation bytes in the header are malformed"
    (isMalformed (decode? (List.replicate 9 0x80)))
  r.check "five continuation bytes in the header are truncated"
    (isTruncated (decode? (List.replicate 5 0x80)))
  r.check "nine continuation bytes in the length are malformed"
    (isMalformed (decode? ([16] ++ List.replicate 9 0x80)))
  r.check "a non-minimal header varint is malformed"
    (isMalformed (decode? [0x80, 0x00, 0]))
  r.check "flag code 7 is malformed" (isMalformed (decode? [7, 0]))
  -- The production decoder against the model (CLAUDE.md, "Proofs and
  -- tests", layer 2).
  let encodings := samples.map encode
  r.check "decodeAtB? agrees with decode? on every encoding"
    (encodings.all pinned)
  r.check "decodeAtB? agrees with decode? on every prefix of every encoding"
    (encodings.all fun e => (List.range (e.length + 1)).all fun k => pinned (e.take k))
  r.check "decodeAtB? agrees with decode? on 2000 fuzz inputs"
    ((List.range 2000).all fun i => pinned (fuzzBytes (i + 1) (i % 24)))
  r.check "decodeAtB? agrees with decode? on the hostile inputs"
    ([List.replicate 9 0x80, List.replicate 5 0x80, overCap, [7, 0], [0x80, 0x00, 0]].all pinned)
  -- The decoder reads in place from an offset.
  let two := encode hello ++ encode emptyReceiver
  r.check "decodeAtB? reads the second message at its offset"
    (match decodeAtB? (ofNatList two) (encode hello).length with
      | .ok (f, next) => f.toMessage == emptyReceiver && next == two.length
      | .error _ => false)

end Tests.Mplex.Wire

namespace Tests.Mplex.State

open Libp2p.Mux.Mplex.Wire
open Libp2p.Mux.Mplex.State

private def allFlags : List Flag :=
  [.newStream, .messageReceiver, .messageInitiator, .closeReceiver,
   .closeInitiator, .resetReceiver, .resetInitiator]

/-- `t` holds `key`. -/
private def holds {σ : Type} (t : Table σ) (key : Key) : Bool :=
  t.entries.contains key

def run (r : Runner) : IO Unit := do
  r.section "mplex state" "packages/libp2p/mux/Libp2p/Mux/Mplex/State.lean"
  -- The identity rule over two tables. Each side opens its first
  -- stream: both take id 0.
  let (ka, a0) := (Table.empty : Table String).openLocal "a-local"
  let (kb, b0) := (Table.empty : Table String).openLocal "b-local"
  r.check "both sides number their first stream 0"
    (ka == some ⟨0, true⟩ && kb == some ⟨0, true⟩)
  -- Each side takes the peer's open of id 0 beside its own.
  let (ansA, a1) := a0.openRemote 0 "a-remote"
  let (ansB, b1) := b0.openRemote 0 "b-remote"
  r.check "each side takes the peer's id 0 beside its own id 0"
    (ansA == .accepted && ansB == .accepted && a1.size == 2 && b1.size == 2)
  r.check "each table holds (0, initiator) and (0, receiver)"
    (holds a1 ⟨0, true⟩ && holds a1 ⟨0, false⟩ && holds b1 ⟨0, true⟩ && holds b1 ⟨0, false⟩)
  -- B's data on its own stream reaches A's remote port, never A's own.
  let routed := match classify (dataFlag ⟨0, true⟩) 0 with
    | .data k => a1.dataPort? k
    | _ => none
  r.check "the initiator's data reaches the receiver's port, no cross-delivery"
    (routed == some "a-remote")
  let back := match classify (dataFlag ⟨0, false⟩) 0 with
    | .data k => a1.dataPort? k
    | _ => none
  r.check "the receiver's data reaches the initiator's port, no cross-delivery"
    (back == some "a-local")
  -- Every flag routes to the key it names.
  r.check "NewStream and the Initiator flags name a remote-opened key"
    ([Flag.newStream, .messageInitiator, .closeInitiator, .resetInitiator].all fun f =>
      match classify f 4 with
      | .open k | .data k | .close k | .reset k => k == ⟨4, false⟩)
  r.check "the Receiver flags name a locally opened key"
    ([Flag.messageReceiver, .closeReceiver, .resetReceiver].all fun f =>
      match classify f 4 with
      | .open k | .data k | .close k | .reset k => k == ⟨4, true⟩)
  r.check "every outbound flag reaches the mirror key at the peer"
    ([(⟨2, true⟩ : Key), ⟨2, false⟩].all fun k =>
      classify (dataFlag k) k.id == .data k.mirror
        && classify (closeFlag k) k.id == .close k.mirror
        && classify (resetFlag k) k.id == .reset k.mirror)
  r.check "the seven flags give seven distinct requests"
    ((allFlags.map fun f => classify f 1).eraseDups.length == 7)
  -- Half-close: the local close leaves the peer direction open.
  let key : Key := ⟨0, true⟩
  let (fin, c1) := a1.closeLocal key
  r.check "a local close is due once and keeps the stream live"
    (fin && holds c1 key && !c1.writable key && c1.dataPort? key == some "a-local")
  let (fin2, c2) := c1.closeLocal key
  r.check "a second local close sends nothing" (!fin2 && holds c2 key)
  let (port, c3) := c2.closeRemote key
  r.check "the peer's close after ours retires the stream"
    (port == some "a-local" && !holds c3 key && c3.size == 1)
  -- The other order: the peer closes first, and we can still write.
  let (p1, d1) := a1.closeRemote key
  r.check "a peer close keeps our write direction open"
    (p1 == some "a-local" && d1.writable key && d1.dataPort? key == none)
  let (p2, d2) := d1.closeRemote key
  r.check "a second peer close ends no inbox" (p2 == none && holds d2 key)
  let (fin3, d3) := d2.closeLocal key
  r.check "our close after the peer's retires the stream" (fin3 && !holds d3 key)
  -- Reset retires at once, in either direction.
  let (rp, e1) := a1.resetRemote key
  r.check "a peer reset retires the stream" (rp == some "a-local" && !holds e1 key)
  let (due, e2) := a1.resetLocal key
  r.check "a local reset is due once and retires the stream" (due && !holds e2 key)
  let (due2, _) := e2.resetLocal key
  r.check "a reset of a retired stream sends nothing" (!due2)
  -- A live key cannot open twice, and a retired one can.
  r.check "a NewStream for a live key is a duplicate"
    ((a1.openRemote 0 "again").1 == .duplicate)
  let (_, g1) := a1.resetRemote ⟨0, false⟩
  r.check "a NewStream for a retired key opens again"
    ((g1.openRemote 0 "again").1 == .accepted)
  -- The session end refuses every open.
  let (ended, f1) := a1.endAll
  r.check "endAll hands back every live stream" (ended.length == 2 && f1.size == 0)
  r.check "no stream opens after endAll"
    ((f1.openLocal "x").1 == none && (f1.openRemote 1 "x").1 == .ended)
  -- The live-stream cap.
  let full := (List.range liveStreamCap).foldl
    (fun (t : Table Nat) i => (t.openRemote i i).2) Table.empty
  r.check "the table holds liveStreamCap streams"
    (full.size == liveStreamCap)
  r.check "an inbound open over the cap is full"
    ((full.openRemote liveStreamCap 0).1 == .full)
  r.check "a local open over the cap is refused"
    ((full.openLocal 0).1 == none)

end Tests.Mplex.State

namespace Tests.Mplex.Session

open Libp2p.Core
open Libp2p.Mux
open Libp2p.Mux.Mplex.Wire
open Conc
open Streams
open Multiformats
open Streams.Sim

private structure Ends where
  dialer : Connection
  peer : Connection

/-- Two connected ends over a fresh sim network. -/
private def ends : Async Ends := do
  let net ← Net.new
  let addr ← match Multiaddr.parse? "/memory/7" with
    | .ok a => pure a
    | .error _ => throw <| IO.userError "test address does not parse"
  let l ← net.listen addr
  let some dialer ← net.dial l.addr | throw <| IO.userError "dial failed"
  let some peer ← l.accept | throw <| IO.userError "accept failed"
  l.close
  return { dialer, peer }

/-- The session `Mux.mplex.open` returns. -/
private def openSession (role : Role) (conn : Connection)
    (leftover : ByteArray := .empty) : Async MuxSession := do
  match ← (mplex.open role conn leftover).run with
  | .ok sess => return sess
  | .error e => throw <| IO.userError s!"mplex open failed: {repr e}"

private def mustOpen (sess : MuxSession) : Async Stream := do
  match ← (sess.openStream mplexId).run with
  | .ok s => return s
  | .error e => throw <| IO.userError s!"openStream failed: {repr e}"

private def mustAccept (sess : MuxSession) : Async Stream := do
  match ← sess.accept with
  | some s => return s
  | none => throw <| IO.userError "accept ended"

/-- Every byte of a stream until its end, or the error that ended it. -/
private def readAll (s : Stream) : Async (Except Streams.Error ByteArray) := do
  let mut acc := ByteArray.empty
  repeat
    match ← s.read with
    | .ok (some c) => acc := acc ++ c
    | .ok none => return .ok acc
    | .error e => return .error e
  return .ok acc

/-- Exactly `n` bytes of a stream. -/
private def readN (s : Stream) (n : Nat) : Async (Option ByteArray) := do
  let mut acc := ByteArray.empty
  while acc.size < n do
    match ← s.read with
    | .ok (some c) => acc := acc ++ c
    | _ => return none
  return some acc

private def text (s : String) : ByteArray := Bytes.ofString s

private def isOk {ε : Type} : Except ε Unit → Bool
  | .ok () => true
  | .error _ => false

private def isProtocol : Except Libp2p.Core.Error Unit → Bool
  | .error (.protocol _) => true
  | _ => false

/-- The join answer of a session, with a thrown error as `none`. -/
private def joinAnswer (sess : MuxSession) : Async (Option (Except Libp2p.Core.Error Unit)) := do
  try
    return some (← sess.join.run)
  catch _ =>
    return none

/-- One message off a raw connection. -/
private def readMessage (c : Connection) (pending : ByteArray) :
    Async (Option (Frame × ByteArray)) := do
  let mut buf := pending
  repeat
    match decodeAtB? buf 0 with
    | .ok (f, next) => return some (f, buf.extract next buf.size)
    | .error .malformed => return none
    | .error .truncated =>
      match ← c.read with
      | some chunk => buf := buf ++ chunk
      | none => return none
  return none

/-- The wire bytes of one message. -/
private def msg (flag : Flag) (id : Nat) (payload : ByteArray := .empty) : ByteArray :=
  encodeB flag id payload

/-- The identity rule between two sessions (§4.9): both open id 0, and
no byte crosses to the other stream. -/
private def runIdentity (r : Runner) : Async Unit := do
  let pair ← ends
  let a ← openSession .initiator pair.dialer
  let b ← openSession .responder pair.peer
  let sa ← mustOpen a
  let sb ← mustOpen b
  let ra ← mustAccept a
  let rb ← mustAccept b
  let w1 ← sa.write (text "from-a")
  let w2 ← sb.write (text "from-b")
  let gotB ← readN rb 6
  let gotA ← readN ra 6
  r.check "two id-0 streams carry their own bytes"
    (isOk w1 && isOk w2 && gotB == some (text "from-a") && gotA == some (text "from-b"))
  let w3 ← rb.write (text "reply-b")
  let w4 ← ra.write (text "reply-a")
  let backA ← readN sa 7
  let backB ← readN sb 7
  r.check "each receiver's reply reaches the initiator's stream"
    (isOk w3 && isOk w4 && backA == some (text "reply-b") && backB == some (text "reply-a"))
  a.close
  b.close
  let ja ← joinAnswer a
  let jb ← joinAnswer b
  r.check "both sessions join after the identity exchange"
    (ja.any isOk && jb.any isOk)

/-- The three half-close cases (§5.3; the mux PLAN, unit 2). -/
private def runHalfClose (r : Runner) : Async Unit := do
  let pair ← ends
  let a ← openSession .initiator pair.dialer
  let b ← openSession .responder pair.peer
  let sa ← mustOpen a
  let rb ← mustAccept b
  let w ← sa.write (text "request")
  sa.close
  -- Case 1: the reads drain to EOF after the peer's close.
  let drained ← readAll rb
  r.check "the reads drain to EOF after the peer close"
    (isOk w && drained == .ok (text "request"))
  -- Case 2: the write direction stays open after the peer's close.
  let late ← rb.write (text "response")
  r.check "the write direction stays open after the peer close" (isOk late)
  -- Case 3: a response sent after our FIN arrives.
  let got ← readN sa 8
  r.check "a response sent after our FIN arrives" (got == some (text "response"))
  -- Our own write after our close is refused.
  let again ← sa.write (text "x")
  r.check "a write after our own close answers closed" (again == .error .closed)
  rb.close
  let tail ← sa.read
  r.check "the peer's close then ends our reads" (tail == .ok none)
  -- A new stream opens after both halves retired the first.
  let sa2 ← mustOpen a
  let rb2 ← mustAccept b
  let w2 ← sa2.write (text "second")
  let got2 ← readN rb2 6
  r.check "a second stream works after the first retired"
    (isOk w2 && got2 == some (text "second"))
  a.close
  b.close
  let ja ← joinAnswer a
  let jb ← joinAnswer b
  r.check "both sessions join after the half-close cases" (ja.any isOk && jb.any isOk)

/-- Reset aborts both directions, from the initiator and from the
receiver: the two use different flags. -/
private def runReset (r : Runner) : Async Unit := do
  let pair ← ends
  let a ← openSession .initiator pair.dialer
  let b ← openSession .responder pair.peer
  -- The initiator resets (ResetInitiator).
  let sa ← mustOpen a
  let rb ← mustAccept b
  let w ← sa.write (text "doomed")
  let first ← readN rb 6
  sa.reset
  let peerRead ← rb.read
  r.check "an initiator reset reaches the receiver's read as reset"
    (isOk w && first == some (text "doomed") && peerRead == .error .reset)
  let peerWrite ← rb.write (text "y")
  r.check "the receiver's write after the reset answers reset" (peerWrite == .error .reset)
  let ownRead ← sa.read
  let ownRead2 ← sa.read
  r.check "our read after our reset reports reset once, then the end"
    (ownRead == .error .reset && ownRead2 == .ok none)
  let ownWrite ← sa.write (text "z")
  r.check "our write after our reset answers reset" (ownWrite == .error .reset)
  -- The receiver resets (ResetReceiver).
  let sa2 ← mustOpen a
  let rb2 ← mustAccept b
  rb2.reset
  let initRead ← sa2.read
  r.check "a receiver reset reaches the initiator's read as reset"
    (initRead == .error .reset)
  let initWrite ← sa2.write (text "w")
  r.check "the initiator's write after the reset answers reset" (initWrite == .error .reset)
  a.close
  b.close
  let ja ← joinAnswer a
  let jb ← joinAnswer b
  r.check "both sessions join after the resets" (ja.any isOk && jb.any isOk)

/-- A raw peer that sends `bytes`, and the session's join answer. -/
private def joinAfterRaw (bytes : ByteArray) : Async (Option (Except Libp2p.Core.Error Unit)) := do
  let pair ← ends
  let sess ← openSession .responder pair.dialer
  pair.peer.write bytes
  -- The session ends on its own at a protocol error. The close after it
  -- is a no-op for that case, and ends any other case.
  let answer ← joinAnswerAfter sess
  pair.peer.close
  return answer
where
  joinAnswerAfter (sess : MuxSession) : Async (Option (Except Libp2p.Core.Error Unit)) := do
    try
      return some (← sess.join.run)
    catch _ =>
      return none

/-- The hostile inputs of a raw peer (§5.1, §5.2). -/
private def runHostile (r : Runner) : Async Unit := do
  let cap := mplexMessageCap
  -- A declared length of cap + 1, and no body: the session ends at once.
  let overCap := Bytes.ofNatList
    (Varint.encodeNat (headerValue .messageInitiator 0) ++ Varint.encodeNat (cap + 1))
  let a1 ← joinAfterRaw (msg .newStream 0 ++ overCap)
  r.check "a declared length of cap + 1 ends the session before any body"
    (a1.any isProtocol)
  -- Nine continuation bytes: the session ends with no more input.
  let a2 ← joinAfterRaw ⟨Array.replicate 9 0x80⟩
  r.check "a header varint that cannot end in 9 bytes ends the session"
    (a2.any isProtocol)
  -- A live key opened twice.
  let a3 ← joinAfterRaw (msg .newStream 0 ++ msg .newStream 0)
  r.check "a NewStream for a live stream ends the session" (a3.any isProtocol)
  -- Flag code 7.
  let a4 ← joinAfterRaw ⟨#[7, 0]⟩
  r.check "flag code 7 ends the session" (a4.any isProtocol)
  -- A message of exactly cap bytes is delivered.
  do
    let pair ← ends
    let sess ← openSession .responder pair.dialer
    let body : ByteArray := ⟨Array.replicate cap 5⟩
    pair.peer.write (msg .newStream 0 ++ msg .messageInitiator 0 body)
    let st ← mustAccept sess
    let got ← readN st cap
    r.check "a message of exactly cap bytes is delivered" (got == some body)
    sess.close
    pair.peer.close
    discard <| joinAnswer sess
  -- Five continuation bytes leave the session waiting, and the rest of
  -- the header completes the message.
  do
    let pair ← ends
    let sess ← openSession .responder pair.dialer
    let bigId := 2 ^ 40
    let opening := msg .newStream bigId
    pair.peer.write (opening.extract 0 5)
    pair.peer.write (opening.extract 5 opening.size ++ msg .messageInitiator bigId (text "ok"))
    let st ← mustAccept sess
    let got ← readN st 2
    r.check "a short header prefix waits, and the completing bytes deliver"
      (got == some (text "ok"))
    sess.close
    pair.peer.close
    discard <| joinAnswer sess
  -- Data for an unknown stream is dropped, as go-mplex drops it.
  do
    let pair ← ends
    let sess ← openSession .responder pair.dialer
    pair.peer.write (msg .messageInitiator 3 (text "lost") ++ msg .newStream 0
      ++ msg .messageInitiator 0 (text "kept"))
    let st ← mustAccept sess
    let got ← readN st 4
    r.check "data for an unknown stream is dropped" (got == some (text "kept"))
    sess.close
    pair.peer.close
    discard <| joinAnswer sess

/-- The wire form of our own messages, seen by a raw peer. -/
private def runOutbound (r : Runner) : Async Unit := do
  let cap := mplexMessageCap
  let pair ← ends
  let sess ← openSession .initiator pair.dialer
  let st ← mustOpen sess
  let some (opened, rest0) ← readMessage pair.peer .empty
    | r.check "the open reaches the peer" false
  r.check "the open is NewStream id 0 labelled with the protocol id"
    (opened.flag == .newStream && opened.id == 0 && opened.payload == text mplexId.toString)
  let big : ByteArray := ⟨Array.replicate (cap + 7) 3⟩
  let w ← st.write big
  let some (m1, rest1) ← readMessage pair.peer rest0
    | r.check "a write over the cap splits in two messages" false
  let some (m2, rest2) ← readMessage pair.peer rest1
    | r.check "a write over the cap splits in two messages" false
  r.check "a write over the cap splits in two messages"
    (isOk w && m1.flag == .messageInitiator && m1.payload.size == cap
      && m2.flag == .messageInitiator && m2.payload.size == 7)
  st.close
  let some (m3, _) ← readMessage pair.peer rest2
    | r.check "our close is CloseInitiator with no data" false
  r.check "our close is CloseInitiator with no data"
    (m3.flag == .closeInitiator && m3.id == 0 && m3.payload.isEmpty)
  sess.close
  pair.peer.close
  discard <| joinAnswer sess

/-- The leftover of the negotiation is the reader's first input. -/
private def runLeftover (r : Runner) : Async Unit := do
  let pair ← ends
  let leftover := msg .newStream 0 ++ msg .messageInitiator 0 (text "hi")
  let sess ← openSession .responder pair.dialer leftover
  let st ← mustAccept sess
  let got ← readN st 2
  r.check "a nonempty leftover opens the stream and delivers its data"
    (got == some (text "hi"))
  sess.close
  pair.peer.close
  discard <| joinAnswer sess

/-- The lifecycle of the session (§3.1). -/
private def runLifecycle (r : Runner) : Async Unit := do
  -- The peer's end ends every stream, and the session joins cleanly.
  do
    let pair ← ends
    let a ← openSession .initiator pair.dialer
    let b ← openSession .responder pair.peer
    let sa ← mustOpen a
    discard <| mustAccept b
    b.close
    let read ← sa.read
    r.check "the session end reads closed on a live stream" (read == .error .closed)
    let write ← sa.write (text "late")
    r.check "the session end answers closed to a write" (write == .error .closed)
    let ja ← joinAnswer a
    let jb ← joinAnswer b
    r.check "both sides join cleanly after the peer's close"
      (ja.any isOk && jb.any isOk)
  -- After our close: no open, no accept, and a second join answers the
  -- same.
  do
    let pair ← ends
    let a ← openSession .initiator pair.dialer
    a.close
    let opened ← (a.openStream mplexId).run
    let accepted ← a.accept
    r.check "openStream after close is refused"
      (match opened with | .error (.closed _) => true | _ => false)
    r.check "accept after close answers none" accepted.isNone
    let j1 ← joinAnswer a
    let j2 ← joinAnswer a
    r.check "join after close is ok, twice" (j1.any isOk && j2.any isOk)
    pair.peer.close

/-- Two sessions under load: several streams at once, past the cap,
with a half-close before each echo. -/
private def runEcho (r : Runner) : Async Unit := do
  let pair ← ends
  let a ← openSession .initiator pair.dialer
  let b ← openSession .responder pair.peer
  let size := mplexMessageCap + 7
  let payload (i : Nat) : ByteArray :=
    ⟨(Array.range size).map fun k => UInt8.ofNat ((k * 7 + i * 13) % 251)⟩
  let server ← TaskSet.new
  server.spawn do
    for _ in [0:3] do
      let st ← mustAccept b
      server.spawn do
        match ← readAll st with
        | .ok data =>
          discard <| st.write data
          st.close
        | .error _ => st.reset
  let failures : OnceRef Nat ← OnceRef.new 0
  let clients ← TaskSet.new
  for i in [0:3] do
    clients.spawn do
      let st ← mustOpen a
      let want := payload i
      match ← st.write want with
      | .error _ => failures.update (· + 1)
      | .ok () =>
        st.close
        match ← readAll st with
        | .ok got => if got != want then failures.update (· + 1)
        | .error _ => failures.update (· + 1)
  clients.joinAll
  server.joinAll
  let n ← (failures.get : BaseIO Nat)
  r.check "three concurrent streams echo cap + 7 bytes each" (n == 0)
  a.close
  b.close
  let ja ← joinAnswer a
  let jb ← joinAnswer b
  r.check "both sessions join after the echo" (ja.any isOk && jb.any isOk)

private def checks (r : Runner) : Async Unit := do
  runIdentity r
  runHalfClose r
  runReset r
  runHostile r
  runOutbound r
  runLeftover r
  runLifecycle r
  runEcho r

def run (r : Runner) : IO Unit := do
  r.section "mplex session" "packages/libp2p/mux/Libp2p/Mux/Mplex/Session.lean"
  r.check "Mux.mplex.id is mplexId" (mplex.id == mplexId)
  Async.run (checks r)

end Tests.Mplex.Session

namespace Tests

def Mplex.run (r : Runner) : IO Unit := do
  Mplex.Wire.run r
  Mplex.State.run r
  Mplex.Session.run r

end Tests
