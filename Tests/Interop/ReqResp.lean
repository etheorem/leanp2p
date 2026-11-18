import Conc
import Streams
import Libp2p.Identity
import Libp2p.Core
import Libp2p.Host
import Libp2p.Mux
import Libp2p.Security.Noise
import Libp2p.Protocols.ReqResp.Exchange

/-!
# The req/resp interop driver

The Lean side of `scripts/reqresp-interop.sh`. The go side
(`scripts/reqresp-interop/`) runs a go-libp2p host and frames every
payload with prysm's own ssz_snappy encoder (`SszNetworkEncoder`, at the
commit `VECTORS.lock` pins). The script runs both directions over
loopback TCP, with Noise and yamux.

Two methods of the consensus networking specs:

* Status v1 (phase0): an 84-byte request, one 84-byte success chunk, no
  context bytes.
* BeaconBlocksByRange v2 (altair): a 24-byte request (`start_slot`,
  `count`, `step`), then `count` success chunks with a 4-byte
  `ForkDigest` context each. One block chunk is 70000 bytes, past one
  snappy frame. A request with a count of 0 draws one `InvalidRequest`
  chunk.

The payloads are opaque test bytes. The framing is the subject. Both
sides build the same patterns.

* `reqresp-interop listen`: serve both methods and `/test/done`, print
  the port, and close after `/test/done` has ended.
* `reqresp-interop dial PORT`: request Status, BlocksByRange with three
  blocks, and BlocksByRange with a count of 0, check every chunk, then
  open `/test/done`, read `bye`, and close.

The go responder waits a moment after its last chunk, then closes its
write side and fails the run when that close fails. Status has one
chunk, so our requester knows the end of the response before the
responder closes. A requester that resets the stream at its last chunk
fails that close, as Lighthouse sees it (`ReqResp.request`, "The end of
a response").

The driver lives outside `lake test`, which stays hermetic: Go tooling
is test-only and confined to the harness (CLAUDE.md, "Dependencies").
-/

set_option autoImplicit false

namespace Tests.Interop.ReqResp

open Conc (Async Chan OnceRef Clock)
open Libp2p.Identity Libp2p.Core
open Libp2p.Host (Host)
open Libp2p.Protocols Libp2p.Protocols.ReqResp

/-- 32 bytes of one value, the form of both identity seeds. -/
def seed (v : UInt8) : ByteArray := ⟨Array.replicate 32 v⟩

/-- Our identity seed: 32 bytes of `R`. The go side holds the same. -/
def leanSeed : ByteArray := seed 'R'.toNat.toUInt8

/-- The go side's identity seed: 32 bytes of `P`. -/
def goSeed : ByteArray := seed 'P'.toNat.toUInt8

/-- The pattern both sides build. -/
def payload (n salt : Nat) : ByteArray :=
  ⟨(Array.range n).map fun k => UInt8.ofNat ((k * 7 + 3 + salt) % 251)⟩

/-- The Status size: `fork_digest`, `finalized_root`, `finalized_epoch`,
`head_root`, `head_slot` (phase0 "Status"). -/
def statusSize : Nat := 4 + 32 + 8 + 32 + 8

/-- The request of Status. -/
def statusRequest : ByteArray := payload statusSize 9

/-- The answer of Status. -/
def statusAnswer : ByteArray := payload statusSize 1

/-- The sizes of the three block chunks. -/
def blockSizes : List Nat := [100, 70000, 5]

/-- The block chunk `i`. -/
def block (i : Nat) : ByteArray := payload (blockSizes.getD i 0) (20 + i)

/-- The `ForkDigest` context of every block chunk. -/
def digest : ByteArray := ⟨#[1, 2, 3, 4]⟩

/-- `n` as 8 little-endian bytes, an SSZ `uint64`. -/
def u64 (n : Nat) : ByteArray := ⟨(Array.range 8).map fun i => UInt8.ofNat (n / 256 ^ i)⟩

/-- `BeaconBlocksByRangeRequest`: `start_slot` 100, `count`, `step` 1. -/
def rangeRequest (count : Nat) : ByteArray := u64 100 ++ u64 count ++ u64 1

/-- The `count` field of a range request: bytes 8 to 15, little-endian. -/
def countOf (req : ByteArray) : Nat :=
  (List.range 8).foldl (fun acc i => acc + (req.get! (8 + i)).toNat * 256 ^ i) 0

/-- Status v1. One chunk at most, so the requester knows the end of the
response at that chunk. -/
def statusMethod : Method where
  id := Constants.reqRespId "status" 1
  request := some ⟨statusSize, statusSize⟩
  response := ⟨statusSize, statusSize⟩
  contextLen := 0
  maxChunks := 1

/-- BeaconBlocksByRange v2. The block bounds cover the test sizes. -/
def rangeMethod : Method where
  id := Constants.reqRespId "beacon_blocks_by_range" 2
  request := some ⟨24, 24⟩
  response := ⟨1, 2 ^ 20⟩
  contextLen := Constants.forkDigestLen
  maxChunks := 1024

/-- The deadline of each exchange, in milliseconds. -/
def timeoutMs : Nat := 10000

/-- The stream that ends the run. -/
def doneId : ProtocolId := ⟨"/test/done"⟩

/-- Fail with a message. -/
def fail {α : Type} (msg : String) : Async α :=
  throw <| IO.userError s!"lean: {msg}"

/-- The value of an `Except`, or a failure that names the error. -/
def orFail {ε α : Type} [Repr ε] (what : String) : Except ε α → Async α
  | .ok a => return a
  | .error e => fail s!"{what}: {(repr e).pretty}"

/-- A multiaddr from its text form. -/
def addr (s : String) : Async Multiformats.Multiaddr :=
  orFail s!"address {s}" (Multiformats.Multiaddr.parse? s)

/-- The Ed25519 key of a seed. -/
def keyOf (s : ByteArray) : Async PrivKey :=
  orFail "identity" (PrivKey.ofData? .ed25519 s)

/-- The peer id of a seed. -/
def peerOfSeed (s : ByteArray) : Async PeerId := do
  orFail "peer id" ((← keyOf s).toPublic.bind PeerId.ofPubKey)

/-- The Status answer: the answer chunk for the expected request, and a
`ServerError` chunk for any other. -/
def statusRespond (req : Option ByteArray) : Async (List Chunk) :=
  if req == some statusRequest then return [⟨.success, .empty, statusAnswer⟩]
  else return [⟨.serverError, .empty, "unexpected status request".toUTF8⟩]

/-- The BlocksByRange answer: one block chunk per block for a count of
three, and one `InvalidRequest` chunk for a count of 0. -/
def rangeRespond (req : Option ByteArray) : Async (List Chunk) := do
  let some r := req | return [⟨.invalidRequest, .empty, "no request".toUTF8⟩]
  if countOf r == 0 then return [⟨.invalidRequest, .empty, "count is zero".toUTF8⟩]
  if r != rangeRequest blockSizes.length then
    return [⟨.serverError, .empty, "unexpected range request".toUTF8⟩]
  return (List.range blockSizes.length).map fun i => ⟨.success, digest, block i⟩

/-- Our host over TCP, and the cell its failures land in. -/
def mkHost (handlers : List StreamHandler) : Async (Host × OnceRef (List String)) := do
  let key ← keyOf leanSeed
  let noise ← orFail "noise" (← (Libp2p.Security.Noise.Config.generate key).run)
  let failures : OnceRef (List String) ← OnceRef.new []
  let h ← orFail "host" (← (Host.new {
    identity := key
    transports := [Streams.Tcp.transport]
    security := [Libp2p.Security.Noise.securityProtocol noise]
    muxers := [Libp2p.Mux.yamux]
    handlers
    onFailure := fun f => failures.update (· ++ [toString f.error]) } : BaseIO _))
  return (h, failures)

/-- Fail when the host reported a failure. -/
def noFailures (failures : OnceRef (List String)) : Async Unit := do
  let fs ← (failures.get : BaseIO (List String))
  unless fs.isEmpty do fail s!"the host reported failures: {fs}"

/-- The listener side: serve both methods, and close at `/test/done`. -/
def listenMode : Async Unit := do
  let done : Chan Unit ← Chan.new 1
  let doneHandler : StreamHandler := {
    id := doneId
    handle := fun _ s => do
      discard <| s.write "bye".toUTF8
      -- The dialer closes its host after `bye`, which ends this read,
      -- with EOF or a reset. Either is the end.
      repeat
        match ← s.read with
        | .ok (some _) => pure ()
        | _ => break
      s.close
      discard (done.trySend () : BaseIO Bool) }
  let (h, failures) ← mkHost [
    handler statusMethod Clock.system timeoutMs statusRespond,
    handler rangeMethod Clock.system timeoutMs rangeRespond,
    doneHandler]
  let a ← orFail "listen" (← h.startListening (← addr "/ip4/127.0.0.1/tcp/0"))
  let some port := Streams.Tcp.socketAddress? a |>.map (·.port) | fail "no port"
  IO.println port
  (← IO.getStdout).flush
  -- Park: the `/test/done` handler wakes it.
  discard done.recv
  try h.close catch e => fail s!"close: {e}"
  noFailures failures

/-- One request through the host: open the stream for the method, then
collect the chunks. -/
def ask (h : Host) (peer : PeerId) (m : Method) (req : ByteArray) : Async (List Chunk) := do
  let (_, s) ← orFail s!"new stream {m.id}" (← h.newStream peer [m.id])
  orFail s!"request {m.id}" (← requestAll s m Clock.system timeoutMs (some req))

/-- The dialer side: the three requests, then `/test/done`. -/
def dialMode (port : String) : Async Unit := do
  let goPeer ← peerOfSeed goSeed
  let (h, failures) ← mkHost []
  let p ← orFail "dial" (← h.dial (← addr s!"/ip4/127.0.0.1/tcp/{port}/p2p/{goPeer}"))
  unless p == goPeer do fail s!"the dial proved {p}, want {goPeer}"
  let cs ← ask h goPeer statusMethod statusRequest
  unless cs == [⟨.success, .empty, statusAnswer⟩] do
    fail s!"status: got {cs.length} chunks, want one success with the answer"
  let cs ← ask h goPeer rangeMethod (rangeRequest blockSizes.length)
  let want := (List.range blockSizes.length).map fun i => (⟨.success, digest, block i⟩ : Chunk)
  unless cs == want do
    fail s!"range: got {cs.length} chunks of sizes {cs.map (·.payload.size)}, want {blockSizes}"
  let cs ← ask h goPeer rangeMethod (rangeRequest 0)
  match cs with
  | [c] => unless c.result == .invalidRequest do fail "range count 0: the chunk is not InvalidRequest"
  | _ => fail s!"range count 0: want one InvalidRequest chunk, got {cs.length}"
  let (_, d) ← orFail "done stream" (← h.newStream goPeer [doneId])
  let mut bye := ByteArray.empty
  while bye.size < 3 do
    match ← d.read with
    | .ok (some b) => bye := bye ++ b
    | _ => break
  unless bye == "bye".toUTF8 do fail s!"done answered {bye.size} bytes, want bye"
  try h.close catch e => fail s!"close: {e}"
  noFailures failures

end Tests.Interop.ReqResp

def main (args : List String) : IO UInt32 := do
  let run : Conc.Async Unit := match args with
    | ["listen"] => Tests.Interop.ReqResp.listenMode
    | ["dial", port] => Tests.Interop.ReqResp.dialMode port
    | _ => Tests.Interop.ReqResp.fail "usage: reqresp-interop listen | dial PORT"
  try
    run.run
    IO.eprintln "lean: ok"
    return 0
  catch e =>
    IO.eprintln s!"{e}"
    return 1
