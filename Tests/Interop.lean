import Tests.Support

/-!
# Interop suite (VECTOR_TEST_PLAN.md, phase 5)

The go-compatibility fixes the wider interop matrix needs, exercised in
process (the live go-libp2p runs are `scripts/interop-matrix.sh`):

- mplex stream identity per go-mplex: both sides number streams from
  zero and the Receiver/Initiator flag bit - not an odd/even id split -
  separates the two namespaces, so simultaneous same-id streams coexist;
- yamux flow control per the hashicorp spec: writes split by the
  peer-granted window and resume on WindowUpdate credit, and a transfer
  larger than the 256 KiB initial window completes in both directions
  over TCP (noise-encrypted, like the interop matrix);
- simultaneous dials resolve to one connection per side, keep the
  connection dialed by the smaller peer id (go's rule), and stay usable.
-/

open LeanP2P Tests

namespace Tests

private def bytesOf (hex : String) : ByteArray :=
  match Bytes.ofHex? hex with
  | some b => b
  | none => ByteArray.empty

private def idI : Keys.PrivKey :=
  { keyType := .ed25519, raw := bytesOf "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60" }
private def idR : Keys.PrivKey :=
  { keyType := .ed25519, raw := bytesOf "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb" }

private def mkHost (key : Keys.PrivKey) (addr : Multiaddr) (muxers : List MuxChoice) :
    IO (Option Host) := do
  let some static ← OpenSsl.randomBytes 32 | return none
  Host.new { key := key, listenAddr := addr } Tcp.transport
    [Noise.security key static (muxers.map (·.name))] muxers

private def loopback : Multiaddr :=
  match Multiaddr.parse? "/ip4/127.0.0.1/tcp/0" with
  | some a => a
  | none => { components := [] }

private def emptyAddr : Multiaddr :=
  { components := [] }

private def mkSplit : IO (Connection × Connection) := do
  let p1 ← BytePipe.new
  let p2 ← BytePipe.new
  let (a, b) := SimNet.splice p1 p2 { components := [] }
  pure (a.byteSplitting, b)

/-- Echo every chunk back until EOF (the phase 5 transfer pattern); EOF
is propagated (stream closed) so the initiator's read sees the end. -/
private partial def echoHandler (s : Stream) : IO Unit := do
  match ← s.read with
  | none => s.close
  | some b => do s.write b; echoHandler s

/-- Read to EOF. -/
private partial def readAll (s : Stream) (acc : ByteArray) : IO ByteArray := do
  match ← s.read with
  | none => pure acc
  | some b => readAll s (acc ++ b)

def InteropSuite.run (r : Runner) : IO Unit := do
  r.section "interop (phase 5)"
    "libp2p/test-plans transport-interop prereqs: go-mplex identity, \
     yamux flow control + ACK, simultaneous dials (in-process; the live \
     go-libp2p matrix is scripts/interop-matrix.sh)"

  /- ## mplex: same-id streams from both sides coexist (go-mplex) -/

  let (cI, cR) ← mkSplit
  let client ← Mplex.MplexSession.make cI true
  let server ← Mplex.MplexSession.make cR false
  -- both sides open their first stream; with ids from zero that is id 0
  -- on both (the old odd/even split would have kept them apart)
  let some stC ← client.openStream "/p/c" | r.check "mplex id collision open C" false
  stC.write (Bytes.ofString "c-hello")
  let _ ← server.pumpOne          -- client's NewStream -> (0, false) at server
  let some stS ← server.openStream "/p/s" | r.check "mplex id collision open S" false
  stS.write (Bytes.ofString "s-hello")
  let r1 ← server.pumpOne         -- client's MessageInitiator -> (0, false)
  let r2 ← client.pumpOne         -- server's NewStream -> (0, false) at client
  let r3 ← client.pumpOne         -- server's MessageInitiator -> (0, false)
  r.check "mplex id collision pumps" (r1 ∧ r2 ∧ r3)
  let serverStreams ← server.streams.get
  let clientStreams ← client.streams.get
  -- each side has exactly two streams: its own (0, true) and the peer's (0, false)
  r.check "mplex id collision namespaces"
    (serverStreams.length == 2 ∧ clientStreams.length == 2 ∧
      serverStreams.any (·.1 == (0, true)) ∧ clientStreams.any (·.1 == (0, true)))
  let gotAtServer ← match serverStreams.lookup (0, false) with
    | some st => st.pipe.read
    | none => pure none
  r.check "mplex id collision routed at server"
    (gotAtServer == some (Bytes.ofString "c-hello"))
  let gotAtClient ← match clientStreams.lookup (0, false) with
    | some st => st.pipe.read
    | none => pure none
  r.check "mplex id collision routed at client"
    (gotAtClient == some (Bytes.ofString "s-hello"))
  -- the locally-initiated streams received nothing (no cross-delivery)
  let ownC ← match clientStreams.lookup (0, true) with
    | some st => do
      let xs ← st.pipe.ch.drain
      pure xs.isEmpty
    | none => pure false
  let ownS ← match serverStreams.lookup (0, true) with
    | some st => do
      let xs ← st.pipe.ch.drain
      pure xs.isEmpty
    | none => pure false
  r.check "mplex id collision no cross-delivery" (ownC ∧ ownS)

  /- ## yamux: transfer larger than the initial window, both directions -/

  let chunkOf (i : Nat) : ByteArray :=
    ByteArray.mk (Array.replicate 65536 (UInt8.ofNat (i % 251 + 1)))
  let total := 16 * 65536   -- 1 MiB, 4x the initial 256 KiB window

  let some hA ← mkHost idR loopback [YamuxChoice]
    | r.check "fc host A" false; return ()
  let some hB ← mkHost idI loopback [YamuxChoice]
    | r.check "fc host B" false; return ()
  hA.setStreamHandler "/echo/1.0.0" echoHandler
  hB.setStreamHandler "/echo/1.0.0" echoHandler
  hA.setStreamHandler Ping.protocol Ping.handle
  let _ ← hA.listen
  let _ ← hB.listen
  let some lA ← hA.listeners.get |>.map (·.head?) | r.check "fc listener A" false
  hB.peerstore.addAddrs hA.id [lA.addr]

  -- B pushes 1 MiB through one stream; the writer runs concurrently with
  -- the reads (like io.Copy), so window credit keeps flowing
  let some sessB ← hB.dialPeer hA.id | r.check "fc dial" false
  let some s ← Host.openProto sessB "/echo/1.0.0" | r.check "fc stream" false
  let writer ← IO.asTask do
    for i in [0:16] do
      s.write (chunkOf i)
    s.close
  let got ← readAll s ByteArray.empty
  let _ ← IO.wait writer
  r.check "fc 1MiB round trip size" (got.size == total)
  let mut chunksOk := got.size == total
  for i in [0:16] do
    if got.extract (i * 65536) ((i + 1) * 65536) != chunkOf i then
      chunksOk := false
  r.check "fc 1MiB round trip bytes" chunksOk
  s.close

  -- the reverse direction: A opens a stream back over a fresh session
  let some lB ← hB.listeners.get |>.map (·.head?) | r.check "fc listener B" false
  hA.peerstore.addAddrs hB.id [lB.addr]
  let some sessA ← hA.dialPeer hB.id | r.check "fc dial reverse" false
  let some s2 ← Host.openProto sessA "/echo/1.0.0" | r.check "fc stream reverse" false
  let writer2 ← IO.asTask do
    for i in [0:16] do
      s2.write (chunkOf (i + 3))
    s2.close
  let got2 ← readAll s2 ByteArray.empty
  let _ ← IO.wait writer2
  r.check "fc 1MiB reverse size" (got2.size == total)
  let mut chunksOk2 := got2.size == total
  for i in [0:16] do
    if got2.extract (i * 65536) ((i + 1) * 65536) != chunkOf (i + 3) then
      chunksOk2 := false
  r.check "fc 1MiB reverse bytes" chunksOk2
  s2.close

  hB.close
  hA.close

  /- ## simultaneous dials: one connection survives, still usable -/

  -- a few rounds: the race must converge whatever the interleaving
  for round in [0:3] do
    let some hA ← mkHost idR loopback [YamuxChoice]
      | r.check "simul host A" false; return ()
    let some hB ← mkHost idI loopback [YamuxChoice]
      | r.check "simul host B" false; return ()
    hA.setStreamHandler Ping.protocol Ping.handle
    hB.setStreamHandler Ping.protocol Ping.handle
    let _ ← hA.listen
    let _ ← hB.listen
    let some lA ← hA.listeners.get |>.map (·.head?) | r.check "simul listener A" false
    let some lB ← hB.listeners.get |>.map (·.head?) | r.check "simul listener B" false
    hA.peerstore.addAddrs hB.id [lB.addr]
    hB.peerstore.addAddrs hA.id [lA.addr]
    let tA ← IO.asTask (hA.dialPeer hB.id)
    let tB ← IO.asTask (hB.dialPeer hA.id)
    let rA ← IO.wait tA
    let rB ← IO.wait tB
    r.check s!"simul round {round} both dials succeed"
      (match rA, rB with | .ok (some _), .ok (some _) => true | _, _ => false)
    r.check s!"simul round {round} one connection at A" ((← hA.conns.get).length == 1)
    r.check s!"simul round {round} one connection at B" ((← hB.conns.get).length == 1)
    -- the surviving sessions are connected to each other: ping both ways
    let pingOk ← match ← hA.newStreamTo hB.id Ping.protocol with
      | none => pure false
      | some s => do
        let res ← Ping.ping s (Bytes.ofNatList (List.replicate 32 round))
        s.close
        pure res.isSome
    r.check s!"simul round {round} ping A->B" pingOk
    let pingOk2 ← match ← hB.newStreamTo hA.id Ping.protocol with
      | none => pure false
      | some s => do
        let res ← Ping.ping s (Bytes.ofNatList (List.replicate 32 (round + 1)))
        s.close
        pure res.isSome
    r.check s!"simul round {round} ping B->A" pingOk2
    hA.close
    hB.close

end Tests
