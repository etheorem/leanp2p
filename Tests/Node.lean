import Tests.Support
import Std.Internal.UV.TCP

/-!
# Node suite (VECTOR_TEST_PLAN.md, phase 4 steps 22 + 24)

- step 22 done-criteria: the concurrency core (blocking channels, owned
  tasks) passes a 1000-stream stress through one mux session, and the
  whole suite runs under `+RTS -N1` (`lake test -- +RTS -N1 -RTS`);
- step 24 done-criteria (in-process form): two full hosts over loopback
  TCP negotiate `/noise` and the muxer on the wire, dial by PeerId through
  the peerstore, verify the remote identity, deduplicate connections,
  report listen addrs with the `/p2p/` suffix, and run ping + identify +
  echo end to end — the same flow the go-libp2p interop of phase 5 uses.
-/

open LeanP2P Tests
open Std.Net Std.Internal.UV

namespace Tests

private def bytesOf (hex : String) : ByteArray :=
  match Bytes.ofHex? hex with
  | some b => b
  | none => ByteArray.empty

private def idI : Keys.PrivKey :=
  { keyType := .ed25519, raw := bytesOf "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60" }
private def idR : Keys.PrivKey :=
  { keyType := .ed25519, raw := bytesOf "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb" }

/-- Build a host with a real Noise security and the given muxer choices;
Noise advertises exactly these muxers in its handshake extension. -/
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

def NodeSuite.run (r : Runner) : IO Unit := do
  r.section "node (host + concurrency core)"
    "(phase 4 steps 22+24; internal e2e + stress - no upstream vectors)"

  /- ## step 22: 1000-stream stress through one mux session (sim) -/

  let net ← SimNet.new
  let some pubR ← idR.publicKey | r.check "stress host A key" false; return ()
  let some pubI ← idI.publicKey | r.check "stress host B key" false; return ()
  -- the toy security speaks the spike's raw key bytes; the marshaled
  -- protobuf form keeps both ends consistent
  let some hA ← Host.new
    { key := idR, listenAddr := emptyAddr } net.transport
    [NoiseSim.security { bytes := Keys.marshalPubKey pubR }] [FramedChoice]
    | r.check "stress host A" false; return ()
  let some hB ← Host.new
    { key := idI, listenAddr := emptyAddr } net.transport
    [NoiseSim.security { bytes := Keys.marshalPubKey pubI }] [FramedChoice]
    | r.check "stress host B" false; return ()
  hA.setStreamHandler Ping.protocol Ping.handle
  let _ ← hA.listen

  /- 950 sequential echo streams + 50 concurrent pings -/
  let mut seqOk := 0
  for i in [0:950] do
    match ← hB.newStream hA.cfg.listenAddr Ping.protocol with
    | none => pure ()
    | some s => do
      let payload := Bytes.ofNatList (List.replicate 32 (i % 256))
      match ← Ping.ping s payload with
      | some _ => seqOk := seqOk + 1
      | none => pure ()
      s.close
  r.check "stress 950 sequential streams" (seqOk == 950)

  let burst ← (List.range 50).mapM fun _ => IO.asTask do
    match ← hB.newStream hA.cfg.listenAddr Ping.protocol with
    | none => return false
    | some s => do
      let payload := Bytes.ofNatList (List.range 32)
      let res ← Ping.ping s payload
      s.close
      return res.isSome
  let burstOk ← burst.filterM fun t => do pure (match ← IO.wait t with | .ok v => v | _ => false)
  r.check "stress 50 concurrent streams" (burstOk.length == 50)

  hB.close
  hA.close

  /- ## step 24: two hosts over loopback TCP, full upgrade path -/

  let some hA ← mkHost idR loopback [YamuxChoice, MplexChoice]
    | r.check "tcp host A" false; return ()
  let some hB ← mkHost idI loopback [YamuxChoice]
    | r.check "tcp host B" false; return ()
  let aid := hA.id

  let pubA ← idR.publicKey
  hA.setStreamHandler Ping.protocol Ping.handle
  hA.setStreamHandler Identify.protocol fun s => do
    let some pub := pubA | s.close
    let addrs ← hA.addrs
    Identify.respondAndSend pub addrs [Ping.protocol, Identify.protocol] none "leanp2p" s
  hA.setStreamHandler "/demo/echo/1.0.0" fun s => do
    match ← s.read with
    | none => s.close
    | some b => do s.write b; s.close

  /- A listens; B learns A's address out of band (the peerstore). -/
  let some _ ← hA.listen | r.check "tcp host A listen" false
  let some lA ← hA.listeners.get |>.map (·.head?) | r.check "tcp host A listener" false
  hB.peerstore.addAddrs aid [lA.addr]

  /- addrs: one per listener, p2p suffix encapsulated (dialable form) -/
  let addrs ← hA.addrs
  let p2pOk ← match addrs with
    | [full] =>
      match full.components.getLast? with
      | some (.p2p mh _) =>
        pure (full.components.dropLast == lA.addr.components
          && mh == aid.digestBytes
          && (Host.addrPeer? full).getD aid == aid)
      | _ => pure false
    | _ => pure false
  r.check "host addrs /p2p/ suffix" ((addrs.length == 1) && p2pOk)

  /- dial by PeerId: security + muxer negotiated, identity verified -/
  let some sess ← hB.dialPeer aid | r.check "dialPeer" false
  r.check "dialPeer identity" (sess.remotePeer == aid)
  -- the Noise extension selected the muxer (go upgrader semantics), in
  -- the dialer's preference order
  r.check "muxer from noise extension" (sess.mux.name == "/yamux/1.0.0")
  r.check "session dedup: one conn" ((← hB.conns.get).length == 1)

  /- dialing a p2p-suffixed address pins the identity directly -/
  let some fullAddr := addrs.head? | r.check "suffixed addr" false
  match ← hB.dial fullAddr none with
  | none => r.check "dial suffixed addr" false
  | some s2x => do
    r.check "dial suffixed addr" (s2x.remotePeer == aid)
    r.check "suffixed addr dedup" ((← hB.conns.get).length == 1)

  /- ping over the negotiated session -/
  match ← hB.newStreamTo aid Ping.protocol with
  | none => r.check "host ping stream" false
  | some s => do
    let payload ← match ← OpenSsl.randomBytes 32 with
      | some b => pure b
      | none => pure (Bytes.ofNatList (List.replicate 32 0x42))
    match ← Ping.ping s payload with
    | none => r.check "host ping" false
    | some _ms => r.check "host ping" true
    s.close

  /- a second stream reuses the same connection -/
  let connsBefore ← hB.conns.get
  let some s2 ← hB.newStreamTo aid "/demo/echo/1.0.0" | r.check "host echo stream" false
  s2.write (Bytes.ofString "echo-me")
  let got ← s2.read
  r.check "host echo" (got == some (Bytes.ofString "echo-me"))
  s2.close
  let connsAfter ← hB.conns.get
  r.check "host echo dedup" (connsAfter.length == connsBefore.length)

  /- identify: the responder's key derives the peer id we dialed -/
  match ← hB.newStreamTo aid Identify.protocol with
  | none => r.check "host identify stream" false
  | some s => do
    match ← Identify.request s with
    | none => r.check "host identify" false
    | some (msg, pid) => do
      r.check "host identify id" (pid == aid)
      -- one encapsulated /p2p/-suffixed listen addr
      r.check "host identify addrs" (msg.listenAddrs.length == 1)
      r.check "host identify agent" (msg.agentVersion == some "leanp2p")

  /- an unknown peer cannot be dialed -/
  let some bogusPub ← idI.publicKey | r.check "bogus peer" false
  let bogus := PeerId.ofPublicKey bogusPub  -- hB's own id, never registered
  let nope ← hB.dialPeer bogus
  r.check "dialPeer unknown peer fails" nope.isNone

  /- shutdown: everything joins -/
  hB.close
  hA.close
  r.check "clean shutdown" true

  /- ## initiator's preference wins the extension selection (mplex) -/

  let some hE ← mkHost idR loopback [YamuxChoice, MplexChoice]
    | r.check "pref host E" false; return ()
  let some hF ← mkHost idI loopback [MplexChoice, YamuxChoice]
    | r.check "pref host F" false; return ()
  hE.setStreamHandler Ping.protocol Ping.handle
  let _ ← hE.listen
  let some lE ← hE.listeners.get |>.map (·.head?) | r.check "pref host E listener" false
  hF.peerstore.addAddrs hE.id [lE.addr]
  match ← hF.dialPeer hE.id with
  | none => r.check "pref extension dial" false
  | some sessF => do
    -- the dialer advertised [mplex, yamux]; the listener follows that order
    r.check "pref extension dial" (sessF.mux.name == "/mplex/6.7.0")
    match ← hF.newStreamTo hE.id Ping.protocol with
    | none => r.check "pref extension ping stream" false
    | some s => do
      let payload := Bytes.ofNatList (List.replicate 32 3)
      r.check "pref extension ping" (← Ping.ping s payload).isSome
      s.close
  hF.close
  hE.close

  /- ## security without a muxer extension falls back to multistream -/

  let some pubR2 ← idR.publicKey | r.check "mss fallback key" false; return ()
  let some pubI2 ← idI.publicKey | r.check "mss fallback key" false; return ()
  let some hG ← Host.new { key := idR, listenAddr := loopback } Tcp.transport
    [NoiseSim.security { bytes := Keys.marshalPubKey pubR2 }] [FramedChoice, YamuxChoice]
    | r.check "mss fallback host G" false; return ()
  let some hH ← Host.new { key := idI, listenAddr := loopback } Tcp.transport
    [NoiseSim.security { bytes := Keys.marshalPubKey pubI2 }] [YamuxChoice, FramedChoice]
    | r.check "mss fallback host H" false; return ()
  hG.setStreamHandler Ping.protocol Ping.handle
  let _ ← hG.listen
  let some lG ← hG.listeners.get |>.map (·.head?) | r.check "mss fallback listener" false
  hH.peerstore.addAddrs hG.id [lG.addr]
  match ← hH.dialPeer hG.id with
  | none => r.check "mss fallback dial" false
  | some sessH => do
    -- noise-sim advertises no muxers: negotiated on the wire, dialer first
    r.check "mss fallback dial" (sessH.mux.name == "/yamux/1.0.0")
    match ← hH.newStreamTo hG.id Ping.protocol with
    | none => r.check "mss fallback ping stream" false
    | some s => do
      let payload := Bytes.ofNatList (List.replicate 32 5)
      r.check "mss fallback ping" (← Ping.ping s payload).isSome
      s.close
  hH.close
  hG.close

  /- ## mplex as the negotiated muxer over TCP (dialer picks) -/

  let some hC ← mkHost idR loopback [YamuxChoice, MplexChoice]
    | r.check "mplex host C" false; return ()
  let some hD ← mkHost idI loopback [MplexChoice]
    | r.check "mplex host D" false; return ()
  hC.setStreamHandler Ping.protocol Ping.handle
  let _ ← hC.listen
  let some lC ← hC.listeners.get |>.map (·.head?) | r.check "mplex host C listener" false
  hD.peerstore.addAddrs hC.id [lC.addr]
  let some sessD ← hD.dialPeer hC.id | r.check "mplex dial" false
  r.check "mplex dial identity" (sessD.remotePeer == hC.id)
  let some ps ← sessD.mux.openStream Ping.protocol | r.check "mplex open" false
  let rdrD ← BufReader.ofConn ps.conn
  let sel ← Multiselect.selectInitiatorLazy rdrD ps.conn Ping.protocol
  r.check "mplex stream negotiate" (sel == some Ping.protocol)
  match sel with
  | none => r.check "mplex host ping stream" false
  | some _ => do
    let payload := Bytes.ofNatList (List.replicate 32 7)
    match ← Ping.ping ps payload with
    | none => r.check "mplex host ping" false
    | some _ => r.check "mplex host ping" true
    ps.close
  hD.close
  hC.close

  /- ## negotiation leftovers reach the handler (no dropped bytes)

  `Host.handleStream` and `Host.openProto` prepend their negotiation
  reader's leftover bytes to the stream they hand on: a coalesced first
  data frame must not vanish between the stages. -/
  let base : Stream :=
    { read := pure (some (Bytes.ofString "TAIL"))
      write := fun _ => pure ()
      close := pure ()
      reset := pure () }
  let s' ← Stream.prependBytes base (Bytes.ofString "AB")
  let first ← s'.read
  let second ← s'.read
  r.check "negotiation leftovers handed on"
    (first == some (Bytes.ofString "AB") ∧ second == some (Bytes.ofString "TAIL"))

  /- ## a silent peer cannot hang the shutdown

  A raw TCP client that connects and sends nothing parks the upgrade
  responder inside the security handshake. `close` must close the pending
  connection (waking the parked read with EOF) and join the task; before
  the fix the join waited forever. -/
  let some hS ← mkHost idR loopback [YamuxChoice, MplexChoice]
    | r.check "silent peer host" false; return ()
  let some _ ← hS.listen | r.check "silent peer listen" false
  let some lS ← hS.listeners.get |>.map (·.head?) | r.check "silent peer listener" false
  let port := match lS.addr.components.getLast? with
    | some (.tcp p) => p
    | _ => 0
  let sock ← TCP.Socket.new
  let sa : SocketAddress :=
    .v4 { addr := { octets := #v[127, 0, 0, 1] }, port := port.toUInt16 }
  let connected ← match ← LeanP2P.Tcp.await (← sock.connect sa) with
    | .ok _ => pure true
    | .error _ => pure false
  r.check "silent peer connected" connected
  IO.sleep 100   -- the responder parks in the handshake read
  hS.close
  r.check "close with silent peer joins" true

end Tests
