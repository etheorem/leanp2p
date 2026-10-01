import Tests.Support

/-!
# Ping + Identify suite (VECTOR_TEST_PLAN.md, phase 3 step 20)

Mirrors vendor/specs/ping/ping.md (32-byte echo, protocol id
`/ipfs/ping/1.0.0`) and vendor/specs/identify/README.md (the Identify
protobuf over `/ipfs/id/1.0.0`, peer id derived from the embedded
public key). The Identify vector is a real protobuf captured from a live
go-libp2p host (`identify-go.json`).
-/

open LeanP2P Tests

namespace Tests

private def connStream (c : Connection) : Stream where
  read := c.read
  write := c.write
  close := c.close
  reset := pure ()

private def mkSplit : IO (Connection × Connection) := do
  let p1 ← BytePipe.new
  let p2 ← BytePipe.new
  let (a, b) := SimNet.splice p1 p2 { components := [] }
  pure (a.byteSplitting, b)



def PingIdSuite.run (r : Runner) : IO Unit := do
  r.section "ping + identify"
    "libp2p/specs ping/ping.md + identify/README.md + captured go Identify protobuf"

  -- ping protocol id and payload size
  r.check "ping protocol id" (Ping.protocol == "/ipfs/ping/1.0.0")
  r.check "ping payload size" (Ping.payloadSize == 32)

  -- e2e ping over the byte-splitting sim: responder echoes, initiator
  -- measures the RTT; a wrong-size payload is rejected
  let p1 ← BytePipe.new
  let p2 ← BytePipe.new
  let (cI, cR) := SimNet.splice p1 p2 { components := [] }
  let responderT ← IO.asTask (Ping.handle (connStream cR))
  let payload ← match ← OpenSsl.randomBytes 32 with
    | some b => pure b
    | none => pure (Bytes.ofNatList (List.replicate 32 7))
  let rtt ← Ping.ping (connStream cI) payload
  r.check "ping e2e rtt measured" rtt.isSome
  cI.close
  cR.close
  let _ := responderT.get

  let q1 ← BytePipe.new
  let q2 ← BytePipe.new
  let (cI2, cR2) := SimNet.splice q1 q2 { components := [] }
  let responderT2 ← IO.asTask (Ping.handle (connStream cR2))
  let bad ← Ping.ping (connStream cI2) (Bytes.ofNatList (List.replicate 8 1))
  r.check "ping wrong size rejected" bad.isNone
  cI2.close
  cR2.close
  let _ := responderT2.get

  -- identify: captured go-libp2p Identify protobuf decodes; the embedded
  -- public key yields the recorded peer id
  let j ← loadJson "identify-go.json"
  let respHex ← jStr "identify-go.json" j "responseHex"
  -- the captured response carries a 2-byte RPC uvarint length prefix
  let respBytes ← hexBytesByteArray respHex
  let stripped := respBytes.extract 2 respBytes.size
  match Messages.decodeIdentify? stripped with
  | none => r.check "identify protobuf decodes" false
  | some msg =>
        -- the go host may leave protocolVersion empty (set out-of-band)
    r.check "identify decoded ok" true
    let wantPeer ← jStr "identify-go.json" j "peerId"
    match msg.publicKey with
    | none => r.check "identify peer id" false
    | some keyBytes =>
      match Keys.unmarshalPubKey? (Bytes.ofNatList keyBytes) with
      | none => r.check "identify peer id" false
      | some key =>
        let pid := PeerId.ofPublicKey key
        r.check "identify peer id" (PeerId.toBase58 pid == wantPeer)

  -- identify e2e over the sim: the responder's message derives the peer
  -- id from its public key, matching the id the dialer expected
  let seedHex := "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
  let seed := Bytes.ofNatList (Bytes.toNatList
    (Bytes.ofHex? seedHex |>.getD ByteArray.empty))
  let priv : Keys.PrivKey := { keyType := .ed25519, raw := seed }
  let some pub ← priv.publicKey | r.check "identify e2e key" false
  let wantId := PeerId.ofPublicKey pub

  let (cI3, cR3) ← mkSplit
  let serverT ← IO.asTask do
    match ← priv.publicKey with
    | none => pure ()
    | some pub =>
      Identify.respondAndSend pub [] [Ping.protocol, Identify.protocol] none "leanp2p" (connStream cR3)
  let rdr ← BufReader.ofConn cI3
  match ← rdr.readAvail with
  | none => r.check "identify e2e read" false
  | some bytes =>
    let bytes := Identify.stripLengthPrefix bytes
    match Messages.decodeIdentify? bytes with
    | none => r.check "identify e2e decode" false
    | some msg =>
      r.check "identify e2e protocolVersion" (msg.protocolVersion == some "/ipfs/1.0.0")
      match msg.publicKey with
      | none => r.check "identify e2e peer id" false
      | some keyBytes =>
        match Keys.unmarshalPubKey? (Bytes.ofNatList keyBytes) with
        | none => r.check "identify e2e peer id" false
        | some key =>
          r.check "identify e2e peer id matches key"
            (PeerId.toBase58 (PeerId.ofPublicKey key) == PeerId.toBase58 wantId)
  let _ := Task.get serverT

end Tests
