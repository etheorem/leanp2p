import Tests.Support

/-!
# Noise XX suite (VECTOR_TEST_PLAN.md, phase 3 step 16)

Mirrors:
- the Noise framework vector for `Noise_XX_25519_ChaChaPoly_SHA256`
  (vendor/cacophony `vectors/cacophony.txt`: prologue, fixed keys, all
  message ciphertexts, handshake hash, and post-handshake transport
  records) - replayed deterministically;
- the captured go-libp2p transcript (`noise-go-transcript.json`): a real
  go-libp2p `noise.Transport` initiator completed a handshake against this
  implementation's deterministic responder in the capture run, so the
  Lean replay of the responder role is a byte-level conformance check
  (message 2 must reproduce byte-for-byte, message 3 must decrypt and
  verify, and the derived cipher states must round-trip the recorded
  transport frames);
- an in-process handshake over the sim with the full libp2p payload
  (identity key, `noise-libp2p-static-key:` signature, muxer extension).
-/

open LeanP2P Tests

namespace Tests

/-! ## helpers -/

private def bytesOf (hex : String) : ByteArray :=
  match Bytes.ofHex? hex with
  | some b => b
  | none => ByteArray.empty

private def bx (hex : String) : List Nat :=
  Bytes.toNatList (bytesOf hex)

private def simPair : IO (Connection × Connection) := do
  let c2s ← Pipe.new
  let s2c ← Pipe.new
  let client : Connection :=
    { read := s2c.read, write := c2s.push,
      close := do c2s.close; s2c.close
      localAddr := { components := [] }, remoteAddr := { components := [] } }
  let server : Connection :=
    { read := c2s.read, write := s2c.push,
      close := do c2s.close; s2c.close
      localAddr := { components := [] }, remoteAddr := { components := [] } }
  pure (client, server)

private def noiseKeys (privHex : String) : IO (Keys.PrivKey × ByteArray) := do
  let identity : Keys.PrivKey := { keyType := .ed25519, raw := bytesOf privHex }
  let some static ← OpenSsl.randomBytes 32 | throw <| IO.userError "no random"
  pure (identity, static)

def NoiseSuite.run (r : Runner) : IO Unit := do
  r.section "Noise XX"
    "Noise framework vectors (Noise_XX_25519_ChaChaPoly_SHA256) + captured \
     go-libp2p noise Transport transcript"

  -- RFC 8439 section 2.8.2: anchors the ChaCha20-Poly1305 shim byte-for-byte
  let rfcKey := bytesOf "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
  let rfcNonce := bytesOf "070000004041424344454647"
  let rfcAd := bytesOf "50515253c0c1c2c3c4c5c6c7"
  let rfcPt := Bytes.ofString
    "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."
  let rfcCt := bytesOf "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b61161ae10b594f09e26a7e902ecbd0600691"
  match ← OpenSsl.chacha20poly1305Seal rfcKey rfcNonce rfcAd rfcPt with
  | none => r.check "noise: chacha seal (RFC 8439)" false
  | some ct => do
    r.check "noise: chacha seal (RFC 8439)" (ct == rfcCt)
    let open1 ← OpenSsl.chacha20poly1305Open rfcKey rfcNonce rfcAd rfcCt
    r.check "noise: chacha open (RFC 8439)" (open1 == some rfcPt)
    let open2 ← OpenSsl.chacha20poly1305Open rfcKey rfcNonce
      (Bytes.ofString "wrong aad") rfcCt
    r.check "noise: chacha rejects wrong ad" (open2 == none)
    let open3 ← OpenSsl.chacha20poly1305Open rfcKey
      (bytesOf "070000004041424344454648") rfcAd rfcCt
    r.check "noise: chacha rejects wrong nonce" (open3 == none)


  -- Noise framework vectors (flynn/noise vectors.txt, the exact library
  -- go-libp2p uses): full deterministic replay of every
  -- Noise_XX_25519_ChaChaPoly_SHA256 entry
  let j ← loadJson "noise-vectors.json"
  let cases ← jArr "noise-vectors.json" j "cases"
  for cIdx in [0:cases.length] do
    let c := cases[cIdx]!
    let label := s!"noise vector {cIdx}"
    let prologueHex ← jStr? "noise-vectors.json" c "prologue"
    let hsHashHex ← jStr? "noise-vectors.json" c "handshakeHash"
    let prologue := match prologueHex with
      | some h => bytesOf h
      | none => ByteArray.empty
    let initStatic := bytesOf (← jStr "noise-vectors.json" c "initStatic")
    let initEph := bytesOf (← jStr "noise-vectors.json" c "initEphemeral")
    let respStatic := bytesOf (← jStr "noise-vectors.json" c "respStatic")
    let respEph := bytesOf (← jStr "noise-vectors.json" c "respEphemeral")
    let msgs ← jArr "noise-vectors.json" c "messages"
    let payloadOf (i : Nat) : IO ByteArray := do
      bytesOf <$> jStr "noise-vectors.json" msgs[i]! "payload"
    let cipherOf (i : Nat) : IO ByteArray := do
      bytesOf <$> jStr "noise-vectors.json" msgs[i]! "ciphertext"

    let some hsI0 ← Noise.HandshakeState.init true initStatic prologue
      | r.check s!"{label}: init initiator" false
    let some hsR0 ← Noise.HandshakeState.init false respStatic prologue
      | r.check s!"{label}: init responder" false
    let hsI1 := { hsI0 with efix := some initEph }
    let hsR1 := { hsR0 with efix := some respEph }

    -- -> e (+ keyless payload)
    let p0 ← payloadOf 0
    let c0 ← cipherOf 0
    match ← hsI1.writeMsg1 p0 with
    | none => r.check s!"{label} msg1" false
    | some (m0, hsI2) => do
      r.check s!"{label} msg1 ciphertext" (m0 == c0)
      match ← hsR1.readMsg1 m0 with
      | none => r.check s!"{label} msg1 read" false
      | some (rp0, hsR2) => do
        r.check s!"{label} msg1 payload" (rp0 == p0)
        -- <- e, ee, s, es (+ payload)
        let p1 ← payloadOf 1
        let c1 ← cipherOf 1
        match ← hsR2.writeMsg2 p1 with
        | none => r.check s!"{label} msg2" false
        | some (m1, hsR3) => do
          r.check s!"{label} msg2 ciphertext" (m1 == c1)
          match ← hsI2.readMsg2 m1 with
          | none => r.check s!"{label} msg2 read" false
          | some (rp1, hsI3) => do
            r.check s!"{label} msg2 payload" (rp1 == p1)
            -- -> s, se (+ payload)
            let p2 ← payloadOf 2
            let c2 ← cipherOf 2
            match ← hsI3.writeMsg3 p2 with
            | none => r.check s!"{label} msg3" false
            | some (m2, hsI4) => do
              r.check s!"{label} msg3 ciphertext" (m2 == c2)
              match ← hsR3.readMsg3 m2 with
              | none => r.check s!"{label} msg3 read" false
              | some (rp2, hsR4) => do
                r.check s!"{label} msg3 payload" (rp2 == p2)
                -- transport messages over the split cipher states
                let (kI, _) := hsI4.ss.split
                let (_, kR) := hsR4.ss.split
                let extra := msgs.length - 3
                let rec transport (i : Nat) (enc dec : Noise.CipherState) :
                    IO Unit := do
                  if i ≥ extra then pure ()
                  else do
                    let pt ← payloadOf (3 + i)
                    let ct ← cipherOf (3 + i)
                    if (3 + i) % 2 == 1 then
                      -- initiator -> responder (msg indices 3, 5, ...)
                      match ← enc.encrypt ByteArray.empty pt with
                      | none => r.check s!"{label} transport enc {i}" false
                      | some (got, enc') => do
                        r.check s!"{label} transport ct {i}" (got == ct)
                        transport (i + 1) enc' dec
                    else
                      -- responder -> initiator (msg indices 4, 6, ...)
                      match ← dec.encrypt ByteArray.empty pt with
                      | none => r.check s!"{label} transport enc {i}" false
                      | some (got, dec') => do
                        r.check s!"{label} transport ct {i}" (got == ct)
                        transport (i + 1) enc dec'
                transport 0 kI kR

  -- captured go-libp2p transcript: Lean replays the responder

  let nj ← loadJson "noise-go-transcript.json"
  let respStaticGo := bytesOf (← jStr "noise-go-transcript.json" nj "respStaticNoiseHex")
  let respEphGo := bytesOf (← jStr "noise-go-transcript.json" nj "respEphemeralPrivHex")
  let respPayload := bytesOf (← jStr "noise-go-transcript.json" nj "respPayloadHex")
  let initPayload := bytesOf (← jStr "noise-go-transcript.json" nj "initPayloadHex")
  let initIdentityPub := bytesOf (← jStr "noise-go-transcript.json" nj "initIdentityPubHex")
  let initPeerId ← jStr "noise-go-transcript.json" nj "initPeerId"
  let muxers ← jStrs "noise-go-transcript.json" nj "extensionsMuxers"
  let some hsG0 ← Noise.HandshakeState.init false respStaticGo
    | r.check "noise go transcript: init" false
  let hsG1 := { hsG0 with efix := some respEphGo }

  let entries ← jArr "noise-go-transcript.json" nj "messages"
  let wireOf (i : Nat) : IO ByteArray := do
    bytesOf <$> jStr "noise-go-transcript.json" entries[i]! "hex"
  let dirOf (i : Nat) : IO String := do
    jStr "noise-go-transcript.json" entries[i]! "dir"
  -- recorded writes carry the 2-byte length prefix; strip it
  let unframe (b : ByteArray) : ByteArray := b.extract 2 b.size

  let w1 ← wireOf 0
  let d0 ← dirOf 0
  r.check "noise go: entry 0 is i2r" (d0 == "i2r")
  match ← hsG1.readMsg1 (unframe w1) with
  | none => r.check "noise go: read msg1" false
  | some (_, hsG2) => do
    match ← hsG2.writeMsg2 respPayload with
    | none => r.check "noise go: write msg2" false
    | some (m2, hsG3) => do
      let w2 ← wireOf 1
      let d1 ← dirOf 1
      r.check "noise go: entry 1 is r2i" (d1 == "r2i")
      -- the deterministic responder must reproduce the recorded message
      r.check "noise go: msg2 byte-identical" (m2 == unframe w2)
      let w3 ← wireOf 2
      let d2 ← dirOf 2
      r.check "noise go: entry 2 is i2r" (d2 == "i2r")
      match ← hsG3.readMsg3 (unframe w3) with
      | none => r.check "noise go: read msg3" false
      | some (gotPayload, hsG4) => do
        r.check "noise go: msg3 payload matches recording" (gotPayload == initPayload)
        match hsG4.rs with
        | none => r.check "noise go: remote static learned" false
        | some rs => do
          match ← Noise.verifyPayload gotPayload rs with
          | none => r.check "noise go: initiator payload verifies" false
          | some (initKey, _) => do
            r.check "noise go: initiator identity key"
              (initKey.raw == initIdentityPub)
            let initPid := PeerId.toBase58 (PeerId.ofPublicKey initKey)
            r.check "noise go: initiator peer id" (initPid == initPeerId)
            let (k1, k2) := hsG4.ss.split
            -- entries 3..6: ping, pong, ping, pong over the derived states
            let ping0 ← wireOf 3
            let pong0 ← wireOf 4
            let ping1 ← wireOf 5
            let pong1 ← wireOf 6
            let d3 ← dirOf 3
            let d4 ← dirOf 4
            let d5 ← dirOf 5
            let d6 ← dirOf 6
            r.check "noise go: transport directions"
              (d3 == "i2r" ∧ d4 == "r2i" ∧ d5 == "i2r" ∧ d6 == "r2i")
            match ← k1.decrypt ByteArray.empty (unframe ping0) with
            | none => r.check "noise go: decrypt ping-0" false
            | some (pt0, k1b) => do
              r.check "noise go: ping-0 plaintext" (pt0 == Bytes.ofString "ping-0")
              match ← k2.encrypt ByteArray.empty (Bytes.ofString "pong:ping-0") with
              | none => r.check "noise go: encrypt pong-0" false
              | some (ct0, k2b) => do
                r.check "noise go: pong-0 byte-identical" (ct0 == unframe pong0)
                match ← k1b.decrypt ByteArray.empty (unframe ping1) with
                | none => r.check "noise go: decrypt ping-1" false
                | some (pt1, _) => do
                  r.check "noise go: ping-1 plaintext" (pt1 == Bytes.ofString "ping-1")
                  match ← k2b.encrypt ByteArray.empty (Bytes.ofString "pong:ping-1") with
                  | none => r.check "noise go: encrypt pong-1" false
                  | some (ct1, _) => r.check "noise go: pong-1 byte-identical" (ct1 == unframe pong1)
            -- the stock go-libp2p initiator sends no extensions
            match Messages.decodeNoisePayload? gotPayload with
            | none => r.check "noise go: payload decodes" false
            | some p =>
              r.check "noise go: initiator sends no extensions"
                ((p.extensions.map (·.streamMuxers)).getD [] == [])
            -- the deterministic responder's payload advertises the muxers
            match Messages.decodeNoisePayload? respPayload with
            | none => r.check "noise go: responder payload decodes" false
            | some rp =>
              r.check "noise go: muxer extension"
                (rp.extensions.map (·.streamMuxers) == some muxers)

  -- in-process handshake over the sim (full libp2p payload)

  let (cI, cR) ← simPair
  let (idI, staticI) ← noiseKeys
    "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb"
  let (idR, staticR) ← noiseKeys
    "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"

  let responderTask ← IO.asTask (Noise.handshake idR staticR .responder cR)
  let secI? ← Noise.handshake idI staticI .initiator cI
  let secR? := match responderTask.get with
    | .ok v => v | .error _ => none

  r.check "noise sim: initiator handshake" secI?.isSome
  r.check "noise sim: responder handshake" secR?.isSome
  match secI?, secR? with
  | some secI, some secR => do
    let idIPub := (← idI.publicKey)
    r.check "noise sim: initiator peer id known to responder"
      (idIPub.map (PeerId.ofPublicKey · == secR.remotePeer) == some true)
    r.check "noise sim: responder peer id known to initiator"
      (secI.remotePeer == secR.localPeer)
    secI.write (Bytes.ofString "hello from initiator")
    let r1 ← secR.read
    r.check "noise sim: encrypted round trip"
      (r1 == some (Bytes.ofString "hello from initiator"))
    secR.write (Bytes.ofString "hello from responder")
    let r2 ← secI.read
    r.check "noise sim: encrypted round trip 2"
      (r2 == some (Bytes.ofString "hello from responder"))
  | _, _ => pure ()

  -- tampered handshake payload aborts the connection: the signature in the
  -- initiator's payload is made by a different identity than the one it carries
  let (cI3, cR3) ← simPair
  let (idGood, staticGood) ← noiseKeys
    "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb"
  let (idEvil, staticEvil) ← noiseKeys
    "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
  let some hsE0 ← Noise.HandshakeState.init true staticGood ByteArray.empty
    | r.check "noise sim: forged init" false
  let some statPubGood ← OpenSsl.x25519Pubkey staticGood | return ()
  -- payload carrying idEvil's key but signed with idGood's private key
  let evilPub? ← idEvil.publicKey
  let sig? ← idGood.sign (Noise.sigInput statPubGood)
  let forgedPayload : ByteArray :=
    match evilPub?, sig? with
    | some evilPub, some sig =>
      Messages.encodeNoisePayloadB
        { identityKey := Bytes.toNatList (Keys.marshalPubKey evilPub)
          identitySig := Bytes.toNatList sig
          extensions := none }
    | _, _ => ByteArray.empty
  let some (m0f, hsE1) ← hsE0.writeMsg1 ByteArray.empty | return ()
  let readerE ← BufReader.ofConn cI3
  let readerR ← BufReader.ofConn cR3
  Noise.writeFramed cI3 m0f
  let some hsV0 ← Noise.HandshakeState.init false staticEvil ByteArray.empty
    | r.check "noise sim: forged resp init" false
  let responderV ← IO.asTask (do
    let some w1 ← Noise.readFramed readerR | return none
    let some (_, hsV1) ← hsV0.readMsg1 w1 | return none
    let some (m2, hsV2) ← hsV1.writeMsg2 (Bytes.ofString "hello") | return none
    Noise.writeFramed cR3 m2
    let some w3 ← Noise.readFramed readerR | return none
    match ← hsV2.readMsg3 w3 with
    | none => return none
    | some (payload, _) => return some payload : IO (Option ByteArray))
  -- initiator consumes the responder's message 2, sends the forged message 3
  let some w2f ← Noise.readFramed readerE | return ()
  let some (_, hsE2) ← hsE1.readMsg2 w2f | return ()
  let some (m3f, _) ← hsE2.writeMsg3 forgedPayload | return ()
  Noise.writeFramed cI3 m3f
  let forgedRv := match responderV.get with
    | .ok v => v | .error _ => none
  -- the responder must reject: the payload's identity key does not match the signature
  let some statPubGood2 ← OpenSsl.x25519Pubkey staticGood | return ()
  let vres : Option (Option (Keys.PubKey × List String)) ←
    match forgedRv with
    | none => pure none
    | some payload => do
      let v ← Noise.verifyPayload payload statPubGood2
      pure (some v)
  let forgedRejected : Bool :=
    match vres with
    | none => true
    | some v => match v with
      | none => true
      | some _ => false
  r.check "noise sim: forged identity rejected by responder" forgedRejected
  let _ := idGood
  let _ := staticEvil

end Tests
