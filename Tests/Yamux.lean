import Tests.Support

/-!
# yamux suite (VECTOR_TEST_PLAN.md, phase 3 step 18)

Mirrors vendor/specs/yamux/README.md (the hashicorp spec, verbatim):
- 12-byte big-endian header layout with the frame-type and flag code
  points (unit vectors derived from the spec's field table);
- decode/encode round trip;
- stream state machine (SYN/ACK/FIN/RST), window accounting, ping echo
  and GoAway exercised over the sim, including a hostile transport that
  splits every write into single bytes.
-/

open LeanP2P Tests

namespace Tests

private def hdrBytes (v t fl sid len : Nat) : List Nat :=
  Yamux.encode { version := v, typ := t, flags := fl, streamID := sid, length := len }

private def mkSplit : IO (Connection × Connection) := do
  let p1 ← BytePipe.new
  let p2 ← BytePipe.new
  let (a, b) := SimNet.splice p1 p2 { components := [] }
  pure (a.byteSplitting, b)

def YamuxSuite.run (r : Runner) : IO Unit := do
  r.section "yamux"
    "libp2p/specs yamux README (hashicorp spec): framing + state machine"

  -- Data frame carrying 3 bytes on stream 5 (odd = client-initiated).
  r.check "yamux header data"
    (hdrBytes Yamux.version0 Yamux.tData 0 5 3 ==
      [0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 3])
  -- WindowUpdate SYN opening stream 7 with the 256 KiB initial window.
  r.check "yamux header windowupdate syn"
    (hdrBytes Yamux.version0 Yamux.tWindowUpdate Yamux.fSYN 7 Yamux.initialWindow ==
      [0, 1, 0, 1, 0, 0, 0, 7, 0, 4, 0, 0])
  -- Ping (SYN) with opaque value 42 on the session stream.
  r.check "yamux header ping"
    (hdrBytes Yamux.version0 Yamux.tPing Yamux.fSYN 0 42 == [0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 42])
  -- GoAway normal termination.
  r.check "yamux header goaway"
    (hdrBytes Yamux.version0 Yamux.tGoAway 0 0 0 == [0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
  -- Data frame with FIN.
  r.check "yamux header data fin"
    (hdrBytes Yamux.version0 Yamux.tData Yamux.fFIN 3 1 == [0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 1])

  -- round trip
  let h : Yamux.Header := ({ version := 0, typ := Yamux.tData, flags := 3, streamID := 4294967295, length := 65535 })
  match Yamux.decode? (Yamux.encode h) with
  | some (got, rest) =>
    r.check "yamux decode roundtrip" (got == h ∧ rest == [])
  | none => r.check "yamux decode roundtrip" false
  -- decode consumes a header off a longer buffer
  match Yamux.decode? (hdrBytes 0 Yamux.tPing Yamux.fACK 0 1 ++ [9, 9]) with
  | some (_, rest) => r.check "yamux decode rest" (rest == [9, 9])
  | none => r.check "yamux decode rest" false

  -- two-party session over the byte-splitting sim, stepped deterministically
  let (cI, cR) ← mkSplit
  let client ← Yamux.YamuxSession.make (← BufReader.ofConn cI) true
  let server ← Yamux.YamuxSession.make (← BufReader.ofConn cR) false

  let some st ← client.openStream | r.check "yamux e2e open" false
  st.write (Bytes.ofString "yamux-payload")
  let step1 ← server.pumpOne
  let step2 ← server.pumpOne
  r.check "yamux e2e server processed frames" (step1 ∧ step2)
  let serverStreams ← server.streams.get
  r.check "yamux e2e incoming stream" (serverStreams.any (·.1 == 1))
  -- step 5 (interop): accepting a stream must emit the ACK window update
  -- (the ACK rides the control queue; the control task emits it)
  let ackOut ← server.controlOne
  let ack ← client.pumpOne
  r.check "yamux e2e accepted stream acked" (ackOut ∧ ack)
  let payload ← match serverStreams.lookup 1 with
    | some sst => sst.pipe.read
    | none => pure none
  r.check "yamux e2e payload" (payload == some (Bytes.ofString "yamux-payload"))
  match payload with
  | none => r.check "yamux e2e echo" false
  | some b => do
    -- the server application echoes via its own stream view
    match serverStreams.lookup 1 with
    | none => r.check "yamux e2e echo" false
    | some sst => do
      server.writeStream 1 sst b
      let cstep ← client.pumpOne
      r.check "yamux e2e client processed" cstep
      let echoed ← st.read
      r.check "yamux e2e echo" (echoed == some b)
  st.close
  let stepFin ← server.pumpOne
  r.check "yamux e2e fin" stepFin

  client.windowUpdate 1 64
  let wu ← server.pumpOne
  r.check "yamux e2e window update" wu
  client.ping 7
  let pinged ← server.pumpOne
  r.check "yamux e2e ping processed" pinged
  -- the ping echo rides the control queue; the control task emits it
  let pongOut ← server.controlOne
  let pong ← client.pumpOne
  r.check "yamux e2e pong echoed" (pongOut ∧ pong)
  client.goaway 0
  let ga ← server.pumpOne
  r.check "yamux e2e goaway" (¬ ga)

  /- hostile frames: only a SYN (with the remote's parity) creates a
  stream; data beyond the receive window is a protocol error. -/
  let (cI3, cR3) ← mkSplit
  let c3 ← Yamux.YamuxSession.make (← BufReader.ofConn cI3) true
  let s3 ← Yamux.YamuxSession.make (← BufReader.ofConn cR3) false
  let hdrTo (t fl sid len : Nat) : ByteArray :=
    Bytes.ofNatList (Yamux.encode { version := Yamux.version0, typ := t, flags := fl, streamID := sid, length := len })
  -- Data for an unopened stream (right parity, but no SYN): dropped, no
  -- stream state is invented, later openStream cannot collide
  c3.conn.write (hdrTo Yamux.tData 0 3 3 ++ Bytes.ofNatList [1, 2, 3])
  let drop1 ← s3.pumpOne
  r.check "yamux unknown stream data dropped" (drop1 ∧ (← s3.streams.get).isEmpty)
  -- SYN with OUR parity (the server's own id space): rejected
  c3.conn.write (hdrTo Yamux.tWindowUpdate Yamux.fSYN 2 0)
  let drop2 ← s3.pumpOne
  r.check "yamux syn wrong parity rejected" (drop2 ∧ (← s3.streams.get).isEmpty)
  -- proper SYN (odd id) opens the stream, then data up to the granted
  -- receive window is accepted, one byte beyond is a violation
  c3.conn.write (hdrTo Yamux.tWindowUpdate Yamux.fSYN 5 0)
  let syn ← s3.pumpOne
  let big := ByteArray.mk (Array.replicate Yamux.initialWindow 7)
  c3.conn.write (hdrTo Yamux.tData 0 5 Yamux.initialWindow ++ big)
  let inWindow ← s3.pumpOne
  c3.conn.write (hdrTo Yamux.tData 0 5 1 ++ Bytes.ofNatList [9])
  let overWindow ← s3.pumpOne
  r.check "yamux receive window enforced" (syn ∧ inWindow ∧ ¬ overWindow ∧ (← s3.dead.get))

  /- parked-writer wake hand-off: a writer that used part of the credit
  passes the wake token to the next parked writer of the same stream. -/
  let (cI4, cR4) ← mkSplit
  let c4 ← Yamux.YamuxSession.make (← BufReader.ofConn cI4) true
  let s4 ← Yamux.YamuxSession.make (← BufReader.ofConn cR4) false
  let st4 ← Yamux.StreamState.new
  s4.streams.update fun sts => (sts ++ [(1, st4)], ())
  -- simulate: one writer parked on the credit channel, 150 bytes of
  -- credit granted by the peer
  st4.parked.update fun _ => (1, ())
  st4.sendWindow.update fun _ => (150, ())
  -- a 100-byte write: takes 100, leaves 50 credit and one parked writer
  -- -> the wake token must be handed on (without it, the second writer
  -- sleeps until the peer happens to grant more credit)
  s4.writeStream 1 st4 (ByteArray.mk (Array.replicate 100 9))
  let token ← st4.credit.recv
  r.check "yamux parked-writer handoff" token.isSome

end Tests
