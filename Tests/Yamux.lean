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
  let client ← Yamux.YamuxSession.make cI true
  let server ← Yamux.YamuxSession.make cR false

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

end Tests
