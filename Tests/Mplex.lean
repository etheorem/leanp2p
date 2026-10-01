import Tests.Support

/-!
# mplex suite (VECTOR_TEST_PLAN.md, phase 3 step 19)

Mirrors vendor/specs/mplex/README.md: header varint layout
(`(id << 3) | flag`), the seven flags, the 1 MiB cap, and the message
flow (NewStream / MessageReceiver-Initiator / Close / Reset) exercised
over the byte-splitting sim, stepped deterministically.
-/

open LeanP2P Tests

namespace Tests

private def mkSplit : IO (Connection × Connection) := do
  let p1 ← BytePipe.new
  let p2 ← BytePipe.new
  let (a, b) := SimNet.splice p1 p2 { components := [] }
  pure (a.byteSplitting, b)

def MplexSuite.run (r : Runner) : IO Unit := do
  r.section "mplex"
    "libp2p/specs mplex README: header layout + message flow"

  -- header layout: NewStream for id 5 (odd = initiator)
  r.check "mplex header newstream id5"
    (Mplex.encodeMsg { flag := Mplex.fNewStream, id := 5, payload := Bytes.toNatList (Bytes.ofString "demo") }
      == [40, 4, 100, 101, 109, 111])
  -- header layout: MessageReceiver on id 1, empty payload
  r.check "mplex header msgreceiver id1"
    (Mplex.encodeMsg { flag := Mplex.fMessageReceiver, id := 1, payload := [] } == [9, 0])
  -- header layout: CloseInitiator on id 3
  r.check "mplex header closeinitiator id3"
    (Mplex.encodeMsg { flag := Mplex.fCloseInitiator, id := 3, payload := [] } == [28, 0])
  -- header layout: ResetReceiver on id 7
  r.check "mplex header resetreceiver id7"
    (Mplex.encodeMsg { flag := Mplex.fResetReceiver, id := 7, payload := [] } == [61, 0])

  -- decode round trip
  match Mplex.decodeMsg? (Mplex.encodeMsg
      { flag := Mplex.fMessageInitiator, id := 9, payload := Bytes.toNatList (Bytes.ofString "hello") }) with
  | .done m consumed =>
    let expected := (Mplex.encodeMsg { flag := Mplex.fMessageInitiator, id := 9, payload := Bytes.toNatList (Bytes.ofString "hello") }).length
    r.check "mplex decode roundtrip" (m.id == 9 ∧ consumed == expected)
  | _ => r.check "mplex decode roundtrip" false

  -- decode consumes a header off a longer buffer
  match Mplex.decodeMsg? (Mplex.encodeMsg
      { flag := Mplex.fCloseReceiver, id := 2, payload := [] } ++ [7]) with
  | .done m consumed =>
    r.check "mplex decode rest" (m.id == 2 ∧ consumed == 2)
  | _ => r.check "mplex decode rest" false

  -- the 1 MiB cap rejects oversized payloads
  match Mplex.decodeMsg? (Mplex.encodeMsg
      { flag := Mplex.fMessageInitiator, id := 0,
        payload := List.replicate (Mplex.maxMsg + 1) 1 }) with
  | .bad => r.check "mplex 1MiB cap rejects" true
  | _ => r.check "mplex 1MiB cap rejects" false

  -- NewStream + data over the byte-splitting sim, stepped
  let (cI, cR) ← mkSplit
  let client ← Mplex.MplexSession.make cI true
  let server ← Mplex.MplexSession.make cR false
  let some st ← client.openStream "/ipfs/kad/1.0.0" | r.check "mplex e2e open" false
  st.write (Bytes.ofString "mplex-data")
  -- the server pump processes NewStream and MessageInitiator
  let s1 ← server.pumpOne
  let s2 ← server.pumpOne
  r.check "mplex e2e server processed" (s1 ∧ s2)
  let streams ← server.streams.get
  r.check "mplex e2e incoming stream" (streams.any (·.1 == (0, false)))
  let serverStreams ← server.streams.get
  let payload ← match serverStreams.lookup (0, false) with
    | some sst => sst.pipe.read
    | none => pure none
  r.check "mplex e2e payload" (payload == some (Bytes.ofString "mplex-data"))
  -- the server application echoes via its own stream view (it is the
  -- stream receiver, so it writes with the MessageReceiver flag; the
  -- client routes that to its locally-initiated stream (0, true))
  match payload with
  | none => r.check "mplex e2e echo" false
  | some b => do
    server.writeMsg { flag := Mplex.fMessageReceiver, id := 0, payload := Bytes.toNatList b }
      let cstep ← client.pumpOne
    r.check "mplex e2e client processed" cstep
    let echoed ← st.read
    r.check "mplex e2e echo" (echoed == some b)
  st.close
  -- the server pump processes the CloseInitiator and closes its stream view
  let sclose ← server.pumpOne
  let serverStreams2 ← server.streams.get
  let openState ← match serverStreams2.lookup (0, false) with
    | some sst => sst.open_.get
    | none => pure true
  r.check "mplex e2e close" (sclose ∧ openState == false)

  -- reset: the peer's stream is torn down
  let (cI2, cR2) ← mkSplit
  let client2 ← Mplex.MplexSession.make cI2 true
  let server2 ← Mplex.MplexSession.make cR2 false
  let some st2 ← client2.openStream "/demo" | r.check "mplex reset open" false
  st2.reset
  -- the server pump processes NewStream, then ResetInitiator
  let _ ← server2.pumpOne
  let r1 ← server2.pumpOne
  let serverStreams3 ← server2.streams.get
  let openState ← match serverStreams3.lookup (0, false) with
    | some sst => sst.open_.get
    | none => pure true
  r.check "mplex e2e reset" (r1 ∧ openState == false)

end Tests
