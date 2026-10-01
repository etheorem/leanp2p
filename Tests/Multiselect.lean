import Tests.Support

/-!
# multistream-select suite (VECTOR_TEST_PLAN.md, phase 3 step 15)

Mirrors:
- libp2p/specs connections/README.md wire examples (`na` framing) and the
  multistream-select README (`ls` request/reply framing);
- go-multistream captured traces (`mss-go-trace.json`): full negotiation,
  `na` answer, and the lazy client whose header and proposal are written
  back-to-back before any response is read;
- the go-multistream `lpReadBuf` 1024-byte message cap;
- two-party negotiations over the sim, including a hostile transport that
  splits every write into single bytes (buffered reader test).
-/

open LeanP2P Tests

namespace Tests

private def deadPipe : IO BytePipe := do
  let p ← BytePipe.new
  p.close
  pure p

/-- Replay a captured trace against our listener: initiator writes are
fed into the reader's buffer, then the negotiation runs and our replies
are compared byte-for-byte with go's responder writes. -/
private def replayTrace (r : Runner) (name : String) (trace : List Lean.Json)
    (supported : List String) (expectSelect : Option String) : IO Unit := do
  let mut i2r : ByteArray := ByteArray.empty
  let mut r2i : List ByteArray := []
  for e in trace do
    let dir ← jStr "trace" e "dir"
    let b ← hexBytesByteArray (← jStr "trace" e "hex")
    if dir == "i2r" then
      i2r := i2r ++ b
    else
      r2i := r2i ++ [b]
  let dead ← deadPipe
  let rdr ← BufReader.ofConn (BytePipe.conn dead dead { components := [] })
  rdr.buf.set i2r
  let outW ← BytePipe.new
  let outC := BytePipe.conn dead outW { components := [] }
  let got ← Multiselect.selectResponder rdr outC supported
  r.check s!"mss go {name}: selection" (got == expectSelect)
  let produced ← outW.peek
  r.check s!"mss go {name}: reply bytes" (produced == r2i.foldl (· ++ ·) ByteArray.empty)

def MultiselectSuite.run (r : Runner) : IO Unit := do
  r.section "multistream-select"
    "libp2p/specs connections/README.md + multistream-select README + \
     go-multistream captured traces"

  -- wire examples (connections/README.md `na` + header framing)
  let j ← loadJson "mss-wire.json"
  for c in (← jArr "mss-wire.json" j "cases") do
    let msg ← jStr "mss-wire.json" c "message"
    let hex ← jStr "mss-wire.json" c "bytesHex"
    let want ← hexBytes hex
    let body : String := if msg.endsWith "\n" then (msg.dropEnd 1).toString else msg
    r.check s!"mss wire {body}" (Multiselect.msgBytes body == want)

  -- ls reply framing (multistream-select README, Listing)
  let ls ← loadJson "mss-ls.json"
  let lsHex ← jStr "mss-ls.json" ls "lsWireHex"
  r.check "mss ls wire" (Multiselect.msgBytes "ls" == (← hexBytes lsHex))
  let reply ← jObj "mss-ls.json" ls "replyExample"
  let protos ← jStrs "mss-ls.json" reply "protocols"
  let bodyHex ← jStr "mss-ls.json" reply "bodyHex"
  let body ← hexBytes bodyHex
  r.check "mss ls reply encode" (Multiselect.lsPayload protos == body)
  r.check "mss ls reply decode" (Multiselect.decodeLsPayload? body == some protos)

  -- message cap (go-multistream lpReadBuf)
  let long := String.pushn "/proto/" 'x' 1024
  match Multiselect.decodeMsg? (Bytes.ofNatList (Multiselect.msgBytes long)) with
  | .bad => r.check "mss 1024 cap rejects" true
  | _ => r.check "mss 1024 cap rejects" false
  match Multiselect.decodeMsg? (Bytes.ofNatList (Multiselect.msgBytes "/probe/1.0.0")) with
  | .done s c =>
    r.check "mss decode ok" (s == "/probe/1.0.0" ∧ c == (Multiselect.msgBytes "/probe/1.0.0").length)
  | _ => r.check "mss decode ok" false

  -- captured go-multistream traces
  let g ← loadJson "mss-go-trace.json"
  let naWire ← hexBytes (← jStr "mss-go-trace.json" g "naWireHex")
  let headerWire ← hexBytes (← jStr "mss-go-trace.json" g "headerWireHex")
  r.check "mss go na wire" (Multiselect.msgBytes "na" == naWire)
  r.check "mss go header wire" (Multiselect.msgBytes Multiselect.header == headerWire)

  let fullTrace ← jArr "mss-go-trace.json" g "fullTrace"
  replayTrace r "full trace" fullTrace ["/ipfs/kad/1.0.0"] (some "/ipfs/kad/1.0.0")
  let naTrace ← jArr "mss-go-trace.json" g "naTrace"
  -- the go client gives up after na; our responder would keep looping, so
  -- only the written bytes up to (and including) na are compared here by
  -- selecting nothing and letting EOF end the loop
  replayTrace r "na trace" naTrace ["/ipfs/kad/1.0.0"] none
  let lazyTrace ← jArr "mss-go-trace.json" g "lazyTrace"
  replayTrace r "lazy trace" lazyTrace ["/ipfs/kad/1.0.0"] (some "/ipfs/kad/1.0.0")

  -- the lazy client's very first write carries header AND proposal
  let mut lazyI2R : ByteArray := ByteArray.empty
  for e in lazyTrace do
    if (← jStr "trace" e "dir") == "i2r" then
      lazyI2R := lazyI2R ++ (← hexBytesByteArray (← jStr "trace" e "hex"))
  r.check "mss go lazy coalesced write"
    (lazyI2R == Bytes.ofNatList (Multiselect.msgBytes Multiselect.header
      ++ Multiselect.msgBytes "/ipfs/kad/1.0.0"))

  -- two-party negotiations over the sim, byte-splitting transport

  let splitPair : IO (Connection × Connection) := do
    let p1 ← BytePipe.new
    let p2 ← BytePipe.new
    let (a, b) := SimNet.splice p1 p2 { components := [] }
    pure (a.byteSplitting, b)

  -- supported protocol, full negotiation
  let (cI1, cR1) ← splitPair
  let resp1 ← IO.asTask (do
    let rdr ← BufReader.ofConn cR1
    Multiselect.selectResponder rdr cR1 ["/ipfs/kad/1.0.0", "/ipfs/id/1.0.0"])
  let rdrI1 ← BufReader.ofConn cI1
  let r1 ← Multiselect.selectInitiator rdrI1 cI1 "/ipfs/kad/1.0.0"
  let r1v := match resp1.get with
    | .ok v => v | .error _ => none
  r.check "mss split e2e" (r1 == some "/ipfs/kad/1.0.0" ∧ r1v == some "/ipfs/kad/1.0.0")

  -- unsupported protocol: initiator sees na and gives up
  let (cI2, cR2) ← splitPair
  let resp2 ← IO.asTask (do
    let rdr ← BufReader.ofConn cR2
    Multiselect.selectResponder rdr cR2 ["/ipfs/kad/1.0.0"])
  let rdrI2 ← BufReader.ofConn cI2
  let r2 ← Multiselect.selectInitiator rdrI2 cI2 "/nope/9.9.9"
  cR2.close
  let r2v := match resp2.get with
    | .ok v => v | .error _ => none
  r.check "mss split e2e na" (r2 == none ∧ r2v == none)

  -- lazy dialer end to end
  let (cI3, cR3) ← splitPair
  let resp3 ← IO.asTask (do
    let rdr ← BufReader.ofConn cR3
    Multiselect.selectResponder rdr cR3 ["/ipfs/kad/1.0.0"])
  let rdrI3 ← BufReader.ofConn cI3
  let r3 ← Multiselect.selectInitiatorLazy rdrI3 cI3 "/ipfs/kad/1.0.0"
  let r3v := match resp3.get with
    | .ok v => v | .error _ => none
  r.check "mss split e2e lazy" (r3 == some "/ipfs/kad/1.0.0" ∧ r3v == some "/ipfs/kad/1.0.0")

  -- ls end to end
  let (cI4, cR4) ← splitPair
  let resp4 ← IO.asTask (do
    let rdr ← BufReader.ofConn cR4
    Multiselect.selectResponder rdr cR4 ["/ipfs/kad/1.0.0", "/ipfs/id/1.0.0"])
  let rdrI4 ← BufReader.ofConn cI4
  let r4 ← Multiselect.listProtocols rdrI4 cI4
  cR4.close
  let r4v := match resp4.get with
    | .ok v => v | .error _ => none
  r.check "mss split e2e ls" (r4 == some ["/ipfs/kad/1.0.0", "/ipfs/id/1.0.0"]
    ∧ r4v == none)

end Tests
