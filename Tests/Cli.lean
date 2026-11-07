import Tests.Support
import CliApp.Demo
import CliApp.PingNode

/-!
# CLI orchestration checks

These tests inject host and protocol test values into the executable
workflows. They check argument handling, exact output, resource ownership
and fault cleanup. They perform no network handshake and do not count
as the live loopback or Go interoperability gates.
-/

set_option autoImplicit false

namespace Tests.Cli

open CliApp.Mock

/-- Every test owns its record; no mutable state is shared between runs. -/
structure Record where
  events : IO.Ref (List String)
  output : IO.Ref (List String)
  errors : IO.Ref (List String)
  allocations : IO.Ref Nat
  failAt : String
  faultAt : String

/-- An isolated, deterministic test run. -/
def Record.new (failAt : String := "") (faultAt : String := "") : IO Record := do
  return ⟨← IO.mkRef [], ← IO.mkRef [], ← IO.mkRef [], ← IO.mkRef 0, failAt, faultAt⟩

/-- Faults exercise finalizers underneath the protocol-error channel. -/
def Record.log (record : Record) (name : String) : IO Unit := do
  record.events.modify (· ++ [name])
  if record.faultAt == name then throw (IO.userError s!"injected {name}")

/-- Protocol errors stay in the host's error channel. -/
def Record.step (record : Record) (name : String) : ExceptT HostError Conc.Async Unit := do
  record.log name
  if record.failAt == name then throw (.upgrade (.protocol name))

/-- Captured output is recorded before a deliberate write failure. -/
def Record.print (record : Record) (text : String) : IO Unit := do
  record.log "stdout"
  record.output.modify (· ++ [text])

/-- Diagnostics stay separate from stdout. -/
def Record.printError (record : Record) (text : String) : IO Unit :=
  record.errors.modify (· ++ [text])

/-- A stream records reset independently of its exchange result. -/
def testStream (record : Record) (name : String) : Streams.Stream :=
  { read := pure (.ok none)
    write := fun _ => pure (.ok ())
    close := record.log s!"half-close:{name}"
    reset := record.log s!"reset:{name}" }

/-- A deterministic host exposes the same ownership operations the executable uses. -/
def testHost (record : Record) (index : Nat) : Host :=
  { id := ⟨s!"peer-{index}"⟩
    startListening := fun _ => do
      record.step "listen"
      return ⟨"/ip4/127.0.0.1/tcp/45001", [⟨.other, []⟩]⟩
    addAddrs := fun _ _ => record.log "peerstore"
    dial := fun _ expected => do
      record.step "dial"
      if expected.isSome then throw (.upgrade (.protocol "CLI must let the host read the peer suffix"))
      return ⟨"remote-peer"⟩
    dialPeer := fun _ => record.step "dialPeer"
    newStreamTo := fun _ protocol => do
      let name := if protocol.toString == Ping.protocolId.toString then "ping"
        else if protocol.toString == Identify.protocolId.toString then "identify" else "echo"
      record.step s!"open:{name}"
      return testStream record name
    setHandler := fun _ => record.log "handler"
    close := record.log s!"close:{index}" }

/-- Counting allocations distinguishes a first-host failure from a second-host failure. -/
def newHost (record : Record) : ExceptT HostError Conc.Async Host := do
  let index ← record.allocations.modifyGet fun n => (n + 1, n + 1)
  record.step s!"new:{index}"
  return testHost record index

/-- A successful test payload is explicit test data, never a production fallback. -/
def pingPayload (record : Record) : ExceptT HostError Conc.Async ByteArray := do
  record.step "random"
  return Bytes.ofNatList (List.replicate 32 42)

/-- The test client checks that the workflow passed its generated payload. -/
def ping (record : Record) (_stream : Streams.Stream) (payload : ByteArray) :
    ExceptT HostError Conc.Async Nat := do
  record.step "ping"
  if payload.size != 32 then throw (.upgrade (.protocol "wrong payload"))
  return 7

/-- The server waits through a test value rather than reading the runner's stdin. -/
def pingRuntime (record : Record) : CliApp.PingNode.Runtime :=
  { newHost := newHost record
    randomPing := pingPayload record
    ping := ping record
    waitInput := record.log "stdin.eof"
    stdout := record.print
    flush := record.log "flush"
    stderr := record.printError }

/-- The demo's protocol results come from explicitly injected test clients. -/
def demoRuntime (record : Record) : CliApp.Demo.Runtime :=
  { newHost := newHost record
    randomPing := pingPayload record
    ping := ping record
    identify := fun _ peer => do
      record.step "identify"
      return ⟨peer, 1, 3⟩
    echo := fun _ payload => do
      record.step "echo"
      return payload
    stdout := record.print
    stderr := record.printError }

/-- Count exact ownership events, including repeated closes. -/
def count (events : List String) (name : String) : Nat :=
  (events.filter (· == name)).length

/-- Invalid commands fail before host creation, even when the dependency could succeed. -/
def argumentChecks (runner : Runner) : IO Unit := do
  for args in [[], ["serve"], ["dial"], ["wat"], ["serve", "-1"],
      ["serve", "65536"], ["serve", "12x"], ["serve", "1_000"],
      ["serve", "١٢"], ["serve", "80", "extra"], ["dial", ""],
      ["dial", "tcp/80"], ["dial", "/ip4/127.0.0.1/tcp/80"],
      ["dial", "/unix/tmp/p2p/id"], ["dial", "/p2p/id", "extra"], ["--wat"]] do
    let record ← Record.new
    let code ← CliApp.PingNode.runWith (pingRuntime record) args
    runner.check s!"invalid pingnode arguments: {args}" (code == 2)
    runner.check "usage errors allocate no host" ((← record.allocations.get) == 0)
  for args in [["--help"], ["serve", "--help"], ["dial", "--help"]] do
    let record ← Record.new
    let code ← CliApp.PingNode.runWith (pingRuntime record) args
    runner.check "pingnode help succeeds without networking" (code == 0 && (← record.allocations.get) == 0)
  for text in ["0", "65535", "00080"] do
    runner.check "decimal port boundary accepted" ((CliApp.PingNode.parsePort? text).isSome)
  let help ← Record.new
  runner.check "demo help creates no hosts"
    ((← CliApp.Demo.runWith (demoRuntime help) ["--help"]) == 0 && (← help.allocations.get) == 0)
  let invalid ← Record.new
  runner.check "demo rejects extra arguments before creating hosts"
    ((← CliApp.Demo.runWith (demoRuntime invalid) ["extra"]) == 2 && (← invalid.allocations.get) == 0)

/-- Readiness is an exact stdout line, flushed before the stdin wait. -/
def serveChecks (runner : Runner) : IO Unit := do
  let record ← Record.new
  let code ← CliApp.PingNode.runWith (pingRuntime record) ["serve", "0"]
  runner.check "serve succeeds with its injected host" (code == 0)
  runner.check "serve prints the actual bound address, not port zero"
    ((← record.output.get) == ["ADDR /ip4/127.0.0.1/tcp/45001 peer-1"])
  runner.check "serve flushes readiness before waiting and closes after EOF"
    ((← record.events.get) == ["new:1", "handler", "listen", "stdout", "flush", "stdin.eof", "close:1"])
  for name in ["new:1", "listen"] do
    let record ← Record.new name
    runner.check s!"serve reports {name} failure"
      ((← CliApp.PingNode.runWith (pingRuntime record) ["serve", "80"]) == 1)
    runner.check "serve closes only a successfully created host"
      (count (← record.events.get) "close:1" == if name == "new:1" then 0 else 1)
  for name in ["handler", "listen", "stdout", "flush", "stdin.eof"] do
    let record ← Record.new (faultAt := name)
    runner.check s!"serve handles IO fault at {name}"
      ((← CliApp.PingNode.runWith (pingRuntime record) ["serve", "80"]) == 1)
    runner.check "serve closes after an IO fault" (count (← record.events.get) "close:1" == 1)

/-- Client errors and IO faults both retire the stream and its host. -/
def dialChecks (runner : Runner) : IO Unit := do
  let args := ["dial", "/ip4/127.0.0.1/tcp/80/p2p/remote"]
  let record ← Record.new
  runner.check "dial succeeds with its injected client"
    ((← CliApp.PingNode.runWith (pingRuntime record) args) == 0)
  runner.check "dial prints the CLI contract" ((← record.output.get) == ["PING OK rtt=7ms"])
  runner.check "dial owns the stream and host through completion"
    ((← record.events.get) == ["new:1", "dial", "open:ping", "random", "ping", "stdout", "reset:ping", "close:1"])
  for name in ["new:1", "dial", "open:ping", "random", "ping"] do
    let record ← Record.new name
    runner.check s!"dial reports {name} failure"
      ((← CliApp.PingNode.runWith (pingRuntime record) args) == 1)
    let events ← record.events.get
    runner.check "dial closes exactly its successfully allocated resources"
      (count events "close:1" == (if name == "new:1" then 0 else 1) &&
        count events "reset:ping" == (if name == "random" || name == "ping" then 1 else 0))
  for name in ["dial", "random", "ping", "stdout", "reset:ping"] do
    let record ← Record.new (faultAt := name)
    runner.check s!"dial handles IO fault at {name}"
      ((← CliApp.PingNode.runWith (pingRuntime record) args) == 1)
    runner.check "dial closes the host after a client fault"
      (count (← record.events.get) "close:1" == 1)

/-- The first host remains owned when any later step fails. -/
def demoChecks (runner : Runner) : IO Unit := do
  let record ← Record.new
  runner.check "demo composes its injected protocol clients"
    ((← CliApp.Demo.runWith (demoRuntime record) []) == 0)
  runner.check "demo reports every exchange"
    ((← record.output.get) == ["dialed peer-1 (noise + yamux, remote verified)",
      "ping rtt: 7 ms", "identified: peer-1, 1 addr(s), 3 protocol(s)", "echo: echo-me"])
  let events ← record.events.get
  runner.check "demo closes the dialer before the listener"
    ((events.reverse.take 2).reverse == ["close:2", "close:1"])
  for name in ["new:1", "new:2", "listen", "dialPeer", "open:ping", "random",
      "ping", "open:identify", "identify", "open:echo", "echo"] do
    let record ← Record.new name
    runner.check s!"demo reports {name} failure"
      ((← CliApp.Demo.runWith (demoRuntime record) []) == 1)
    let events ← record.events.get
    runner.check "demo closes every successfully created host exactly once"
      (count events "close:1" == (if name == "new:1" then 0 else 1) &&
        count events "close:2" == (if name == "new:1" || name == "new:2" then 0 else 1))
  for name in ["stdout", "peerstore", "identify", "echo", "close:2"] do
    let record ← Record.new (faultAt := name)
    runner.check s!"demo handles IO fault at {name}"
      ((← CliApp.Demo.runWith (demoRuntime record) []) == 1)
    runner.check "listener cleanup survives a later IO fault"
      (count (← record.events.get) "close:1" == 1)

/-- Composition preserves the intended order, without a second muxer or extension shortcut. -/
def compositionChecks (runner : Runner) : IO Unit := do
  let key : PrivKey := ⟨Bytes.ofNatList (List.replicate 32 0)⟩
  let raw := Bytes.ofNatList (List.replicate 32 0)
  let static : Key32 := ⟨raw, by simp [raw, Bytes.ofNatList, ByteArray.size]⟩
  let demo := CliApp.Demo.hostConfig key static
  let ping := CliApp.PingNode.hostConfig key static
  for config in [demo, ping] do
    runner.check "one configured TCP transport" (config.transports.length == 1)
    runner.check "Noise is the configured security protocol"
      (config.securities.map (·.id.toString) == ["/noise"])
    runner.check "yamux is the configured muxer"
      (config.muxers.map (·.id.toString) == ["/yamux/1.0.0"])
  runner.check "the demo registers its protocol handlers"
    (demo.handlers.map (·.id.toString) == [Ping.protocolId.toString, Echo.protocolId.toString])
  let record ← Record.new
  let runtime : CliApp.PingNode.Runtime := { stdout := record.print, stderr := record.printError }
  runner.check "default dependencies fail instead of claiming network success"
    ((← CliApp.PingNode.runWith runtime ["serve", "0"]) == 1 && (← record.output.get).isEmpty)

/-- Mock-backed workflow checks are labeled separately from live networking. -/
def run (runner : Runner) : IO Unit := do
  runner.section "CLI orchestration (dependency test values)" "packages/cli/docs/PLAN.md, W5.8"
  argumentChecks runner
  serveChecks runner
  dialChecks runner
  demoChecks runner
  compositionChecks runner
  runner.skip "CLI live loopback gate" "host, Noise, muxer and protocol implementations are unmerged"
  runner.skip "CLI live Go ping gate" "requires the real stack; workflow test values are not interop evidence"

end Tests.Cli
