import Conc
import Tests.Support

/-!
# Demo and pingnode arguments

The checks run the built binaries. A usage error exits 2 with an
empty stdout. A dial to port 0 is an immediate local failure.
`capture` bounds it at 10 seconds. The child exits inside that
deadline with code 1, empty stdout, and a nonempty stderr.
`pingnode serve` with a valid port listens.
-/

set_option autoImplicit false

namespace Tests.Cli

/-- An Ed25519 peer id from the identity suite. -/
private def peer : String :=
  "12D3KooWD3eckifWpRn9wQpMG9R9hX3sD158z7EqHWmweQAJU5SA"

/-- The single stdout line, when the process wrote exactly one. -/
private def oneStdout (stdout : String) : Option String :=
  if stdout.endsWith "\n" && !((stdout.dropEnd 1).any (· == '\n')) then
    some (stdout.dropEnd 1).copy
  else none

/-- The port text of a loopback TCP address. -/
private def boundPort (addr : String) : Option String :=
  let head := "/ip4/127.0.0.1/tcp/"
  if addr.startsWith head then some (addr.drop head.length).copy else none

/-- A kernel-assigned port: digits, no leading zero, and at most 65535. -/
private def realPort (text : String) : Bool :=
  text != "0" && text.all Char.isDigit && text.front?.any (· != '0') &&
    match text.toNat? with
    | some n => n ≤ 65535
    | none => false

/-- Pause the caller. -/
def pause (ms : Nat) : IO Unit := do
  let park ← Conc.Park.sleep ms ()
  Conc.Async.run (Conc.select #[park] : Conc.Async Unit)

/-- Kill a child that is still running, then reap it. A second call
meets a process that is already gone. -/
def reap {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) : IO Unit := do
  try
    match ← child.tryWait with
    | some _ => pure ()
    | none =>
      child.kill
      discard child.wait
  catch _ => pure ()

/-- Wait for the child. At the deadline, kill it and reap it. -/
def waitChild {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg)
    (ms : Nat) : IO (UInt32 × Bool) := do
  let start ← IO.monoMsNow
  repeat
    match ← child.tryWait with
    | some code => return (code, false)
    | none =>
      if (← IO.monoMsNow) - start ≥ ms then
        child.kill
        return (← child.wait, true)
      pause 20

/-- The captured output of one bounded run. -/
structure Captured where
  exitCode : UInt32
  stdout : String
  stderr : String
  timedOut : Bool

/-- Run `cmd` until it exits or `ms` passes. The deadline kills the
child, which closes the pipes and wakes the readers. This function
then joins both readers. -/
def capture (cmd : String) (args : Array String) (ms : Nat)
    (env : Array (String × Option String) := #[]) : IO Captured := do
  let child ← IO.Process.spawn {
    cmd
    args
    env
    stdin := .null
    stdout := .piped
    stderr := .piped
  }
  let mut outTask : Option (Task (Except IO.Error String)) := none
  let mut errTask : Option (Task (Except IO.Error String)) := none
  let mut code : UInt32 := 0
  let mut timedOut := false
  let mut fault : Option IO.Error := none
  try
    outTask := some (← IO.asTask child.stdout.readToEnd Task.Priority.dedicated)
    errTask := some (← IO.asTask child.stderr.readToEnd Task.Priority.dedicated)
    let waited ← waitChild child ms
    code := waited.1
    timedOut := waited.2
  catch e =>
    fault := some e
  -- The kill closes both pipes, so a reader that exists can finish.
  reap child
  let mut stdout := ""
  let mut stderr := ""
  if let some task := outTask then
    try
      stdout ← IO.ofExcept (← IO.wait task)
    catch e =>
      if fault.isNone then fault := some e
  if let some task := errTask then
    try
      stderr ← IO.ofExcept (← IO.wait task)
    catch e =>
      if fault.isNone then fault := some e
  if let some e := fault then throw e
  return { exitCode := code, stdout, stderr, timedOut }

/-- `serve` with a valid port. Port 0 must bind. Another port may be
busy or unprivileged, and then the process exits 1 with empty stdout.
The process has 10 s. A miss kills it and joins its readers. -/
private def expectServe (runner : Runner) (name port : String) (requireBind : Bool) :
    IO Unit := do
  let out ← capture ".lake/build/bin/pingnode" #["serve", port] 10000
  if out.timedOut then
    runner.check s!"{name}: exited within 10 s" false
    return
  if out.exitCode == 0 then
    match oneStdout out.stdout with
    | some line =>
      match line.splitOn " " with
      | ["ADDR", addr, peer] =>
        match boundPort addr with
        | some got =>
          let portOk := if port == "0" then realPort got else got == port
          runner.check s!"{name}: bound address" (out.stderr == "" && peer != "" && portOk)
        | none => runner.check s!"{name}: loopback address" false
      | _ => runner.check s!"{name}: ADDR fields" false
    | none => runner.check s!"{name}: one stdout line" false
  else if requireBind then
    runner.check s!"{name}: exit 0, got {out.exitCode}, stderr {out.stderr}" false
  else
    runner.check s!"{name}: runtime exit" (out.exitCode == 1)
    runner.check s!"{name}: stdout empty" (out.stdout == "")
    runner.check s!"{name}: runtime stderr"
      (out.stderr != "" && !out.stderr.startsWith "invalid port:")

/-- A dial that passes validation and then fails before a ping.
The deadline bounds an immediate local failure. The child must exit
inside it, with code 1, empty stdout, and a nonempty stderr. -/
private def expectDialFail (runner : Runner) (name : String) (args : Array String) :
    IO Unit := do
  let out ← capture ".lake/build/bin/pingnode" args 10000
  runner.check s!"{name}: bounded" !out.timedOut
  runner.check s!"{name}: exit 1" (out.exitCode == 1)
  runner.check s!"{name}: stdout empty" (out.stdout == "")
  runner.check s!"{name}: runtime stderr" (out.stderr != "")

/-- Run one built executable and compare its exit, stdout, and stderr. -/
private def expect (runner : Runner) (name exe : String) (args : Array String)
    (code : UInt32) (stderr : String) : IO Unit := do
  let out ← IO.Process.output { cmd := s!".lake/build/bin/{exe}", args }
  runner.check s!"{name}: exit {code}" (out.exitCode == code)
  runner.check s!"{name}: stdout empty" (out.stdout == "")
  runner.check s!"{name}: stderr" (out.stderr == stderr ++ "\n")

/-- The argument table of the demo and the ping node. -/
def run (runner : Runner) : IO Unit := do
  runner.section "cli arguments" "packages/cli/Demo.lean, packages/cli/PingNode.lean"
  expect runner "demo one argument" "demo" #["foo"] 2
    "Redundant positional argument `foo`."
  expect runner "demo two arguments" "demo" #["foo", "bar"] 2
    "Redundant positional argument `foo`."
  expect runner "demo help" "demo" #["--help"] 2 "Unknown flag `--help`."
  expect runner "demo short help" "demo" #["-h"] 2 "Unknown flag `-h`."
  expect runner "demo version" "demo" #["--version"] 2 "Unknown flag `--version`."
  expect runner "demo end of flags" "demo" #["--"] 2 "unexpected argument: --"
  expect runner "pingnode missing subcommand" "pingnode" #[] 2 "missing subcommand"
  expect runner "pingnode unknown subcommand" "pingnode" #["foo"] 2
    "Redundant positional argument `foo`."
  expect runner "pingnode help" "pingnode" #["--help"] 2 "Unknown flag `--help`."
  expect runner "pingnode serve missing port" "pingnode" #["serve"] 2
    "Missing positional argument `<port>.`"
  expectServe runner "pingnode serve 0" "0" true
  expectServe runner "pingnode serve 1" "1" false
  expectServe runner "pingnode serve 65535" "65535" false
  expect runner "pingnode serve 65536" "pingnode" #["serve", "65536"] 2
    "invalid port: 65536"
  expect runner "pingnode serve 00" "pingnode" #["serve", "00"] 2 "invalid port: 00"
  expect runner "pingnode serve 01" "pingnode" #["serve", "01"] 2 "invalid port: 01"
  expect runner "pingnode serve sign" "pingnode" #["serve", "-1"] 2 "Unknown flag `-1`."
  expect runner "pingnode serve plus" "pingnode" #["serve", "+1"] 2 "invalid port: +1"
  expect runner "pingnode serve leading space" "pingnode" #["serve", " 1"] 2
    "invalid port:  1"
  expect runner "pingnode serve trailing space" "pingnode" #["serve", "1 "] 2
    "invalid port: 1 "
  expect runner "pingnode serve nondigit" "pingnode" #["serve", "1a"] 2
    "invalid port: 1a"
  expect runner "pingnode serve extra" "pingnode" #["serve", "1", "extra"] 2
    "Redundant positional argument `extra`."
  let dial := s!"/ip4/127.0.0.1/tcp/4001/p2p/{peer}"
  expect runner "pingnode dial missing address" "pingnode" #["dial"] 2
    "Missing positional argument `<multiaddr>.`"
  -- Port 0 fails in the kernel before a listener is required. The
  -- capture bound is 10 seconds. A refused port that the suite binds
  -- itself lives in `Tests/CliLive.lean`.
  expectDialFail runner "pingnode dial port 0" #[ "dial", s!"/ip4/127.0.0.1/tcp/0/p2p/{peer}" ]
  expect runner "pingnode dial extra" "pingnode" #[ "dial", dial, "extra" ] 2
    "Redundant positional argument `extra`."
  expect runner "pingnode dial parse" "pingnode" #["dial", "not-an-addr"] 2
    "Multiformats.Error.badAddress not-an-addr"
  expect runner "pingnode dial bare peer component" "pingnode" #["dial", "/p2p"] 2
    "Multiformats.Error.badValue /p2p"
  expect runner "pingnode dial no peer" "pingnode" #["dial", "/ip4/127.0.0.1/tcp/4001"] 2
    "dial address has no final /p2p peer: /ip4/127.0.0.1/tcp/4001"
  expect runner "pingnode dial peer only" "pingnode" #[ "dial", s!"/p2p/{peer}" ] 2
    s!"no transport handles /p2p/{peer} /p2p/{peer}"
  expect runner "pingnode dial peer not final" "pingnode"
    #[ "dial", s!"/ip4/127.0.0.1/p2p/{peer}/tcp/4001" ] 2
    s!"dial address has no final /p2p peer: /ip4/127.0.0.1/p2p/{peer}/tcp/4001"
  expect runner "pingnode dial repeated peer" "pingnode"
    #[ "dial", s!"/ip4/127.0.0.1/tcp/4001/p2p/{peer}/p2p/{peer}" ] 2
    s!"dial address has an earlier /p2p peer: /ip4/127.0.0.1/tcp/4001/p2p/{peer}/p2p/{peer}"
  expect runner "pingnode dial earlier peer" "pingnode"
    #[ "dial", s!"/ip4/127.0.0.1/p2p/{peer}/tcp/4001/p2p/{peer}" ] 2
    s!"dial address has an earlier /p2p peer: /ip4/127.0.0.1/p2p/{peer}/tcp/4001/p2p/{peer}"
  expect runner "pingnode serve newline" "pingnode" #["serve", "1\n"] 2
    "invalid port: 1\\n"
  expect runner "pingnode dial newline" "pingnode" #["dial", "not-an-addr\n"] 2
    "Multiformats.Error.badAddress not-an-addr\\n"

end Tests.Cli
