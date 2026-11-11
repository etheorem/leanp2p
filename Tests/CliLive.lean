import Conc
import Crypto
import Streams
import Multiformats
import Libp2p.Identity
import Libp2p.Security
import Libp2p.Mux
import Libp2p.Host
import Libp2p.Protocols.Ping
import Libp2p.Protocols.Identify
import Tests.Cli
import Tests.Support

/-!
# The pingnode server

The checks run the built `pingnode` with `LEAN_NUM_THREADS=1`. One
client host dials it over TCP and Noise while stdin stays open. The
other checks cover EOF, a busy port, a failed `ADDR` write, an inbound
failure, a deadline that kills a sleeper, and a registered task that
returns an error.

Each reader task belongs to the check that started it. The check wakes
the task by closing the pipe it reads, and then joins it.
-/

set_option autoImplicit false

namespace Tests.CliLive

open Libp2p.Host (Host)
open Libp2p.Identity (PeerId PrivKey)

/-- The built server. -/
private def bin : String := ".lake/build/bin/pingnode"

/-- One worker in the server process. -/
private def oneWorker : Array (String × Option String) :=
  #[("LEAN_NUM_THREADS", some "1")]

/-- Drop the trailing line break from `getLine`. -/
private def stripNl (text : String) : String :=
  let text := if text.endsWith "\n" then (text.dropEnd 1).copy else text
  if text.endsWith "\r" then (text.dropEnd 1).copy else text

/-- The port text of a loopback TCP address. -/
private def portOf (addr : String) : Option String :=
  let head := "/ip4/127.0.0.1/tcp/"
  if addr.startsWith head then some (addr.drop head.length).copy else none

/-- Keep the first fault. -/
private def note (primary : IO.Ref (Option IO.Error)) (e : IO.Error) : IO Unit := do
  if (← primary.get).isNone then primary.set (some e)

/-- Read one stdout line. The task's owner is this function. A miss
kills `child`, which closes the pipe and wakes the read, and then this
function joins the task. -/
private def getLineWithin {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg)
    (h : IO.FS.Handle) (ms : Nat) : IO String := do
  let task ← IO.asTask h.getLine Task.Priority.dedicated
  let mut timedOut := false
  let mut fault : Option IO.Error := none
  try
    let start ← IO.monoMsNow
    repeat
      if ← IO.hasFinished task then
        break
      if (← IO.monoMsNow) - start ≥ ms then
        timedOut := true
        break
      Tests.Cli.pause 20
  catch e =>
    fault := some e
  if timedOut || fault.isSome then
    Tests.Cli.reap child
  let result ← IO.wait task
  if let some e := fault then throw e
  if timedOut then
    throw <| IO.userError s!"no stdout line within {ms} ms"
  IO.ofExcept result

/-- Append stderr lines until EOF. The caller owns the task and joins
it after the write end closes. -/
private def collectLines (h : IO.FS.Handle) (lines : IO.Ref (Array String)) : IO Unit := do
  repeat
    let line ← h.getLine
    if line.isEmpty then return
    lines.modify (·.push (stripNl line))

/-- A fresh client host with the same stack as `pingnode serve`. -/
private def clientHost : IO Host := do
  let seed ← match ← Crypto.ed25519Generate.run with
    | .error e => throw <| IO.userError (reprStr e)
    | .ok seed => pure seed
  let key ← match PrivKey.ofData? .ed25519 seed.bytes with
    | .error e => throw <| IO.userError (reprStr e)
    | .ok key => pure key
  let noise ← match ← (Libp2p.Security.Noise.Config.generate key).run with
    | .error e => throw <| IO.userError (reprStr e)
    | .ok noise => pure noise
  match ← (Host.new {
    identity := key
    transports := [Streams.Tcp.transport]
    security := [Libp2p.Security.Noise.securityProtocol noise]
    muxers := [Libp2p.Mux.yamux, Libp2p.Mux.mplex]
  } : BaseIO _) with
  | .error e => throw <| IO.userError (reprStr e)
  | .ok host => return host

/-- Dial `peer`, ping once, and read its identify record. `host.close`
finishes before this function returns, including when the exchange throws. -/
private def exchange (addr : Multiformats.Multiaddr) (peer : PeerId) : IO Unit := do
  let host ← clientHost
  let mut primary : Option IO.Error := none
  try
    Conc.Async.run do
      match ← host.dial addr (some peer) with
      | .error e => throw <| IO.userError s!"dial: {e.render}"
      | .ok got =>
        if got.hash != peer.hash then
          throw <| IO.userError "dial proved a different peer"
      let payload ← match ← (Crypto.randomBytes Libp2p.Protocols.Ping.payloadSize).run with
        | .error e => throw <| IO.userError (reprStr e)
        | .ok payload => pure payload
      match ← host.newStream peer [Libp2p.Protocols.Ping.protocolId] with
      | .error e => throw <| IO.userError s!"ping stream: {e.render}"
      | .ok (_, stream) =>
        match ← Libp2p.Protocols.Ping.ping stream Conc.Clock.system payload with
        | .error e =>
          stream.reset
          throw <| IO.userError s!"ping: {reprStr e}"
        | .ok none =>
          stream.reset
          throw <| IO.userError "ping returned none"
        | .ok (some _) => stream.close
      match ← host.newStream peer [Libp2p.Protocols.Identify.protocolId] with
      | .error e => throw <| IO.userError s!"identify stream: {e.render}"
      | .ok (_, stream) =>
        match ← Libp2p.Protocols.Identify.client stream Conc.Clock.system
            Streams.unauthDeadlineMs (some peer) with
        | .error e =>
          stream.reset
          throw <| IO.userError s!"identify: {reprStr e}"
        | .ok none =>
          stream.reset
          throw <| IO.userError "identify returned none"
        | .ok (some (msg, got)) =>
          stream.close
          if got.hash != peer.hash then
            throw <| IO.userError "identify peer differs"
          if msg.agentVersion != some "leanp2p" then
            throw <| IO.userError s!"agent {repr msg.agentVersion}"
          if !(msg.listenAddrs.any (· == addr.toBytes)) then
            throw <| IO.userError "identify omitted the bound address"
          let protocols := [
            Libp2p.Protocols.Ping.protocolId.toString,
            Libp2p.Protocols.Identify.protocolId.toString
          ]
          if msg.protocols != protocols then
            throw <| IO.userError s!"protocols {msg.protocols}"
  catch e =>
    primary := some e
  try
    Conc.Async.run host.close
  catch e =>
    if primary.isNone then primary := some e
  if let some e := primary then throw e

/-- Open a TCP connection and close it, so the server records one inbound failure. -/
private def disturb (addr : Multiformats.Multiaddr) : IO Unit := do
  match ← Conc.Async.run ((Streams.Tcp.transport).dial addr) with
  | none => throw <| IO.userError "disturb found no listener"
  | some conn => conn.close

/-- Run `act` on a task this function owns. A miss closes `stdin` and
kills `child`, which wakes the dial, and then this function joins the
task before it throws. -/
private def tracked {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg)
    (stdinRef : IO.Ref (Option IO.FS.Handle))
    (extra : IO.Ref (Array (Task (Except IO.Error Unit))))
    (act : IO Unit) (ms : Nat) : IO Unit := do
  let task ← IO.asTask act Task.Priority.dedicated
  extra.modify (·.push task)
  let mut timedOut := false
  let mut fault : Option IO.Error := none
  try
    let start ← IO.monoMsNow
    repeat
      if ← IO.hasFinished task then
        break
      if (← IO.monoMsNow) - start ≥ ms then
        timedOut := true
        break
      Tests.Cli.pause 20
  catch e =>
    fault := some e
  if timedOut || fault.isSome then
    stdinRef.set none
    Tests.Cli.reap child
  let result ← IO.wait task
  if let some e := fault then throw e
  if timedOut then
    throw <| IO.userError s!"exchange missed {ms} ms"
  IO.ofExcept result

/-- The server after `ADDR` is visible. `stdin` is the last owner of
the pipe. `lines` fills from the stderr task. -/
private structure Session where
  child : IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }
  stdin : IO.Ref (Option IO.FS.Handle)
  lines : IO.Ref (Array String)
  extra : IO.Ref (Array (Task (Except IO.Error Unit)))
  addr : Multiformats.Multiaddr
  peer : PeerId

/-- Spawn `pingnode serve 0`, read `ADDR`, run `k`, then drop stdin,
reap the child, and join every task `k` registered. The child dying
wakes those tasks. `IO.wait` returns `Except`, so a `.error` is
recorded here. The first fault is the one that propagates, and the
throw follows the joins. -/
private def withSession (k : Session → IO Unit) : IO Unit := do
  let primary ← IO.mkRef (none : Option IO.Error)
  let stdinRef ← IO.mkRef (none : Option IO.FS.Handle)
  let lines ← IO.mkRef (#[] : Array String)
  let extra ← IO.mkRef (#[] : Array (Task (Except IO.Error Unit)))
  let child ← do
    let (stdin, child) ← (← IO.Process.spawn {
      cmd := bin
      args := #["serve", "0"]
      stdin := .piped
      stdout := .piped
      stderr := .piped
      env := oneWorker
    }).takeStdin
    stdinRef.set (some stdin)
    pure child
  try
    let errTask ← IO.asTask (collectLines child.stderr lines) Task.Priority.dedicated
    extra.modify (·.push errTask)
    let line ← getLineWithin child child.stdout 10000
    let (addrText, peerText) ← match (stripNl line).splitOn " " with
      | ["ADDR", addrText, peerText] => pure (addrText, peerText)
      | _ => throw <| IO.userError s!"bad ADDR line: {line}"
    let some port := portOf addrText | throw <| IO.userError s!"address {addrText}"
    if port == "0" || !port.all Char.isDigit then
      throw <| IO.userError s!"bound port {port}"
    let addr ← match Multiformats.Multiaddr.parse? addrText with
      | .ok addr => pure addr
      | .error e => throw <| IO.userError (reprStr e)
    let peer ← match PeerId.ofString? peerText with
      | .ok peer => pure peer
      | .error e => throw <| IO.userError (reprStr e)
    k { child, stdin := stdinRef, lines, extra, addr, peer }
  catch e =>
    note primary e
  stdinRef.set none
  Tests.Cli.reap child
  for task in ← extra.get do
    try
      match ← IO.wait task with
      | .ok () => pure ()
      | .error e => note primary e
    catch e =>
      note primary e
  if let some e ← primary.get then throw e

/-- `serve 0` accepts a ping and an identify while stdin stays open. -/
private def live (runner : Runner) : IO Unit := do
  withSession fun session => do
    let some input ← session.stdin.get | throw <| IO.userError "stdin is already closed"
    input.putStr "hello\n"
    input.flush
    tracked session.child session.stdin session.extra
      (exchange session.addr session.peer) 20000
    session.stdin.set none
    let (code, killed) ← Tests.Cli.waitChild session.child 10000
    let rest ← session.child.stdout.readToEnd
    -- Join the stderr reader after the process is gone, so the list
    -- holds every line it wrote. The checks below run only after
    -- every joined result is `.ok`.
    let mut fault : Option IO.Error := none
    for task in ← session.extra.get do
      try
        match ← IO.wait task with
        | .ok () => pure ()
        | .error e =>
          if fault.isNone then fault := some e
      catch e =>
        if fault.isNone then fault := some e
    if let some e := fault then throw e
    let lines ← session.lines.get
    runner.check "serve live exit" (code == 0 && !killed)
    runner.check "serve live stderr" (lines == #[])
    runner.check "serve live no extra stdout" (rest == "")

/-- One inbound failure, then a successful exchange on the same server. -/
private def inboundThenServe (runner : Runner) : IO Unit := do
  withSession fun session => do
    disturb session.addr
    let start ← IO.monoMsNow
    let mut seen : Option String := none
    repeat
      let got ← session.lines.get
      match got[0]? with
      | some text =>
        seen := some text
        break
      | none =>
        if (← IO.monoMsNow) - start ≥ 5000 then
          throw <| IO.userError "no inbound failure line"
        Tests.Cli.pause 20
    let some line := seen | throw <| IO.userError "no inbound failure line"
    runner.check "serve inbound failure" (line.startsWith "upgrade failed:")
    tracked session.child session.stdin session.extra
      (exchange session.addr session.peer) 20000
    session.stdin.set none
    let (code, killed) ← Tests.Cli.waitChild session.child 10000
    runner.check "serve continues after failure" (code == 0 && !killed)

/-- Immediate EOF still prints `ADDR` and exits 0. -/
private def immediateEof (runner : Runner) : IO Unit := do
  let out ← Tests.Cli.capture bin #["serve", "0"] 10000 oneWorker
  if out.timedOut then
    runner.check "serve immediate EOF exited" false
    return
  let line := stripNl out.stdout
  let ok := match line.splitOn " " with
    | ["ADDR", addr, peer] =>
      match portOf addr with
      | some port => port != "0" && port.all Char.isDigit && peer != ""
      | none => false
    | _ => false
  runner.check "serve immediate EOF" (out.exitCode == 0 && out.stderr == "" &&
    out.stdout.endsWith "\n" && ok)

/-- A port that is already bound exits 1 with no `ADDR` line. -/
private def busyPort (runner : Runner) : IO Unit := do
  let want ← match Multiformats.Multiaddr.parse? "/ip4/127.0.0.1/tcp/0" with
    | .ok addr => pure addr
    | .error e => throw <| IO.userError (reprStr e)
  let listener ← Conc.Async.run ((Streams.Tcp.transport).listen want)
  try
    let some port := portOf listener.addr.toString
      | throw <| IO.userError s!"listener {listener.addr}"
    let out ← Tests.Cli.capture bin #["serve", port] 10000 oneWorker
    if out.timedOut then
      runner.check "serve busy exited" false
      return
    runner.check "serve busy exit" (out.exitCode == 1)
    runner.check "serve busy stdout" (out.stdout == "")
    runner.check "serve busy stderr"
      (out.stderr != "" && (out.stderr.splitOn "ADDR").length == 1)
  finally
    listener.close
    Conc.Async.run listener.join

/-- A closed stdout fails the `ADDR` write, and the process still exits.
The stderr reader is joined after the child is reaped, which wakes it. -/
private def closedStdout (runner : Runner) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := "/bin/sh"
    args := #["-c", "exec \"$1\" serve 0 >&-", "sh", bin]
    stdin := .null
    stdout := .null
    stderr := .piped
    env := oneWorker
  }
  let mut errTask : Option (Task (Except IO.Error String)) := none
  let mut code : Option UInt32 := none
  let mut fault : Option IO.Error := none
  try
    errTask := some (← IO.asTask child.stderr.readToEnd Task.Priority.dedicated)
    let (got, killed) ← Tests.Cli.waitChild child 10000
    code := if killed then none else some got
  catch e =>
    fault := some e
  Tests.Cli.reap child
  let err ← match errTask with
    | none => pure ""
    | some task =>
      try
        IO.ofExcept (← IO.wait task)
      catch e =>
        if fault.isNone then fault := some e
        pure ""
  if let some e := fault then
    runner.check s!"serve closed stdout: {e}" false
    return
  runner.check "serve closed stdout exits" (code == some 1)
  runner.check "serve closed stdout stderr" (err != "")

/-- A registered task returns an error. Cleanup still reaps the child
and joins the later task, and the error is the one that surfaces. -/
private def registeredFault (runner : Runner) : IO Unit := do
  let followed ← IO.mkRef false
  let pid ← IO.mkRef (0 : UInt32)
  let mut caught : Option String := none
  try
    withSession fun session => do
      pid.set session.child.pid
      let failed ← IO.asTask (throw <| IO.userError "registered task failed")
        Task.Priority.dedicated
      session.extra.modify (·.push failed)
      -- This read parks on stdout. The reap closes that pipe, and the
      -- join is what waits for the flag.
      let later ← IO.asTask (do
        discard <| session.child.stdout.readToEnd
        followed.set true) Task.Priority.dedicated
      session.extra.modify (·.push later)
  catch e =>
    caught := some (toString e)
  let id ← pid.get
  let probe ← Tests.Cli.capture "/bin/kill" #["-0", toString id] 1000
  runner.check "registered task observed" (caught == some "registered task failed")
  runner.check "registered sibling joined" (← followed.get)
  runner.check "registered child reaped" (id != 0 && !probe.timedOut && probe.exitCode != 0)

/-- A sleeper that ignores its deadline is killed, reaped, and its
readers are joined by `capture`. -/
private def timeoutCleanup (runner : Runner) : IO Unit := do
  let start ← IO.monoMsNow
  let out ← Tests.Cli.capture "/bin/sleep" #["30"] 500
  let elapsed := (← IO.monoMsNow) - start
  runner.check "timeout cleanup reaped" out.timedOut
  runner.check "timeout cleanup bounded" (elapsed < 5000)
  runner.check "timeout cleanup readers" (out.stdout == "" && out.stderr == "")

/-- The server checks. -/
def run (runner : Runner) : IO Unit := do
  runner.section "pingnode serve" "packages/cli/PingNode.lean"
  live runner
  inboundThenServe runner
  immediateEof runner
  busyPort runner
  closedStdout runner
  timeoutCleanup runner
  registeredFault runner

end Tests.CliLive
