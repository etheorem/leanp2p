import Cli
import Conc
import Crypto
import Streams
import Bytes
import Multiformats
import Libp2p.Core
import Libp2p.Identity
import Libp2p.Security
import Libp2p.Mux
import Libp2p.Host
import Libp2p.Protocols.Ping
import Libp2p.Protocols.Identify
import Libp2p.Protocols.TestSupport.Echo

/-!
# Demo

The `demo` executable. `Cmd.parse` checks the argument list. `Cmd.mk`
would add help and version flags, so this command is built with
`Cmd.init` and an empty flag list. A usage error exits 2, before any
host exists. A line break in an argument is escaped in the usage
line.

An empty argument list builds two hosts. The listener serves ping,
`/demo/echo/1.0.0`, and identify. The dialer stores the bound address,
dials with `dialPeer`, and runs ping, identify, and echo. The dialer
closes first. A fault from that close still closes the listener.
-/

set_option autoImplicit false

namespace Cli.Demo

open Cli
open Libp2p.Host (Host Error Failure)
open Libp2p.Identity (PeerId PrivKey)

/-- The command carries no flags and no operands. -/
private def command : Cmd :=
  .init {
    name := "demo"
    parentNames := #[]
    version? := none
    description := "Run the loopback demo."
    flags := #[]
    positionalArgs := #[]
    variableArg? := none
  } (fun _ => pure 0) #[] none

/-- Replace a newline with `\n` and a carriage return with `\r`. -/
private def oneLine (text : String) : String :=
  (text.replace "\r" "\\r").replace "\n" "\\n"

/-- Print one usage line and exit 2. -/
private def usage (line : String) : IO UInt32 := do
  IO.eprintln (oneLine line)
  return 2

/-- The agent string identify advertises. -/
private def agent : String := "leanp2p"

/-- The bytes the demo writes on the echo stream. -/
private def echoPayload : ByteArray := Bytes.ofString "echo-me"

/-- The protocol ids the listener serves, in registration order. -/
private def registered : List String := [
  Libp2p.Protocols.Ping.protocolId.toString,
  Libp2p.Protocols.TestSupport.Echo.protocolId.toString,
  Libp2p.Protocols.Identify.protocolId.toString
]

/-- The command budget around `Host.newStream`, ping, and echo.
Identify takes the same duration as its own client timeout. The home
of the duration is `Streams.unauthDeadlineMs`. -/
private def commandBudget : Nat := Streams.unauthDeadlineMs

/-- The stderr line for one inbound failure. -/
private def failureLine (f : Failure) : String := Id.run do
  let mut line := f.error.render
  if let some peer := f.peer then
    line := s!"{line} peer {peer}"
  if let some protocol := f.protocol then
    line := s!"{line} protocol {protocol}"
  return line

/-- The callback record for both hosts. `reported` is set when
`onFailure` runs, including a write that succeeds. `writeFault` is a
thrown diagnostic write. The command does not turn a `Host.Error`
into an `IO.Error`. -/
private structure CallbackState where
  reported : Bool
  writeFault : Option IO.Error

/-- No callback has run. -/
private def emptyCallback : CallbackState :=
  { reported := false, writeFault := none }

/-- The status after both closes. A nonzero code stays a failure. A
reported callback and a stored write fault each force 1. -/
private def exitAfterCleanup (code : UInt32) (state : CallbackState) : UInt32 :=
  if code != 0 || state.reported || state.writeFault.isSome then 1 else 0

example : exitAfterCleanup 0 { reported := true, writeFault := none } = 1 := rfl

example : exitAfterCleanup 0
    { reported := false, writeFault := some (IO.userError "diag") } = 1 := rfl

example : exitAfterCleanup 0
    { reported := true, writeFault := some (IO.userError "diag") } = 1 := rfl

example : exitAfterCleanup 1 emptyCallback = 1 := rfl

example : exitAfterCleanup 0 emptyCallback = 0 := rfl

/-- Keep the first diagnostic write that threw. `modify` holds the cell
for the whole update, so the first stored fault stays. The reported
flag is left as it is. -/
private def keepFault (faults : IO.Ref CallbackState) (e : IO.Error) : BaseIO Unit :=
  faults.modify fun old =>
    if old.writeFault.isNone then { old with writeFault := some e } else old

/-- Record the callback, then write its line. The flag is set before
the write, so a successful write still leaves `reported`. A thrown
write stays in `writeFault`. `Host.close` joins this task. -/
private def reportFailure (faults : IO.Ref CallbackState) (f : Failure) : BaseIO Unit := do
  faults.modify fun old => { old with reported := true }
  EIO.catchExceptions (IO.eprintln (failureLine f)) (keepFault faults)

/-- A fresh Ed25519 host: TCP, Noise, yamux, then mplex. `handlers`
are the protocols the host serves at `Host.new`. -/
private def openHost (faults : IO.Ref CallbackState)
    (handlers : List Libp2p.Core.StreamHandler) : IO (Except String Host) := do
  let seed ← match ← Crypto.ed25519Generate.run with
    | .error e => return .error (reprStr e)
    | .ok seed => pure seed
  let key ← match PrivKey.ofData? .ed25519 seed.bytes with
    | .error e => return .error (reprStr e)
    | .ok key => pure key
  let noise ← match ← (Libp2p.Security.Noise.Config.generate key).run with
    | .error e => return .error (reprStr e)
    | .ok noise => pure noise
  match ← (Host.new {
    identity := key
    transports := [Streams.Tcp.transport]
    security := [Libp2p.Security.Noise.securityProtocol noise]
    muxers := [Libp2p.Mux.yamux, Libp2p.Mux.mplex]
    handlers
    onFailure := reportFailure faults
  } : BaseIO _) with
  | .error e => return .error (reprStr e)
  | .ok host => return .ok host

/-- Print one contract line and flush it. `IO.println` can keep the
bytes in the stdout buffer. A closed stdout then stays silent until
process exit. The flush makes that fault a thrown `IO.Error` inside
the command, which `guarding` records before it closes the hosts. -/
private def writeLine (line : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStr s!"{line}\n"
  out.flush

/-- Print `line` and exit 1. -/
private def failLine (line : String) : IO UInt32 := do
  IO.eprintln line
  return 1

/-- Print one host error and exit 1. -/
private def failHost (e : Error) : IO UInt32 :=
  failLine e.render

/-- Reset `stream`, and suppress a secondary reset error. -/
private def resetStream (stream : Streams.Stream) : IO Unit := do
  try Conc.Async.run stream.reset catch _ => pure ()

/-- Join `cleanup`. A fault of the join is kept when `primary` is empty. -/
private def joinCleanup (cleanup : Conc.TaskSet) (primary : Option IO.Error) :
    IO (Option IO.Error) := do
  try
    Conc.Async.run cleanup.joinAll
    return primary
  catch e =>
    return primary <|> some e

/-- Print a cleanup fault that followed the line already written. -/
private def showLater (later : Option IO.Error) : IO Unit := do
  if let some err := later then
    try IO.eprintln s!"{err}" catch _ => pure ()

/-- The address the listener asks the kernel to bind. -/
private def loopback : IO Multiformats.Multiaddr := do
  match Multiformats.Multiaddr.parse? "/ip4/127.0.0.1/tcp/0" with
  | .ok addr => return addr
  | .error e => throw <| IO.userError (reprStr e)

/-- Open one stream under `commandBudget`. Expiry starts `Host.close`
on the dialer, which wakes the parked open. A late stream is reset
through the same set. The caller owns a stream this function returns. -/
private def withStream (dialer : Host) (peer : PeerId) (id : Libp2p.Core.ProtocolId)
    (exchange : Streams.Stream → IO UInt32) : IO UInt32 := do
  let cleanup ← Conc.TaskSet.new
  let opened ← try
      Conc.Async.run <|
        Conc.withinDeadline Conc.Clock.system commandBudget
          (cleanup.spawn dialer.close)
          (dialer.newStream peer [id])
          (fun
            | .ok (_, stream) => cleanup.spawn stream.reset
            | .error _ => pure ())
    catch e =>
      cleanup.spawn dialer.close
      let fault ← joinCleanup cleanup (some e)
      if let some err := fault then throw err
      throw e
  match opened with
  | .error .deadlineExpired =>
    let later ← joinCleanup cleanup none
    IO.eprintln (Error.stream (.timeout "the stream opening deadline expired")).render
    showLater later
    return 1
  | .error .closed =>
    let later ← joinCleanup cleanup none
    IO.eprintln (Error.stream (.closed "the stream opening select closed")).render
    showLater later
    return 1
  | .ok (.error e) =>
    let later ← joinCleanup cleanup none
    IO.eprintln e.render
    showLater later
    return 1
  | .ok (.ok (_, stream)) =>
    match ← joinCleanup cleanup none with
    | some err =>
      resetStream stream
      IO.eprintln s!"{err}"
      return 1
    | none =>
      exchange stream

/-- One ping. The exchange deadline starts after `newStream` returns.
A timeout or a protocol failure resets the stream. A validated echo
closes it. `.ok none` stays the end-of-stream channel. -/
private def runPing (dialer : Host) (peer : PeerId) : IO UInt32 :=
  withStream dialer peer Libp2p.Protocols.Ping.protocolId fun stream => do
    let payload ← match ← (Crypto.randomBytes Libp2p.Protocols.Ping.payloadSize).run with
      | .error e =>
        resetStream stream
        IO.eprintln (reprStr e)
        return 1
      | .ok payload => pure payload
    let resets ← Conc.TaskSet.new
    let raced ← try
        Conc.Async.run <|
          Conc.withinDeadline Conc.Clock.system commandBudget
            (resets.spawn stream.reset)
            (Libp2p.Protocols.Ping.ping stream Conc.Clock.system payload)
      catch e =>
        resets.spawn stream.reset
        let fault ← joinCleanup resets (some e)
        IO.eprintln s!"{fault.getD e}"
        return 1
    let later ← joinCleanup resets none
    match raced with
    | .error .deadlineExpired =>
      IO.eprintln (Error.stream (.timeout "the ping exchange deadline expired")).render
      showLater later
      return 1
    | .error .closed =>
      resetStream stream
      IO.eprintln (Error.stream (.closed "the ping exchange select closed")).render
      showLater later
      return 1
    | .ok (.error e) =>
      resetStream stream
      IO.eprintln (Error.stream (Libp2p.Protocols.Ping.mapPingError e)).render
      showLater later
      return 1
    | .ok (.ok none) =>
      resetStream stream
      IO.eprintln (Error.stream (.closed "ping returned no round trip")).render
      showLater later
      return 1
    | .ok (.ok (some rtt)) =>
      if let some err := later then
        resetStream stream
        IO.eprintln s!"{err}"
        return 1
      try
        Conc.Async.run stream.close
      catch e =>
        IO.eprintln s!"{e}"
        return 1
      writeLine s!"ping rtt: {rtt} ms"
      return 0

/-- The facts the demo checks after `Identify.client`. The client
receives `some peer` and owns the peer comparison. This check requires
the bound address and every registered protocol id. -/
private def requireIdentify (msg : Libp2p.Protocols.Identify)
    (bound : Multiformats.Multiaddr) : Except Error Unit := do
  if !msg.listenAddrs.contains bound.toBytes then
    throw <| Error.stream (.protocol "identify: the bound address is absent")
  if !registered.all fun id => msg.protocols.contains id then
    throw <| Error.stream (.protocol "identify: a registered protocol is absent")
  return ()

/-- One identify exchange. The client owns the read deadline and resets
the stream when that deadline expires. `.ok none` stays the
end-of-stream channel. -/
private def runIdentify (dialer : Host) (peer : PeerId) (bound : Multiformats.Multiaddr) :
    IO UInt32 :=
  withStream dialer peer Libp2p.Protocols.Identify.protocolId fun stream => do
    let got ← Conc.Async.run
      (Libp2p.Protocols.Identify.client stream Conc.Clock.system commandBudget (some peer))
    match got with
    | .error e =>
      resetStream stream
      return ← failHost (Error.stream (Libp2p.Protocols.Identify.mapIdentifyError e))
    | .ok none =>
      resetStream stream
      return ← failHost (Error.stream (.closed "identify: the stream ended before a record"))
    | .ok (some (msg, pid)) =>
      match requireIdentify msg bound with
      | .error e =>
        resetStream stream
        return ← failHost e
      | .ok () =>
        try
          Conc.Async.run stream.close
        catch e =>
          IO.eprintln s!"{e}"
          return 1
        writeLine s!"identified: {PeerId.toString pid}, {msg.listenAddrs.length} addr(s), {msg.protocols.length} protocol(s)"
        return 0

/-- One echo exchange. The deadline starts after `newStream` returns.
The handler reads one chunk. A reply that differs, and an EOF before a
reply, both exit 1. The caller closes the stream after a match. -/
private def runEcho (dialer : Host) (peer : PeerId) : IO UInt32 :=
  withStream dialer peer Libp2p.Protocols.TestSupport.Echo.protocolId fun stream => do
    let resets ← Conc.TaskSet.new
    let raced ← try
        Conc.Async.run <|
          Conc.withinDeadline Conc.Clock.system commandBudget
            (resets.spawn stream.reset)
            (Libp2p.Protocols.TestSupport.Echo.exchange stream echoPayload)
      catch e =>
        resets.spawn stream.reset
        let fault ← joinCleanup resets (some e)
        IO.eprintln s!"{fault.getD e}"
        return 1
    let later ← joinCleanup resets none
    match raced with
    | .error .deadlineExpired =>
      IO.eprintln (Error.stream (.timeout "the echo exchange deadline expired")).render
      showLater later
      return 1
    | .error .closed =>
      resetStream stream
      IO.eprintln (Error.stream (.closed "the echo exchange select closed")).render
      showLater later
      return 1
    | .ok (.error e) =>
      resetStream stream
      IO.eprintln (Error.stream e).render
      showLater later
      return 1
    | .ok (.ok none) =>
      resetStream stream
      IO.eprintln (Error.stream (.closed "echo: the stream ended before a reply")).render
      showLater later
      return 1
    | .ok (.ok (some got)) =>
      if got != echoPayload then
        resetStream stream
        IO.eprintln (Error.stream (.protocol "echo: the reply differs")).render
        showLater later
        return 1
      if let some err := later then
        resetStream stream
        IO.eprintln s!"{err}"
        return 1
      try
        Conc.Async.run stream.close
      catch e =>
        IO.eprintln s!"{e}"
        return 1
      writeLine "echo: echo-me"
      return 0

/-- Listen, dial, and run ping, identify, and echo. The caller closes
both hosts. -/
private def runDemo (listener dialer : Host) : IO UInt32 := do
  listener.setHandler Libp2p.Protocols.Ping.pingHandler
  listener.setHandler Libp2p.Protocols.TestSupport.Echo.handler
  let bound ← match ← Conc.Async.run (listener.startListening (← loopback)) with
    | .error e => return ← failHost e
    | .ok bound => pure bound
  let key ← match listener.config.identity.toPublic with
    | .error e => return ← failLine (reprStr e)
    | .ok key => pure key
  listener.setHandler (Libp2p.Protocols.Identify.respondHandler key [bound.toBytes]
    registered agent)
  dialer.addAddrs listener.localPeer [bound]
  let peer ← match ← Conc.Async.run (dialer.dialPeer listener.localPeer) with
    | .error e => return ← failHost e
    | .ok peer => pure peer
  writeLine s!"dialed {PeerId.toString peer} (noise + yamux, remote verified)"
  let pingCode ← runPing dialer peer
  if pingCode != 0 then return pingCode
  let identifyCode ← runIdentify dialer peer bound
  if identifyCode != 0 then return identifyCode
  runEcho dialer peer

/-- Close `dialer`, then `listener`. A fault from the first close still
runs the second. A close fault is printed only when `code` is still
success, so the first fault stays the line on stderr. -/
private def closeBoth (dialer listener : Host) (code : UInt32) : IO UInt32 := do
  let mut code := code
  try
    Conc.Async.run dialer.close
  catch e =>
    if code == 0 then
      try IO.eprintln s!"{e}" catch _ => pure ()
    code := 1
  try
    Conc.Async.run listener.close
  catch e =>
    if code == 0 then
      try IO.eprintln s!"{e}" catch _ => pure ()
    code := 1
  return code

/-- Run `body`, then close the dialer and the listener. `closeBoth`
joins both host tasks before this function reads the callback. A
reported callback exits 1. A stored write fault exits 1, and it is
printed only when the body and the closes left `code` at 0. A fault
already printed stays the stderr line. -/
private def guarding (dialer listener : Host) (faults : IO.Ref CallbackState)
    (body : IO UInt32) : IO UInt32 := do
  let mut code : UInt32 := 0
  try
    code ← body
  catch e =>
    code := 1
    try IO.eprintln s!"{e}" catch _ => pure ()
  code ← closeBoth dialer listener code
  let state ← faults.get
  if let some e := state.writeFault then
    if code == 0 then
      try IO.eprintln s!"{e}" catch _ => pure ()
  return exitAfterCleanup code state

/-- Close the listener after the dialer failed to appear. The listener
line stays the one already chosen. A close fault does not replace it. -/
private def dropListener (listener : Host) (report : IO Unit) : IO UInt32 := do
  try
    Conc.Async.run listener.close
  catch _ => pure ()
  try report catch _ => pure ()
  return 1

/-- Build both hosts. The listener is owned as soon as its `Host.new`
returns. A failure while the dialer is built closes that listener. -/
private def demonstrate : IO UInt32 := do
  let faults ← IO.mkRef emptyCallback
  let listener ← try
      match ← openHost faults [] with
      | .error line => return ← failLine line
      | .ok host => pure host
    catch e =>
      try IO.eprintln s!"{e}" catch _ => pure ()
      return 1
  try
    match ← openHost faults [] with
    | .error line => return ← dropListener listener (IO.eprintln line)
    | .ok dialer => return ← guarding dialer listener faults (runDemo listener dialer)
  catch e =>
    dropListener listener (IO.eprintln s!"{e}")

/-- Check `args`. An empty list runs the two-host demo. -/
def main (args : List String) : IO UInt32 := do
  match command.parse args with
  | .error err => usage err.kind.msg
  | .ok _ =>
    -- `parse` treats `--` as the end of flags, so an empty command
    -- can still have seen an argument.
    if args.isEmpty then demonstrate else usage s!"unexpected argument: {" ".intercalate args}"

end Cli.Demo

def main : List String → IO UInt32 := Cli.Demo.main
