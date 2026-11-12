import Cli
import Conc
import Crypto
import Streams
import Multiformats
import Libp2p.Core
import Libp2p.Identity
import Libp2p.Security
import Libp2p.Mux
import Libp2p.Host
import Libp2p.Protocols.Ping
import Libp2p.Protocols.Identify

/-!
# PingNode

The `pingnode` executable. `Cmd.parse` accepts `serve <port>` or
`dial <multiaddr>`. `Cmd.init` keeps the help and version flags out
of the command. A usage error exits 2, before any host exists.
`splitPeer` drops the trailing peer. A `p2p` component left in the
transport prefix is a usage error. A line break in an operand is
escaped in the usage line.

`serve` builds one host after that check. It listens, registers
identify, prints `ADDR`, and flushes. It then reads stdin in `IO`.
EOF calls `Host.close` and exits 0. `dial` dials the expected peer,
opens one ping stream under the 30 second command budget, completes
one exchange, prints `PING OK`, and closes the host.
-/

set_option autoImplicit false

namespace Cli.PingNode

open Cli
open Libp2p.Host (Host Error Failure)
open Libp2p.Identity (PeerId PrivKey)

/-- One string operand. -/
private def operand (name description : String) : Arg :=
  { name, description, type := String }

/-- A subcommand with one operand and no flags. -/
private def leaf (name argName description : String) : Cmd :=
  .init {
    name
    parentNames := #["pingnode"]
    version? := none
    description
    flags := #[]
    positionalArgs := #[operand argName description]
    variableArg? := none
  } (fun _ => pure 0) #[] none

/-- `serve` and `dial`, and no flags on the root. -/
private def command : Cmd :=
  .init {
    name := "pingnode"
    parentNames := #[]
    version? := none
    description := "Serve or dial a ping."
    flags := #[]
    positionalArgs := #[]
    variableArg? := none
  } (fun _ => pure 0) #[
    leaf "serve" "port" "Listen on a port.",
    leaf "dial" "multiaddr" "Dial a multiaddr."
  ] none

/-- Replace a newline with `\n` and a carriage return with `\r`. -/
private def oneLine (text : String) : String :=
  (text.replace "\r" "\\r").replace "\n" "\\n"

/-- Print one usage line and exit 2. -/
private def usage (line : String) : IO UInt32 := do
  IO.eprintln (oneLine line)
  return 2

/-- The agent string identify advertises. -/
private def agent : String := "leanp2p"

/-- The stderr line for one inbound failure. -/
private def failureLine (f : Failure) : String := Id.run do
  let mut line := f.error.render
  if let some peer := f.peer then
    line := s!"{line} peer {peer}"
  if let some protocol := f.protocol then
    line := s!"{line} protocol {protocol}"
  return line

/-- Keep the first diagnostic write that threw. `modify` holds the cell
for the whole update, so the first stored fault stays. -/
private def keepFault (faults : IO.Ref (Option IO.Error)) (e : IO.Error) : BaseIO Unit :=
  faults.modify fun old => if old.isNone then some e else old

/-- Write the failure from the host task that saw it. `Host.close`
joins that task, so the write has finished when `close` returns. A
thrown write stays in `faults` and the accept loop continues. -/
private def reportFailure (faults : IO.Ref (Option IO.Error)) (f : Failure) : BaseIO Unit :=
  EIO.catchExceptions (IO.eprintln (failureLine f)) (keepFault faults)

/-- A fresh Ed25519 host: TCP, Noise, yamux, then mplex, and ping. -/
private def openHost (faults : IO.Ref (Option IO.Error)) : IO (Except String Host) := do
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
    handlers := [Libp2p.Protocols.Ping.pingHandler]
    onFailure := reportFailure faults
  } : BaseIO _) with
  | .error e => return .error (reprStr e)
  | .ok host => return .ok host

/-- Run `body`, then `Host.close`. A fault of either path exits 1.
The first fault is the line on stderr. A diagnostic write that threw
during the run exits 1 after `close` joins the host task. -/
private def guarding (host : Host) (faults : IO.Ref (Option IO.Error))
    (body : IO UInt32) : IO UInt32 := do
  let mut code : UInt32 := 0
  try
    code ← body
  catch e =>
    code := 1
    try IO.eprintln s!"{e}" catch _ => pure ()
  try
    Conc.Async.run host.close
  catch e =>
    if code == 0 then
      try IO.eprintln s!"{e}" catch _ => pure ()
    code := 1
  match ← faults.get with
  | some e =>
    if code == 0 then
      try IO.eprintln s!"{e}" catch _ => pure ()
    return 1
  | none =>
    return code

/-- The address `serve` asks the kernel to bind. -/
private def listenAddr (port : Nat) : IO Multiformats.Multiaddr := do
  match Multiformats.Multiaddr.parse? s!"/ip4/127.0.0.1/tcp/{port}" with
  | .ok addr => return addr
  | .error e => throw <| IO.userError (reprStr e)

/-- Print `ADDR` and flush before the stdin read. -/
private def publishReady (bound : Multiformats.Multiaddr) (peer : PeerId) : IO Unit := do
  let out ← IO.getStdout
  out.putStr s!"ADDR {bound} {peer}\n"
  out.flush

/-- Read stdin until EOF. A line that is not EOF is discarded. -/
private def waitStdin : IO Unit := do
  let stdin ← IO.getStdin
  repeat
    let line ← stdin.getLine
    if line.isEmpty then return

/-- Listen, serve ping and identify, and stop on stdin EOF. -/
private def serve (portText : String) : IO UInt32 := do
  let some port := portText.toNat?
    | do
      IO.eprintln s!"invalid port: {oneLine portText}"
      return 1
  let faults ← IO.mkRef (none : Option IO.Error)
  match ← openHost faults with
  | .error line =>
    IO.eprintln line
    return 1
  | .ok host =>
    guarding host faults do
      match ← Conc.Async.run (host.startListening (← listenAddr port)) with
      | .error e =>
        IO.eprintln e.render
        return 1
      | .ok bound =>
        let key ← match host.config.identity.toPublic with
          | .error e =>
            IO.eprintln (reprStr e)
            return 1
          | .ok key => pure key
        let protocols := [
          Libp2p.Protocols.Ping.protocolId.toString,
          Libp2p.Protocols.Identify.protocolId.toString
        ]
        host.setHandler (Libp2p.Protocols.Identify.respondHandler key [bound.toBytes]
          protocols agent)
        publishReady bound host.localPeer
        waitStdin
        return 0

/-- `0`, or a decimal from 1 to 65535 with no leading zero. -/
private def validPort (text : String) : Bool :=
  if text == "0" then true
  else
    text.all Char.isDigit && text.front?.any (· != '0') &&
      match text.toNat? with
      | some n => n ≤ 65535
      | none => false

/-- The operand of the selected subcommand. -/
private def operandValue (parsed : Parsed) (name : String) : Option String :=
  parsed.positionalArg? name |>.map (·.value)

/-- True when `transport` still contains a `/p2p` component. -/
private def transportHasPeer (transport : Multiformats.Multiaddr) : Bool :=
  transport.components.any fun c =>
    decide (c.proto = Multiformats.Protocol.«p2p»)

/-- Accept a final `/p2p/<id>` whose transport prefix has no `/p2p`.
The pair is the address `Host.dial` takes and the expected peer. -/
private def validDial (text : String) :
    Except String (Multiformats.Multiaddr × PeerId) := do
  let addr ← match Multiformats.Multiaddr.parse? text with
    | .ok addr => pure addr
    | .error err => throw s!"{reprStr err} {text}"
  match Host.splitPeer addr with
  | .ok (transport, some peer) =>
    if transportHasPeer transport then
      throw s!"dial address has an earlier /p2p peer: {text}"
    else pure (addr, peer)
  | .ok (_, none) => throw s!"dial address has no final /p2p peer: {text}"
  | .error err => throw s!"{err} {text}"

/-- The command budget around `Host.newStream` and the ping exchange.
The home of the duration is `Streams.unauthDeadlineMs`. -/
private def commandBudget : Nat := Streams.unauthDeadlineMs

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

/-- Print `line` and exit 1. -/
private def failLine (line : String) : IO UInt32 := do
  IO.eprintln line
  return 1

/-- One ping on `stream`. The exchange deadline starts here. A timeout
or a protocol failure resets the stream. A validated echo closes it. -/
private def onePing (stream : Streams.Stream) : IO UInt32 := do
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
    if let some err := later then IO.eprintln s!"{err}"
    return 1
  | .error .closed =>
    resetStream stream
    IO.eprintln (Error.stream (.closed "the ping exchange select closed")).render
    if let some err := later then IO.eprintln s!"{err}"
    return 1
  | .ok (.error e) =>
    resetStream stream
    IO.eprintln (Error.stream (Libp2p.Protocols.Ping.mapPingError e)).render
    if let some err := later then IO.eprintln s!"{err}"
    return 1
  | .ok (.ok none) =>
    resetStream stream
    IO.eprintln (Error.stream (.protocol "ping returned no round trip")).render
    if let some err := later then IO.eprintln s!"{err}"
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
    IO.println s!"PING OK rtt={rtt}ms"
    return 0

/-- Open the ping stream under `commandBudget`. Expiry starts
`Host.close` on `cleanup`, which wakes the parked open. A late stream
is reset through the same set. -/
private def openPing (host : Host) (peer : PeerId) (cleanup : Conc.TaskSet) :
    IO (Except Conc.Error (Except Error (Libp2p.Core.ProtocolId × Streams.Stream))) := do
  try
    Conc.Async.run <|
      Conc.withinDeadline Conc.Clock.system commandBudget
        (cleanup.spawn host.close)
        (host.newStream peer [Libp2p.Protocols.Ping.protocolId])
        (fun
          | .ok (_, stream) => cleanup.spawn stream.reset
          | .error _ => pure ())
  catch e =>
    cleanup.spawn host.close
    let fault ← joinCleanup cleanup (some e)
    if let some err := fault then throw err
    throw e

/-- Dial `addr`, require `peer`, and print one ping. `guarding` closes
the host on every return. -/
private def dial (addr : Multiformats.Multiaddr) (peer : PeerId) : IO UInt32 := do
  let faults ← IO.mkRef (none : Option IO.Error)
  match ← openHost faults with
  | .error line => failLine line
  | .ok host =>
    guarding host faults do
      match ← Conc.Async.run (host.dial addr (some peer)) with
      | .error e => failLine e.render
      | .ok _ =>
        let cleanup ← Conc.TaskSet.new
        let opened ← openPing host peer cleanup
        match opened with
        | .error .deadlineExpired =>
          let later ← joinCleanup cleanup none
          IO.eprintln (Error.stream (.timeout "the stream opening deadline expired")).render
          if let some err := later then IO.eprintln s!"{err}"
          return 1
        | .error .closed =>
          let later ← joinCleanup cleanup none
          IO.eprintln (Error.stream (.closed "the stream opening select closed")).render
          if let some err := later then IO.eprintln s!"{err}"
          return 1
        | .ok (.error e) => failLine e.render
        | .ok (.ok (_, stream)) => onePing stream

/-- Check `args`. `serve` runs the host. `dial` pings the expected peer. -/
def main (args : List String) : IO UInt32 := do
  match command.parse args with
  | .error err => usage err.kind.msg
  | .ok (cmd, parsed) =>
    match cmd.meta.name with
    | "serve" =>
      match operandValue parsed "port" with
      | some port =>
        if validPort port then serve port else usage s!"invalid port: {port}"
      | none => usage "missing port"
    | "dial" =>
      match operandValue parsed "multiaddr" with
      | some text =>
        match validDial text with
        | .ok (addr, peer) => dial addr peer
        | .error line => usage line
      | none => usage "missing multiaddr"
    | _ => usage "missing subcommand"

end Cli.PingNode

def main : List String → IO UInt32 := Cli.PingNode.main
