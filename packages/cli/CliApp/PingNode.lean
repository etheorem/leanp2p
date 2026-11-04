import Cli
import CliApp.Mock.Stack

/-!
# Ping node composition

Serve announces a bound address before waiting for stdin EOF. The
blocking stdin reader runs on a dedicated thread; the networking
runtime parks on its completion and keeps its shared worker free.
Dial delegates peer authentication to the host and echo validation
to the ping client. Every allocated host closes and joins on exit.
-/

set_option autoImplicit false

namespace CliApp.PingNode

open Mock

/-- The two CLI modes have different argument types. -/
inductive Command where
  | serve (port : UInt16)
  | dial (address : String)
  | help (text : String)

/-- The maintained parser rejects extra arguments and unknown flags. -/
def command : Cli.Cmd :=
  Cli.Cmd.mk "pingnode" none "Serve or dial one ping peer."
    (run := fun _ => pure 0)
    (subCmds := #[
      Cli.Cmd.mk "serve" none "Serve ping on IPv4 loopback until stdin closes."
        (run := fun _ => pure 0)
        (positionalArgs := #[⟨"port", "A decimal port from 0 to 65535.", (String : Cli.ParamType)⟩]),
      Cli.Cmd.mk "dial" none "Dial a multiaddr whose trailing /p2p/id pins the peer."
        (run := fun _ => pure 0)
        (positionalArgs := #[⟨"multiaddr", "The complete peer multiaddr.", (String : Cli.ParamType)⟩])])

/-- Ports use ASCII decimal digits only; conversion happens after the range check. -/
def parsePort? (text : String) : Option UInt16 := do
  if text.isEmpty || !text.toList.all (fun c => '0' ≤ c && c ≤ '9') then none
  else
    let value ← text.toNat?
    if value < 65536 then some (UInt16.ofNat value) else none

/-- Dial mode requires the parsed final component, including the alias normalized by W2.3. -/
def hasPeerSuffix (address : Multiaddr) : Bool :=
  address.components.getLast?.map (·.proto) == some .p2p

/-- Parsing does not allocate keys or touch the network. -/
def parse? (args : List String) : Except String Command := do
  let (selected, parsed) ← command.process args |>.mapError Prod.snd
  if parsed.hasFlag "help" then return .help selected.help
  match selected.meta.name, parsed.positionalArgs.toList with
  | "serve", [port] =>
      match parsePort? port.value with
      | some port => .ok (.serve port)
      | none => .error "port must contain decimal digits and be between 0 and 65535"
  | "dial", [address] =>
      if address.value.isEmpty then .error "a peer multiaddr is required"
      else .ok (.dial address.value)
  | _, _ => .error "usage: pingnode serve <port> | pingnode dial <multiaddr>"

/-- Input on a dedicated reader cannot starve the async networking tasks. -/
def waitForInputEnd : Conc.Async Unit := do
  let task ← IO.asTask (prio := .dedicated) do
    let stdin ← IO.getStdin
    let mut ended := false
    while !ended do
      ended := (← stdin.getLine).isEmpty
  match ← Conc.Wrap.await task with
  | .ok () => pure ()
  | .error error => throw error

/-- The ordered implementation lists are assembled at the executable boundary. -/
def hostConfig (key : PrivKey) (static : Key32) : HostConfig :=
  { key
    transports := [tcpTransport]
    securities := [noiseSecurity key static]
    muxers := [yamux]
    handlers := [Ping.pingHandler]
    gater := Policy.permissiveGater
    resourceManager := Policy.unlimitedResources
    addressRanker := Policy.identityRanker }

/-- Every invocation creates fresh identity and Noise static keys. -/
def makeHost : ExceptT HostError Conc.Async Host := do
  let key ← generateIdentity
  let static ← generateStatic
  Host.new (hostConfig key static)

/-- Operations of this executable, supplied explicitly to workflow tests. -/
structure Runtime where
  newHost : ExceptT HostError Conc.Async Host := makeHost
  parseAddress : String → Except String Multiaddr := Multiaddr.parse?
  randomPing : ExceptT HostError Conc.Async ByteArray := randomPayload
  ping : Streams.Stream → ByteArray → ExceptT HostError Conc.Async Nat :=
    fun stream payload => Ping.ping stream Conc.Clock.system payload
  waitInput : Conc.Async Unit := waitForInputEnd
  stdout : String → IO Unit := IO.println
  flush : IO Unit := do (← IO.getStdout).flush
  stderr : String → IO Unit := IO.eprintln

/-- Serve publishes the actual bound address and flushes it before waiting. -/
def serve (runtime : Runtime) (port : UInt16) : ExceptT HostError Conc.Async Unit := do
  let address ← match runtime.parseAddress s!"/ip4/127.0.0.1/tcp/{port.toNat}" with
    | .ok value => pure value
    | .error reason => throw (.upgrade (.protocol reason))
  let host ← runtime.newHost
  try
    host.setHandler (Identify.handler host)
    let bound ← host.startListening address
    runtime.stdout s!"ADDR {bound.toString} {host.id.toBase58}"
    runtime.flush
    runtime.waitInput
  finally
    host.close

/-- The expected peer comes from the address suffix, which the host validates. -/
def dial (runtime : Runtime) (address : Multiaddr) : ExceptT HostError Conc.Async Unit := do
  let host ← runtime.newHost
  try
    let peer ← host.dial address none
    let stream ← host.newStreamTo peer Ping.protocolId
    try
      let payload ← runtime.randomPing
      let elapsed ← runtime.ping stream payload
      runtime.stdout s!"PING OK rtt={elapsed}ms"
    finally
      stream.reset
  finally
    host.close

/-- Usage errors exit 2, protocol or system failures exit 1, and success exits 0. -/
def runWith (runtime : Runtime) (args : List String) : IO UInt32 := do
  match parse? args with
  | .error reason => runtime.stderr reason; return 2
  | .ok (.help text) => runtime.stdout text; return 0
  | .ok mode =>
      try
        let action ← match mode with
          | .serve port => pure (serve runtime port)
          | .dial text =>
              match runtime.parseAddress text with
              | .ok address =>
                  if hasPeerSuffix address then pure (dial runtime address)
                  else runtime.stderr "dial requires a trailing /p2p/<peer-id>"; return 2
              | .error reason => runtime.stderr reason; return 2
          | .help _ => return 0
        match ← Conc.Async.run action.run with
        | .ok () => return 0
        | .error error => runtime.stderr s!"pingnode: {repr error}"; return 1
      catch error =>
        runtime.stderr s!"pingnode: {error}"
        return 1

end CliApp.PingNode
