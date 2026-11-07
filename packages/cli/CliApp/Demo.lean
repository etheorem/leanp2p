import Cli
import CliApp.Mock.Stack

/-!
# Demo composition

The binary creates two fresh hosts, then calls the protocol clients
through the negotiated streams. The nested finalizers own both hosts
from the moment creation succeeds. Each client stream is reset on
every exit, including an IO fault. No protocol bytes are decoded here.

The runtime argument exists only to test this executable's workflow.
The default uses the unmerged dependency interfaces, whose failure
bodies report that networking is unavailable. Workflow tests are
distinct from the real loopback gate in the package plan.
-/

set_option autoImplicit false

namespace CliApp.Demo

open Mock

/-- The demo's composition statement; every handler is a dependency value. -/
def hostConfig (key : PrivKey) (static : Key32) : HostConfig :=
  { key
    transports := [tcpTransport]
    securities := [noiseSecurity key static]
    muxers := [yamux]
    handlers := [Ping.pingHandler, Echo.handler]
    gater := Policy.permissiveGater
    resourceManager := Policy.unlimitedResources
    addressRanker := Policy.identityRanker }

/-- Fresh key generation is repeated for each host, with no fallback identity. -/
def makeHost : ExceptT HostError Conc.Async Host := do
  let key ← generateIdentity
  let static ← generateStatic
  Host.new (hostConfig key static)

/-- Operations of this executable, with output captured by its workflow tests. -/
structure Runtime where
  newHost : ExceptT HostError Conc.Async Host := makeHost
  parseAddress : String → Except String Multiaddr := Multiaddr.parse?
  randomPing : ExceptT HostError Conc.Async ByteArray := randomPayload
  ping : Streams.Stream → ByteArray → ExceptT HostError Conc.Async Nat :=
    fun stream payload => Ping.ping stream Conc.Clock.system payload
  identify : Streams.Stream → PeerId → ExceptT HostError Conc.Async Identify.Result := Identify.request
  echo : Streams.Stream → ByteArray → ExceptT HostError Conc.Async ByteArray := Echo.exchange
  stdout : String → IO Unit := IO.println
  stderr : String → IO Unit := IO.eprintln

/-- The protocol clients own their validation; the demo checks no lower-layer error. -/
def exchange (runtime : Runtime) (listener dialer : Host) : ExceptT HostError Conc.Async Unit := do
  let address ← match runtime.parseAddress "/ip4/127.0.0.1/tcp/0" with
    | .ok value => pure value
    | .error reason => throw (.upgrade (.protocol reason))
  listener.setHandler (Identify.handler listener)
  let bound ← listener.startListening address
  dialer.addAddrs listener.id [bound]
  dialer.dialPeer listener.id
  runtime.stdout s!"dialed {listener.id.toBase58} (noise + yamux, remote verified)"

  let pingStream ← dialer.newStreamTo listener.id Ping.protocolId
  try
    let payload ← runtime.randomPing
    let elapsed ← runtime.ping pingStream payload
    runtime.stdout s!"ping rtt: {elapsed} ms"
  finally
    pingStream.reset

  let identifyStream ← dialer.newStreamTo listener.id Identify.protocolId
  try
    let metadata ← runtime.identify identifyStream listener.id
    runtime.stdout s!"identified: {metadata.peer.toBase58}, {metadata.addressCount} addr(s), {metadata.protocolCount} protocol(s)"
  finally
    identifyStream.reset

  let echoStream ← dialer.newStreamTo listener.id Echo.protocolId
  try
    let reply ← runtime.echo echoStream (Bytes.ofString "echo-me")
    runtime.stdout s!"echo: {(Bytes.toString? reply).getD "<binary>"}"
  finally
    echoStream.reset

/-- A failed second allocation still closes the first host. -/
def execute (runtime : Runtime) : ExceptT HostError Conc.Async Unit := do
  let listener ← runtime.newHost
  try
    let dialer ← runtime.newHost
    try
      exchange runtime listener dialer
    finally
      dialer.close
  finally
    listener.close

/-- The maintained parser owns help, flags and rejection of surplus arguments. -/
def command : Cli.Cmd :=
  Cli.Cmd.mk "demo" none "Connect two local hosts and run ping, identify and echo."
    (run := fun _ => pure 0)

/-- Usage failures happen before any identity or host is allocated. -/
def runWith (runtime : Runtime) (args : List String) : IO UInt32 := do
  match command.process args with
  | .error (_, reason) => runtime.stderr reason; return 2
  | .ok (_, parsed) =>
      if parsed.hasFlag "help" then runtime.stdout command.help; return 0
      try
        match ← Conc.Async.run ((execute runtime).run) with
        | .ok () => return 0
        | .error error => runtime.stderr s!"demo: {repr error}"; return 1
      catch error =>
        runtime.stderr s!"demo: {error}"
        return 1

end CliApp.Demo
