import Crypto
import Streams
import Interop.Config
import Interop.Redis
import Interop.Mock.Stack

/-!
# The transport-interop harness

One run of the libp2p transport-interop test plan
(`vendor/test-plans/transport-interop/README.md`), as the listener or
the dialer. The steps are the test plan's, in its order, and go-libp2p's
test-plan peer is the model on the other side of the wire
(`vendor/go-libp2p/test-plans/cmd/ping/main.go`).

Both sides read the configuration, connect to Redis, and start a host
with the TCP transport, Noise, and the configured muxer.

* **The listener** listens, publishes its address with the `/p2p/<id>`
  suffix through `RPUSH`, and sleeps for the test timeout. The runner
  kills it when the dialer is done, and a run that reaches the end of
  the sleep failed.
* **The dialer** takes the address through `BLPOP`, dials it, opens a
  ping stream, and pings once. It prints the timing record to stdout,
  and nothing else.

Diagnostics go to stderr. Every failure exits nonzero.

## The published address

go's peer publishes its first address that is not loopback, from the
host's interface list (line 203 of its `main.go`). The Lean runtime has
no interface list. When the listener binds `0.0.0.0`, it publishes the
local address of its Redis connection instead: the kernel picked that
address to reach the server that both peers share, so the dialer
reaches it too.

## The measurements

The test plan measures `handshakePlusOneRTT` from just before the dial
to the end of the first ping, and `pingRTT` across the ping alone. The
harness reads `IO.monoNanosNow` around both, so the record has the
microsecond resolution of the go peer.
-/

set_option autoImplicit false

namespace Interop

open Conc (Async)
open Interop.Config (Config)
open Interop.Mock

/-- The interval between two `PING`s while Redis starts, in milliseconds.
The go peer waits the same 100 ms (line 84 of its `main.go`). -/
def redisRetryMs : Nat := 100

/-- A failed step: the message for stderr. -/
abbrev Run := ExceptT String Async

/-- Lift an `Except` with a printable error into a run. -/
def orFail {ε α : Type} (what : String) (render : ε → String) (x : Except ε α) : Run α :=
  match x with
  | .ok a => pure a
  | .error e => throw s!"{what}: {render e}"

/-- A Redis client that answered `PING`, or a failure once `timeoutSec`
has passed. -/
partial def connectRedis (cfg : Config) (deadlineMs : Nat) : Run Redis.Client := do
  let attempt : Async (Option Redis.Client) := do
    let some conn ← (Streams.Tcp.transport).dial cfg.redisAddr | return none
    match ← (Redis.Client.new conn).ping with
    | .ok c => return some c
    | .error _ =>
      conn.close
      return none
  -- A refused dial or a server that is not ready yet: wait and try
  -- again, as the go peer does. A fault of the dial is a retry too.
  let c ← try attempt catch _ => pure none
  if let some c := c then return c
  if deadlineMs ≤ (← IO.monoMsNow) then
    throw s!"redis at {cfg.redisAddr.describe}: no answer within {cfg.timeoutSec} s"
  let sleep ← Conc.Park.sleep redisRetryMs ()
  -- Park: the sleep ends it; nothing else waits on this task. The
  -- ascription keeps `select` in `Async` (see `dial` for the unfolding).
  (Conc.select #[sleep] : Async Unit)
  connectRedis cfg deadlineMs

/-- The host of one run: TCP, Noise, and the configured muxer, with the
ping handler (root §3.1: the ordered lists are assembled here). -/
def startHost (cfg : Config) : Run Host := do
  let key ← (generateKey : IO PrivKey)
  let muxer := match cfg.muxer with
    | .yamux => yamux
    | .mplex => mplex
  orFail "host" (fun e => reprStr e) (← Host.new {
    key
    transports := [Streams.Tcp.transport]
    securities := [noise key]
    muxers := [muxer]
    handlers := [Ping.handler] })

/-- The address the listener publishes: the bound address, with the
Redis connection's local IP in place of `0.0.0.0`, and the `/p2p/<id>`
suffix. -/
def publishedAddr (bound redisLocal : Multiformats.Multiaddr) (peer : PeerId) :
    Except String String := do
  let ip ← match bound.components, redisLocal.components with
    | ⟨.«ip4», [0, 0, 0, 0]⟩ :: _, mine :: _ => pure mine
    | ip :: _, _ => pure ip
    | [], _ => throw "the bound address has no components"
  let rest := bound.components.drop 1
  let some addr := Multiformats.Multiaddr.ofComponents? (ip :: rest)
    | throw "the published address does not check"
  return s!"{addr.describe}/p2p/{peer.text}"

/-- The listener: publish the address, then sleep for the timeout. -/
def listen (cfg : Config) (redis : Redis.Client) (h : Host) : Run Unit := do
  let bound ← orFail "listen" (fun e => reprStr e) (← h.startListening cfg.listenAddr)
  let addr ← orFail "address" id (publishedAddr bound redis.conn.localAddr h.id)
  IO.eprintln s!"listening on {addr}"
  discard <| orFail "redis RPUSH" (fun e => reprStr e)
    (← redis.rpush Config.listenerAddrKey addr)
  -- The test plan: sleep for the timeout; the runner kills the process
  -- when the dialer finishes.
  let sleep ← Conc.Park.sleep (1000 * cfg.timeoutSec) ()
  -- Park: the sleep ends it, or the runner's kill ends the process.
  (Conc.select #[sleep] : Async Unit)
  throw s!"no dialer finished within {cfg.timeoutSec} s"

/-- The dialer: take the address, dial, ping once, and print the timing
record. -/
def dial (cfg : Config) (redis : Redis.Client) (h : Host) : Run Unit := do
  let (text, _) ← orFail "redis BLPOP" (fun e => reprStr e)
    (← redis.blpop Config.listenerAddrKey cfg.timeoutSec)
  let some text := text | throw s!"no listener address within {cfg.timeoutSec} s"
  let addr ← orFail s!"listener address {text}" (fun e => reprStr e)
    (Multiformats.Multiaddr.parse? text)
  IO.eprintln s!"dialing {text}"
  let start ← IO.monoNanosNow
  let peer ← orFail "dial" (fun e => reprStr e) (← h.dial addr)
  let (_, stream) ← orFail "ping stream" (fun e => reprStr e)
    (← h.newStream peer [Ping.protocolId])
  let payload ← orFail "ping payload" (fun e => reprStr e)
    (← (Crypto.randomBytes Ping.payloadSize).run)
  let pingStart ← IO.monoNanosNow
  -- `Run` unfolds to `Async (Except String _)`, the type of `Ping.ping`,
  -- so an unannotated `←` would run the call as a `Run` step and throw
  -- its error here, before the reset below. The annotation makes Lean
  -- lift the `Async` call and bind the `Except` as data.
  let answer : Except String (Option Nat) ← (Ping.ping stream Conc.Clock.system payload : Async _)
  let done ← IO.monoNanosNow
  stream.reset
  discard <| orFail "ping" id answer
  IO.println (Config.timingJson ((done - start) / 1000) ((done - pingStart) / 1000))

/-- One harness run. The host closes on every path (cli ARCHITECTURE,
contract 5), and so does the Redis connection. -/
def run (cfg : Config) : Run Unit := do
  let deadlineMs := (← IO.monoMsNow) + 1000 * cfg.timeoutSec
  let redis ← connectRedis cfg deadlineMs
  try
    let h ← startHost cfg
    try
      if cfg.isDialer then dial cfg redis h else listen cfg redis h
    finally
      h.close
  finally
    redis.close

/-- The configuration from the process environment. -/
def readEnv : IO (String → Option String) := do
  let names := [Config.transportVar, Config.muxerVar, Config.securityVar, Config.isDialerVar,
    Config.ipVar, Config.redisAddrVar, Config.timeoutVar]
  let values ← names.mapM fun n => return (n, ← IO.getEnv n)
  return fun n => (values.lookup n).join

/-- The entry point: exit 0 when the run passed, 1 otherwise. -/
def main : IO UInt32 := do
  match Config.parse (← readEnv) with
  | .error e =>
    IO.eprintln s!"interop: {e}"
    return 1
  | .ok cfg =>
    -- A failed step is an `Except` value, and a fault is an `IO.Error`
    -- (§3.5). Both end the run with a diagnostic and exit 1.
    try
      match ← Conc.Async.run (run cfg).run with
      | .ok () => return 0
      | .error e =>
        IO.eprintln s!"interop: {e}"
        return 1
    catch e =>
      IO.eprintln s!"interop: {e}"
      return 1

end Interop
