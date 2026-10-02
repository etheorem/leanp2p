import LeanP2P
import LeanP2P.Interop.Redis

/-!
# interop — the phase 5 transport-interop harness (step 25)

Shape-compatible with `libp2p/test-plans/transport-interop` (the nim
implementation is the closest native template): parameters arrive as
environment variables, the listener publishes its multiaddr through
Redis (`RPUSH listenerAddr`), the dialer fetches it (`BLPOP`), dials,
pings once and prints the timing JSON to stdout — all diagnostics go to
stderr, and exit is nonzero on any failure or timeout.

Environment (per the test-plan README):

| name                 | default      | notes                                  |
|----------------------|--------------|----------------------------------------|
| `transport`          | required     | `tcp` (ws/quic: phase 5 remaining)     |
| `muxer`              | required     | `yamux` or `mplex`                     |
| `security`           | required     | `noise` (tls: phase 5 remaining)       |
| `is_dialer`          | required     | `true` / `false`                       |
| `ip`                 | `0.0.0.0`    | bind ip; also the advertised ip, so pass a dialable one (docker network ip / 127.0.0.1) |
| `redis_addr`         | `redis:6379` | must be `ip:port` (no DNS in the spike's redis client) |
| `test_timeout_seconds` | `180`      | listener lifetime / dialer BLPOP bound |

Dialer stdout (keys verbatim from the test plan, including its
`pingRTTMilllis` typo):

    {"handshakePlusOneRTTMillis": 12, "pingRTTMilllis": 4}

Known gap: the dial/ping phase has no internal timeout (only the BLPOP
is bounded); a peer that accepts but never responds parks the dialer
until the runner kills it, exactly as the test plan's
`test_timeout_seconds` provides for.
-/

open LeanP2P
open LeanP2P.Interop

structure InteropCfg where
  transport : String
  muxer : String
  security : String
  isDialer : Bool
  ip : String
  redisAddr : String
  timeoutSecs : Nat

def envDflt (k dflt : String) : IO String := do
  match ← IO.getEnv k with
  | some v => pure v
  | none => pure dflt

def readCfg : IO (Option InteropCfg) := do
  let req (k : String) : IO (Option String) := do
    match ← IO.getEnv k with
    | some v => pure (some v)
    | none => do IO.eprintln s!"interop: missing environment variable {k}"; pure none
  let some transport ← req "transport" | pure none
  let some muxer ← req "muxer" | pure none
  let some security ← req "security" | pure none
  let some isDialerStr ← req "is_dialer" | pure none
  let some isDialer :=
    (if isDialerStr == "true" then some true
     else if isDialerStr == "false" then some false else none) | do
      IO.eprintln s!"interop: bad is_dialer {isDialerStr}"; pure none
  let ip ← envDflt "ip" "0.0.0.0"
  let redisAddr ← envDflt "redis_addr" "redis:6379"
  let timeoutStr ← envDflt "test_timeout_seconds" "180"
  let timeoutSecs := (timeoutStr.toNat?).getD 180
  pure (some { transport := transport, muxer := muxer, security := security
               isDialer := isDialer, ip := ip, redisAddr := redisAddr
               timeoutSecs := timeoutSecs })

def randomIdentity : IO (Option Keys.PrivKey) := do
  let some seed ← OpenSsl.randomBytes 32 | return none
  return some { keyType := .ed25519, raw := seed }

/-- The node the test plan asks for: the configured transport, security
and muxer, serving `/ipfs/ping/1.0.0`. -/
def buildNode (cfg : InteropCfg) : IO (Option Host) := do
  unless cfg.transport == "tcp" do
    IO.eprintln s!"interop: transport {cfg.transport} not implemented (phase 5 remaining: ws, quic)"
    return none
  unless cfg.security == "noise" do
    IO.eprintln s!"interop: security {cfg.security} not implemented (phase 5 remaining: tls)"
    return none
  let muxers : List MuxChoice :=
    match cfg.muxer with
    | "yamux" => [YamuxChoice]
    | "mplex" => [MplexChoice]
    | _ => []
  if muxers.isEmpty then
    IO.eprintln s!"interop: muxer {cfg.muxer} not implemented (yamux/mplex only)"
    return none
  let some id ← randomIdentity | do IO.eprintln "interop: no randomness"; return none
  let some static ← OpenSsl.randomBytes 32 | do IO.eprintln "interop: no randomness"; return none
  let ipComps :=
    match Redis.parseIp4? cfg.ip with
    | some (a, b, c, d) => [AddrComponent.ip4 a b c d]
    | none => [AddrComponent.ip4 0 0 0 0]
  let listenAddr : Multiaddr := { components := ipComps ++ [AddrComponent.tcp 0] }
  Host.new { key := id, listenAddr := listenAddr } Tcp.transport
    [Noise.security id static (muxers.map (·.name))] muxers

/-- The ip to advertise: the configured one, or - when the runner passed
the default 0.0.0.0 - the interface address the redis connection used
(the redis server is by definition reachable from both harness sides). -/
def advertisedIp (cfg : InteropCfg) (redis : Redis.Client) : String :=
  if cfg.ip != "0.0.0.0" then cfg.ip
  else match redis.conn.localAddr.components with
    | [AddrComponent.ip4 a b c d, _] => s!"{a}.{b}.{c}.{d}"
    | _ => "127.0.0.1"

/-- Listener: bind, publish the dialable multiaddr on the `listenerAddr`
list, serve pings until the test timeout, then exit nonzero (the runner
kills us earlier on success). -/
def listenerMode (cfg : InteropCfg) : IO UInt32 := do
  let some redis ← Redis.connect? cfg.redisAddr | do
    IO.eprintln s!"interop: redis connect failed ({cfg.redisAddr})"; return 1
  let some h ← buildNode cfg | do redis.close; return 1
  h.setStreamHandler Ping.protocol Ping.handle
  let some _ ← h.listen | do
    IO.eprintln "interop: listen failed"; h.close; redis.close; return 1
  let port := match (← h.listeners.get).head? with
    | some l => match l.addr.components.getLast? with
      | some (.tcp p) => p
      | _ => 0
    | none => 0
  let addrStr :=
    s!"/ip4/{advertisedIp cfg redis}/tcp/{port}/p2p/{PeerId.toBase58 h.id}"
  match ← Redis.rpush redis "listenerAddr" addrStr with
  | some _ => IO.eprintln s!"interop: listening at {addrStr}"
  | none => do
    IO.eprintln "interop: redis RPUSH failed"
    h.close
    redis.close
    return 1
  IO.sleep ((cfg.timeoutSecs * 1000).toUInt32)
  IO.eprintln "interop: test timeout hit"
  h.close
  redis.close
  return 1

/-- Dialer: fetch the listener addr, dial + handshake + one ping, print
the timing JSON. Times are whole milliseconds. -/
def dialerMode (cfg : InteropCfg) : IO UInt32 := do
  let some redis ← Redis.connect? cfg.redisAddr | do
    IO.eprintln s!"interop: redis connect failed ({cfg.redisAddr})"; return 1
  match ← Redis.blpop redis "listenerAddr" cfg.timeoutSecs with
  | none => do
    IO.eprintln "interop: no listener address (BLPOP timeout)"
    redis.close
    return 1
  | some addrStr => do
    IO.eprintln s!"interop: dialing {addrStr}"
    let some addr := Multiaddr.parse? addrStr | do
      IO.eprintln s!"interop: bad multiaddr {addrStr}"; return 1
    let t0 ← IO.monoMsNow
    let some h ← buildNode cfg | return 1
    let some sess ← h.dial addr none | do
      IO.eprintln "interop: dial failed"; return 1
    let some s ← Host.openProto sess Ping.protocol | do
      IO.eprintln "interop: ping stream failed"; return 1
    let payload ← match ← OpenSsl.randomBytes 32 with
      | some b => pure b
      | none => pure (Bytes.ofNatList (List.replicate 32 0x42))
    match ← Ping.ping s payload with
    | none => do IO.eprintln "interop: ping failed"; return 1
    | some rtt => do
      let total ← IO.monoMsNow
      -- keys verbatim from the test plan (including its `pingRTTMilllis` typo)
      IO.print ("{\"handshakePlusOneRTTMillis\": " ++ toString (total - t0)
        ++ ", \"pingRTTMilllis\": " ++ toString rtt ++ "}\n")
      (← IO.getStdout).flush
      s.close
      h.close
      redis.close
      return 0

def main : IO UInt32 := do
  match ← readCfg with
  | none => return 2
  | some cfg => if cfg.isDialer then dialerMode cfg else listenerMode cfg
