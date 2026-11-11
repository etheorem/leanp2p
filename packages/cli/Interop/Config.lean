import Multiformats

/-!
# The harness configuration and the timing record

The test runner passes the configuration as environment variables (the
transport-interop test plan, "Test spec"). This module reads them into a
`Config`, and it renders the dialer's one line of output, the timing
record (the test plan, "Dialer" step 8). Both are pure: `parse` takes
the variable lookup as a function, so the suite runs it on a table.

The names, the defaults, and the record keys are the test plan's,
verbatim. go-libp2p's test-plan peer reads the same variables
(`vendor/go-libp2p/test-plans/cmd/ping/main.go`, lines 36 to 60). The
record key `pingRTTMilllis` keeps the test plan's three `l`s, because
the runner compares the keys literally.

## What the harness supports

The gate runs `tcp + /noise + yamux` (root PLAN W5.9). The parse also
reads `mplex`, the second muxer of root §4.9. `libp2p/mux` holds no
mplex value yet (P2, the mux PLAN, unit 2), so the host start refuses
it. Any other transport, security, or muxer name is a configuration
error. On every refusal the binary exits nonzero (the test plan: "On
error, the dialer should return a non-zero exit code").

`ip` and `redis_addr` take literal IPv4 addresses. The TCP transport
dials and listens on `/ip4` and `/ip6` only (the streams ARCHITECTURE,
"Public surface"), and root §4.1 keeps `Std.Async`, and so its DNS
resolver, out of every package but `base/conc`. A host name, the test
plan's default `redis` among them, is a configuration error.
-/

set_option autoImplicit false

namespace Interop.Config

/-! ## The names of the test plan -/

/-- The variable that names the transport. -/
def transportVar : String := "transport"
/-- The variable that names the muxer. -/
def muxerVar : String := "muxer"
/-- The variable that names the security protocol. -/
def securityVar : String := "security"
/-- The variable that picks the dialer (`true`) or the listener. -/
def isDialerVar : String := "is_dialer"
/-- The variable that names the listen address. -/
def ipVar : String := "ip"
/-- The variable that names the Redis server. -/
def redisAddrVar : String := "redis_addr"
/-- The variable that gives the test timeout, in seconds. -/
def timeoutVar : String := "test_timeout_seconds"

/-- The listen address when `ip` is absent. -/
def defaultIp : String := "0.0.0.0"
/-- The Redis server when `redis_addr` is absent. -/
def defaultRedisAddr : String := "redis:6379"
/-- The timeout when `test_timeout_seconds` is absent or no numeral, in
seconds. -/
def defaultTimeoutSec : Nat := 180

/-- The Redis list that carries the listener's address. -/
def listenerAddrKey : String := "listenerAddr"

/-! ## The configuration -/

/-- The two muxers of root §4.9. -/
inductive Muxer where
  /-- `/yamux/1.0.0`, the muxer of the gate. -/
  | yamux
  /-- `/mplex/6.7.0`. -/
  | mplex
  deriving DecidableEq, Repr

/-- The parsed configuration of one harness run. -/
structure Config where
  /-- The muxer to offer. -/
  muxer : Muxer
  /-- `true` for the dialer, `false` for the listener. -/
  isDialer : Bool
  /-- The address to listen on, with port 0. -/
  listenAddr : Multiformats.Multiaddr
  /-- The address of the Redis server. -/
  redisAddr : Multiformats.Multiaddr
  /-- The test timeout, in seconds. -/
  timeoutSec : Nat

/-- The TCP multiaddr of a literal IPv4 address and a port. -/
def tcpAddr? (ip : String) (port : String) : Except String Multiformats.Multiaddr :=
  match Multiformats.Multiaddr.parse? s!"/ip4/{ip}/tcp/{port}" with
  | .ok a => .ok a
  | .error _ => .error s!"{ip}:{port} is no IPv4 address and TCP port"

/-- `redis_addr` as `<ipv4>:<port>`. The port is the text after the last
colon. -/
def redisAddr? (text : String) : Except String Multiformats.Multiaddr :=
  match text.splitOn ":" with
  | [host, port] =>
    (tcpAddr? host port).mapError fun _ =>
      s!"{redisAddrVar}={text}: the harness takes a literal IPv4 address and a port"
  | _ => .error s!"{redisAddrVar}={text}: expected <ipv4>:<port>"

/-- The configuration from the variable lookup `env`. -/
def parse (env : String → Option String) : Except String Config := do
  match env transportVar with
  | some "tcp" => pure ()
  | other => throw s!"{transportVar}={other.getD ""}: the harness supports tcp only"
  match env securityVar with
  | some "noise" => pure ()
  | other => throw s!"{securityVar}={other.getD ""}: the harness supports noise only"
  let muxer ← match env muxerVar with
    | some "yamux" => pure Muxer.yamux
    | some "mplex" => pure Muxer.mplex
    | other => throw s!"{muxerVar}={other.getD ""}: the harness supports yamux and mplex"
  let listenAddr ← tcpAddr? ((env ipVar).getD defaultIp) "0"
  let redisAddr ← redisAddr? ((env redisAddrVar).getD defaultRedisAddr)
  -- The go peer keeps the default when the value is no numeral (lines 46
  -- to 52 of its `main.go`), and so does the harness.
  let timeoutSec := ((env timeoutVar).bind String.toNat?).getD defaultTimeoutSec
  return { muxer, isDialer := env isDialerVar == some "true", listenAddr, redisAddr, timeoutSec }

/-! ## The timing record -/

/-- A duration in microseconds as milliseconds, with three decimals.
The test plan asks for milliseconds "as a float"; go prints its
microsecond count over 1000 the same way. -/
def millis (us : Nat) : String :=
  let frac := toString (us % 1000)
  s!"{us / 1000}." ++ "".pushn '0' (3 - frac.length) ++ frac

/-- The dialer's output line: the two durations under the test plan's
keys, verbatim. -/
def timingJson (handshakePlusOneRttUs pingRttUs : Nat) : String :=
  "{\"handshakePlusOneRTTMillis\":" ++ millis handshakePlusOneRttUs ++
    ",\"pingRTTMilllis\":" ++ millis pingRttUs ++ "}"

#guard millis 12345 == "12.345"
#guard millis 7 == "0.007"
#guard timingJson 1500 250 == "{\"handshakePlusOneRTTMillis\":1.500,\"pingRTTMilllis\":0.250}"

end Interop.Config
