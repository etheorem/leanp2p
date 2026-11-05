import Tests.Support
import Streams
import Interop

/-!
# Interop suite (unit W5.9)

The in-suite checks of `packages/cli/docs/PLAN.md`, "Test milestones
(unit 2)": the parts of the harness that run without a peer. The live
matrix runs outside the suite, in `scripts/interop-matrix.sh`.

* The configuration, read from a table in place of the environment, and
  the timing record with the test plan's keys.
* The RESP2 header parse and its caps.
* The Redis client against a scripted server over the sim transport. The
  server's reply waits in the pipe before the client sends its command,
  so no answer depends on the order of the two tasks. Each exchange runs
  with whole writes and again in the byte-splitting mode, which drives
  the line reader's `fill` loop one byte at a time.
* The CRLF scan of the production path, pinned to its model.
* The address the listener publishes.
-/

set_option autoImplicit false

namespace Tests.Interop

open Conc (Async)
open Streams (Connection)
open _root_.Interop
open _root_.Interop.Resp (maxReplyBytes)

/-! ## The configuration -/

/-- A lookup over a table, in place of the environment. -/
private def envOf (table : List (String × String)) : String → Option String :=
  fun k => table.lookup k

/-- The variables of a valid run. -/
private def base : List (String × String) :=
  [("transport", "tcp"), ("security", "noise"), ("muxer", "yamux"),
   ("redis_addr", "10.0.0.5:6379")]

private def configChecks (r : Runner) : IO Unit := do
  match Config.parse (envOf base) with
  | .ok c =>
    r.check "config: is_dialer absent picks the listener" (!c.isDialer)
    r.check "config: ip absent listens on 0.0.0.0, port 0"
      (c.listenAddr.describe == "/ip4/0.0.0.0/tcp/0")
    r.check "config: redis_addr reads as a TCP address" (c.redisAddr.describe == "/ip4/10.0.0.5/tcp/6379")
    r.check "config: the timeout defaults to 180 s" (c.timeoutSec == 180)
    r.check "config: yamux" (c.muxer == .yamux)
  | .error e => r.check s!"config: a valid table parses ({e})" false
  match Config.parse (envOf (("is_dialer", "true") :: ("muxer", "mplex") :: ("ip", "127.0.0.1") ::
      ("test_timeout_seconds", "30") :: base)) with
  | .ok c =>
    r.check "config: is_dialer=true picks the dialer" c.isDialer
    r.check "config: mplex" (c.muxer == .mplex)
    r.check "config: ip" (c.listenAddr.describe == "/ip4/127.0.0.1/tcp/0")
    r.check "config: test_timeout_seconds" (c.timeoutSec == 30)
  | .error e => r.check s!"config: the dialer table parses ({e})" false
  match Config.parse (envOf (("test_timeout_seconds", "soon") :: base)) with
  | .ok c => r.check "config: a timeout that is no numeral keeps the default, as go does" (c.timeoutSec == 180)
  | .error e => r.check s!"config: a bad timeout still parses ({e})" false
  -- Each unsupported value, and each address the harness cannot take,
  -- is an error.
  for (k, v) in [("transport", "quic-v1"), ("security", "tls"), ("muxer", "mux9"),
      ("redis_addr", "redis:6379"), ("redis_addr", "10.0.0.5"), ("ip", "::1")] do
    r.check s!"config: {k}={v} is an error"
      ((Config.parse (envOf ((k, v) :: base.filter (·.1 != k)))) matches .error _)
  r.check "config: transport absent is an error"
    ((Config.parse (envOf (base.filter (·.1 != "transport")))) matches .error _)

private def recordChecks (r : Runner) : IO Unit := do
  r.check "record: microseconds print as milliseconds with three decimals"
    (Config.millis 12345 == "12.345" && Config.millis 7 == "0.007" && Config.millis 0 == "0.000")
  r.check "record: the keys of the test plan, verbatim"
    (Config.timingJson 2000 1001 == "{\"handshakePlusOneRTTMillis\":2.000,\"pingRTTMilllis\":1.001}")

/-! ## RESP2 -/

/-- The model bytes of a string. -/
private def nat (s : String) : List Nat := Bytes.toNatList s.toUTF8

private def respChecks (r : Runner) : IO Unit := do
  r.check "resp: +PONG" (Resp.parseHeader (nat "+PONG") matches .ok (.simple "PONG"))
  r.check "resp: -ERR" (Resp.parseHeader (nat "-ERR x") matches .ok (.error "ERR x"))
  r.check "resp: :-12" (Resp.parseHeader (nat ":-12") matches .ok (.integer (-12)))
  r.check "resp: :+3" (Resp.parseHeader (nat ":+3") matches .ok (.integer 3))
  r.check "resp: $5" (Resp.parseHeader (nat "$5") matches .ok (.bulk (some 5)))
  r.check "resp: $-1 is the null bulk string" (Resp.parseHeader (nat "$-1") matches .ok (.bulk none))
  r.check "resp: *-1 is the null array" (Resp.parseHeader (nat "*-1") matches .ok (.array none))
  r.check "resp: *2" (Resp.parseHeader (nat "*2") matches .ok (.array (some 2)))
  -- The caps: a bulk length one over, and an array of three.
  r.check "resp: a bulk length over the cap is tooLong"
    (Resp.parseHeader (nat s!"${maxReplyBytes + 1}") matches .error .tooLong)
  r.check "resp: a bulk length at the cap passes"
    (Resp.parseHeader (nat s!"${maxReplyBytes}") matches .ok (.bulk (some _)))
  r.check "resp: an array of three is tooLong" (Resp.parseHeader (nat "*3") matches .error .tooLong)
  for bad in ["$", "$x", "$-2", ":", ":1a", "?1", ""] do
    r.check s!"resp: {bad.quote} is malformed" (Resp.parseHeader (nat bad) matches .error (.malformed _))
  r.check "resp: a command is an array of bulk strings"
    (Resp.encodeCommand [nat "RPUSH", nat "k", nat "v1"] ==
      nat "*3\r\n$5\r\nRPUSH\r\n$1\r\nk\r\n$2\r\nv1\r\n")

/-- The production CRLF scan agrees with the model on every sample:
dense in CR and LF, at every length up to 64. -/
private def crlfChecks (r : Runner) : IO Unit := do
  let alphabet : List Nat := [13, 10, 97]
  let mut ok := true
  for n in [0:65] do
    for seed in [0:9] do
      let l : List Nat := (List.range n).map fun i => alphabet[(i * (seed + 1) + seed + i / 3) % 3]!
      if Redis.crlfAtB? (Bytes.ofNatList l) != Redis.crlfAt? l then ok := false
  r.check "resp: the ByteArray CRLF scan answers as its model" ok

/-! ## The Redis client over the sim -/

/-- A connected sim pair: the client's end and the server's end. -/
private def pair (split : Bool) : Async (Connection × Connection) := do
  let net ← Streams.Sim.Net.new split
  let some addr := (Multiformats.Multiaddr.parse? "/memory/6379").toOption
    | throw <| IO.userError "the test address does not parse"
  let l ← net.transport.listen addr
  let some c ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
  let some s ← l.accept | throw <| IO.userError "accept failed"
  l.close
  return (c, s)

/-- Every byte until the end of the stream. -/
private partial def readAll (c : Connection) (acc : ByteArray := .empty) : Async ByteArray := do
  -- Park: the peer's close ends it with `none`.
  match ← c.read with
  | some chunk => readAll c (acc ++ chunk)
  | none => return acc

/-- Queue the server's `reply`, run `act` on a client, then answer what
the client sent. -/
private def exchange {α : Type} (split : Bool) (reply : ByteArray) (act : Redis.Client → Async α) :
    Async (α × ByteArray) := do
  let (c, s) ← pair split
  s.write reply
  let a ← act (Redis.Client.new c)
  c.close
  let sent ← readAll s
  s.close
  return (a, sent)

/-- The bytes of the `PING` command. -/
private def pingCommand : ByteArray := "*1\r\n$4\r\nPING\r\n".toUTF8

/-- A server that takes the client's `PING`, sends `reply`, and closes.
It reads the command first, so the client's write never meets a closed
connection, in every order of the two tasks. -/
private def hangUp {α : Type} (split : Bool) (reply : ByteArray) (act : Redis.Client → Async α) :
    Async α := do
  let (c, s) ← pair split
  let server ← Conc.TaskSet.new
  server.spawn do
    -- Park: the client's command wakes it, and so does the client's close.
    discard <| s.readExactly pingCommand.size
    s.write reply
    s.close
  let a ← act (Redis.Client.new c)
  c.close
  server.joinAll
  return a

private def clientChecks (r : Runner) (split : Bool) : Async Unit := do
  let mode := if split then " (byte-splitting)" else ""
  let (a, sent) ← exchange split "+PONG\r\n".toUTF8 (·.ping)
  r.check s!"redis: PING reads +PONG{mode}" (a matches .ok _)
  r.check s!"redis: PING goes as an array of one bulk string{mode}"
    (sent.toList == "*1\r\n$4\r\nPING\r\n".toUTF8.toList)
  let (a, sent) ← exchange split ":1\r\n".toUTF8 (·.rpush "listenerAddr" "/ip4/1.2.3.4/tcp/5")
  r.check s!"redis: RPUSH reads the list length{mode}" (a matches .ok _)
  r.check s!"redis: RPUSH sends the key and the value{mode}"
    (sent.toList == "*3\r\n$5\r\nRPUSH\r\n$12\r\nlistenerAddr\r\n$18\r\n/ip4/1.2.3.4/tcp/5\r\n".toUTF8.toList)
  let (a, sent) ← exchange split "*2\r\n$12\r\nlistenerAddr\r\n$4\r\n/a/b\r\n".toUTF8
    (·.blpop "listenerAddr" 30)
  r.check s!"redis: BLPOP reads the value{mode}" (a matches .ok (some "/a/b", _))
  r.check s!"redis: BLPOP sends the key and the timeout in seconds{mode}"
    (sent.toList == "*3\r\n$5\r\nBLPOP\r\n$12\r\nlistenerAddr\r\n$2\r\n30\r\n".toUTF8.toList)
  let (a, _) ← exchange split "*-1\r\n".toUTF8 (·.blpop "listenerAddr" 1)
  r.check s!"redis: BLPOP reads the null array as the timeout{mode}" (a matches .ok (none, _))
  let (a, _) ← exchange split "-ERR boom\r\n".toUTF8 (·.ping)
  r.check s!"redis: an error reply is Error.server{mode}" (a matches .error (.server "ERR boom"))
  let (a, _) ← exchange split ":1\r\n".toUTF8 (·.ping)
  r.check s!"redis: a PING answer other than PONG is unexpected{mode}" (a matches .error (.unexpected _))
  let (a, _) ← exchange split "*2\r\n:1\r\n:2\r\n".toUTF8 (·.blpop "k" 1)
  r.check s!"redis: an array element that is no bulk string is unexpected{mode}"
    (a matches .error (.unexpected _))
  let (a, _) ← exchange split s!"${maxReplyBytes + 1}\r\n".toUTF8 (·.blpop "k" 1)
  r.check s!"redis: a bulk over the cap is tooLong before its body{mode}" (a matches .error .tooLong)
  let (a, _) ← exchange split "*3\r\n".toUTF8 (·.blpop "k" 1)
  r.check s!"redis: an array over the cap is tooLong before its elements{mode}" (a matches .error .tooLong)
  let (a, _) ← exchange split "*2\r\n$1\r\nkXY".toUTF8 (·.blpop "k" 1)
  r.check s!"redis: a bulk string without its CRLF is malformed{mode}" (a matches .error (.malformed _))
  let a ← hangUp split "+PO".toUTF8 (·.ping)
  r.check s!"redis: a reply cut by the server's close is closed{mode}" (a matches .error .closed)

/-- A line of `maxReplyBytes + 2` bytes with no CRLF: the reader stops
there and takes no further chunk. Whole writes only: the byte-splitting
mode would deliver six million chunks. -/
private def lineCapCheck (r : Runner) : Async Unit := do
  let long := ByteArray.mk (Array.replicate (maxReplyBytes + 2) 97)
  let a ← hangUp false ("+".toUTF8 ++ long) (·.ping)
  r.check "redis: a line over the cap is tooLong" (a matches .error .tooLong)

/-! ## The published address -/

private def addrChecks (r : Runner) : IO Unit := do
  let parse (s : String) : IO Multiformats.Multiaddr := do
    match Multiformats.Multiaddr.parse? s with
    | .ok a => pure a
    | .error _ => throw <| IO.userError s!"{s} does not parse"
  let any ← parse "/ip4/0.0.0.0/tcp/4001"
  let fixed ← parse "/ip4/192.168.1.9/tcp/4001"
  let redisLocal ← parse "/ip4/172.18.0.1/tcp/51000"
  let peer : Mock.PeerId := ⟨"12D3KooWExample"⟩
  r.check "address: 0.0.0.0 takes the IP of the Redis connection, and keeps the port"
    (publishedAddr any redisLocal peer matches .ok "/ip4/172.18.0.1/tcp/4001/p2p/12D3KooWExample")
  r.check "address: a concrete IP stays"
    (publishedAddr fixed redisLocal peer matches .ok "/ip4/192.168.1.9/tcp/4001/p2p/12D3KooWExample")

def run (r : Runner) : IO Unit := do
  r.section "interop" "(packages/cli/docs/PLAN.md, test milestones, unit 2)"
  configChecks r
  recordChecks r
  respChecks r
  crlfChecks r
  addrChecks r
  Conc.Async.run do
    clientChecks r false
    clientChecks r true
    lineCapCheck r

end Tests.Interop
