import Streams
import Libp2p.Security

/-!
# The Noise interop driver (unit W5.3)

The Lean side of the Noise interop check against go-libp2p v0.50.0's
Noise transport, with flynn/noise v1.1.0 under it.
`scripts/noise-interop.sh` builds the go side (`scripts/noise-interop/`)
and runs both directions over loopback TCP, with no multistream-select,
so the check sees the Noise handshake and transport frames alone. The
full stack meets go-libp2p at W5.9.

* `noise-interop listen`: listen, print the port, accept one connection
  as the responder, read `size` bytes, echo them, and then read the
  peer's orderly end.
* `noise-interop dial PORT`: connect as the initiator, write `size`
  bytes, check the echo, and close.

Both sides take fixed Ed25519 identities from 32-byte seeds, so each
side checks the peer id the other proves. The Noise static key comes
from `Config.generate`, as in production.

The driver lives outside `lake test`, which stays hermetic: Go tooling
is test-only and confined to the harness (CLAUDE.md, "Dependencies").
The payload pattern matches the go side.
-/

set_option autoImplicit false

namespace Tests.Interop.Noise

open Conc (Async)
-- The keys and the peer id come from the identity mock of the package
-- until W5.1 merges (RULES.md, "Working ahead of the tree").
open Libp2p.Security.Mock.Identity
open Libp2p.Security

/-- 32 bytes of one value, the form of both identity seeds. -/
def seed (v : UInt8) : ByteArray := ⟨Array.replicate 32 v⟩

/-- Our identity seed: 32 bytes of `L`. The go side holds the same. -/
def leanSeed : ByteArray := seed 'L'.toNat.toUInt8

/-- The go side's identity seed: 32 bytes of `G`. -/
def goSeed : ByteArray := seed 'G'.toNat.toUInt8

/-- The bytes each way: past three full frames of `maxPlaintext`, so a
write goes out as four frames. -/
def size : Nat := 200000

/-- The pattern both sides build. -/
def payload (n : Nat) : ByteArray :=
  ⟨(Array.range n).map fun k => UInt8.ofNat ((k * 7 + 3) % 251)⟩

/-- Fail with a message. -/
def fail {α : Type} (msg : String) : Async α :=
  throw <| IO.userError s!"lean: {msg}"

/-- The value of an `Except`, or a failure that names the error. -/
def orFail {ε α : Type} [ToString ε] (what : String) : Except ε α → Async α
  | .ok a => return a
  | .error e => fail s!"{what}: {e}"

/-- A multiaddr from its text form. -/
def addr (s : String) : Async Multiformats.Multiaddr := do
  orFail s!"address {s}" (Multiformats.Multiaddr.parse? s |>.mapError fun e => repr e |>.pretty)

/-- The Ed25519 key of a seed. -/
def keyOf (s : ByteArray) : Async PrivKey :=
  orFail "identity" (PrivKey.ofData? .ed25519 s |>.mapError fun e => (repr e).pretty)

/-- Our seam value, and the peer id the go side must prove. -/
def setup : Async (Mock.Core.SecurityProtocol × PeerId) := do
  let cfg ← orFail "static key"
    ((← (Noise.Config.generate (← keyOf leanSeed)).run).mapError fun e => (repr e).pretty)
  let goKey ← keyOf goSeed
  let want ← orFail "go peer id"
    ((do PeerId.ofPubKey (← goKey.toPublic) : Except Error PeerId) |>.mapError fun e => (repr e).pretty)
  return (Noise.securityProtocol cfg, want)

/-- Read until `n` bytes have arrived, or the end. -/
def readN (sc : Mock.Core.SecureConn) (n : Nat) : Async ByteArray := do
  let mut acc := ByteArray.empty
  while acc.size < n do
    match ← sc.read with
    | some b => acc := acc ++ b
    | none => break
  return acc

/-- The secure connection's answer, as a failure when it is an error. -/
def joinOk (sc : Mock.Core.SecureConn) : Async Unit := do
  orFail "join" (← sc.join.run)

/-- The listener side: the responder, then the echo, then the peer's
orderly end. -/
def listenMode : Async Unit := do
  let (proto, want) ← setup
  let l ← Streams.Tcp.transport.listen (← addr "/ip4/127.0.0.1/tcp/0")
  let some port := Streams.Tcp.socketAddress? l.addr |>.map (·.port) | fail "no port"
  IO.println port
  (← IO.getStdout).flush
  let some conn ← l.accept | fail "accept failed"
  l.close
  let sc ← orFail "handshake" (← (proto.handshake .responder conn .empty).run)
  unless sc.remotePeer == want do fail s!"remote peer {sc.remotePeer}, want {want}"
  let got ← readN sc size
  unless got.size == size do fail s!"read {got.size} bytes, want {size}"
  sc.write got
  -- The dialer closes after it has read the echo: an orderly end.
  if (← sc.read).isSome then fail "bytes after the echo, want the end"
  sc.close
  joinOk sc
  l.join

/-- The dialer side: the initiator, then the write and the echo. -/
def dialMode (port : String) : Async Unit := do
  let (proto, want) ← setup
  let some conn ← Streams.Tcp.transport.dial (← addr s!"/ip4/127.0.0.1/tcp/{port}") | fail "dial failed"
  let sc ← orFail "handshake" (← (proto.handshake .initiator conn .empty).run)
  unless sc.remotePeer == want do fail s!"remote peer {sc.remotePeer}, want {want}"
  let data := payload size
  sc.write data
  let got ← readN sc size
  unless got == data do fail s!"the echo of {size} bytes differs, got {got.size}"
  sc.close
  joinOk sc

end Tests.Interop.Noise

def main (args : List String) : IO UInt32 := do
  let run : Conc.Async Unit := match args with
    | ["listen"] => Tests.Interop.Noise.listenMode
    | ["dial", port] => Tests.Interop.Noise.dialMode port
    | _ => Tests.Interop.Noise.fail "usage: noise-interop listen | dial PORT"
  try
    run.run
    IO.eprintln "lean: ok"
    return 0
  catch e =>
    IO.eprintln s!"{e}"
    return 1
