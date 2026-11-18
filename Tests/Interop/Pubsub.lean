import Conc
import Streams
import Libp2p.Identity
import Libp2p.Core
import Libp2p.Host
import Libp2p.Mux
import Libp2p.Security.Noise
import Libp2p.Protocols.Identify
import Libp2p.Protocols.Gossipsub.HostSeam
import Libp2p.Protocols.Gossipsub.Node

/-!
# The gossipsub interop driver

The Lean side of `scripts/pubsub-interop.sh`: our gossipsub node on our
host, over loopback TCP with Noise and yamux, against a go-libp2p-pubsub
v0.19.0 node (`scripts/pubsub-interop/`).

* `pubsub-interop dial ADDR BURST`: dial the go node at ADDR.
* `pubsub-interop listen BURST`: listen, and wait for the go node to
  dial us.

Either mode prints `ADDR <multiaddr>/p2p/<id>` once it listens. It then
subscribes to `BURST` filler topics, and then to the topic `interop`,
as a consensus node subscribes to many topics at once. A burst past the
queue of a peer drops subscription records, so the go node learns
`interop` only when our node sends them again. Our node publishes
`from-lean-<n>` every 200 ms, and prints `LEAN-GOT <data>` for each
message from go. At the end it prints `DROPPED <n>`, the frames that a
full queue dropped. It exits 0 once a message with the prefix `from-go`
arrives, and 1 after 40 s. The script checks that the go node got ours.

The message policy is the go node's: no author, no signature, and the
message id from the data. Those are the defaults of `Core.defaults`.
-/

set_option autoImplicit false

namespace Tests.Interop.Pubsub

open Conc (Async Chan Clock)
open Libp2p.Identity Libp2p.Core
open Libp2p.Protocols Libp2p.Protocols.Gossipsub

/-- The topic of the check. -/
def topic : TopicId := ⟨"interop"⟩

/-- Fail with a message. -/
def fail {α : Type} (msg : String) : Async α :=
  throw <| IO.userError s!"pubsub-interop: {msg}"

/-- The value of an `Except`, or a failure that names the error. -/
def orFail {ε α : Type} [Repr ε] (what : String) : Except ε α → Async α
  | .ok a => return a
  | .error e => fail s!"{what}: {(repr e).pretty}"

/-- A multiaddr from its text form. -/
def addr (s : String) : Async Multiformats.Multiaddr :=
  orFail s!"address {s}" (Multiformats.Multiaddr.parse? s)

/-- Sleep on the system clock. -/
def sleep (ms : Nat) : Async Unit := do
  let timer ← (Clock.system.after ms : BaseIO (Conc.Park Unit))
  discard <| Conc.select #[timer]

/-- Print a line and flush it, so the script reads it while we run. -/
def say (line : String) : Async Unit := do
  let out ← (IO.getStdout : IO IO.FS.Stream)
  out.putStrLn line
  out.flush

/-- Our identity: the Ed25519 key of 32 bytes of `L`. -/
def leanKey : Async PrivKey :=
  orFail "key" (PrivKey.ofData? .ed25519 ⟨Array.replicate 32 'L'.toNat.toUInt8⟩)

/-- Run one check: `dialTo` is the go node's address, or `none` to wait
for its dial. -/
def check (dialTo : Option String) (burst : Nat) : Async Unit := do
  let key ← leanKey
  let noise ← orFail "noise" (← (Libp2p.Security.Noise.Config.generate key).run)
  let pub ← orFail "public key" key.toPublic
  -- Identify names meshsub: go-libp2p-pubsub adds a peer only after
  -- identify reports a protocol that its router speaks.
  let protocols := [Identify.protocolId.toString, Constants.meshsubId.toString]
  let host ← orFail "host" (← (Libp2p.Host.Host.new {
    identity := key
    transports := [Streams.Tcp.transport]
    security := [Libp2p.Security.Noise.securityProtocol noise]
    muxers := [Libp2p.Mux.yamux]
    handlers := [Identify.respondHandler pub [] protocols "leanp2p"] } : BaseIO _))
  let node ← (Node.start (HostSeam.ofHost host) {} : BaseIO Node.Node)
  let bound ← orFail "listen" (← host.startListening (← addr "/ip4/127.0.0.1/tcp/0"))
  say s!"ADDR {bound.describe}/p2p/{host.localPeer}"
  if let some text := dialTo then
    let peer ← orFail "dial" (← host.dial (← addr text))
    if !(← (node.peerJoined peer .meshsub : BaseIO Bool)) then fail "the join was refused"
  -- The burst, then the topic of the check.
  for i in [0:burst] do
    discard <| node.subscribeWait ⟨s!"filler-{i}"⟩ (fun _ => pure ())
  let got : Chan String ← (Chan.new 256 : BaseIO (Chan String))
  let subscribed ← node.subscribeWait topic fun m =>
    discard <| got.trySend ((String.fromUTF8? (Bytes.ofNatList (m.data.getD []))).getD "")
  if !subscribed then fail "the subscribe was refused"
  let mut fromGo := false
  for n in [0:200] do
    discard <| (node.publish topic s!"from-lean-{n}".toUTF8 : BaseIO Bool)
    sleep 200
    repeat
      match ← (got.tryRecv : BaseIO (Option String)) with
      | some d =>
        say s!"LEAN-GOT {d}"
        if d.startsWith "from-go" then fromGo := true
      | none => break
    -- Publish a few rounds more, so the go node gets ours too.
    if fromGo && 10 ≤ n then break
  -- The frames that a full queue dropped: with a burst past the queue,
  -- the subscription records among them came back (`Node.enqueue`).
  say s!"DROPPED {← (node.dropped : BaseIO Nat)}"
  node.stop
  Libp2p.Host.Host.close host
  if !fromGo then fail "no message from go within 40 s"
  say "DONE"

end Tests.Interop.Pubsub

open Tests.Interop.Pubsub in
def main (args : List String) : IO UInt32 := do
  let run (dialTo : Option String) (burst : String) : IO UInt32 := do
    match burst.toNat? with
    | none =>
      IO.eprintln s!"pubsub-interop: burst {burst} is not a number"
      return 2
    | some n =>
      try
        Conc.Async.run (check dialTo n)
        return 0
      catch e =>
        IO.eprintln (toString e)
        return 1
  match args with
  | ["dial", target, burst] => run (some target) burst
  | ["listen", burst] => run none burst
  | _ =>
    IO.eprintln "usage: pubsub-interop dial ADDR BURST | listen BURST"
    return 2
