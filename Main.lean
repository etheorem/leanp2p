import LeanP2P

/-!
# End-to-end demo (phase 4)

Two full hosts on loopback TCP (phase 4 steps 23-24): both upgrade
connections the libp2p way - multistream-select negotiates `/noise`, the
Noise XX handshake authenticates identities, multistream-select negotiates
`/yamux/1.0.0` - then dial by PeerId through the peerstore and run ping,
identify and echo over the muxed session.

Run with `lake build && ./.lake/build/bin/demo` (add `+RTS -N4 -RTS` for
multiple capabilities; everything also works with one).
-/

open LeanP2P

/-- A fresh Ed25519 identity (real nodes generate keys; the spike used
seed strings). -/
def randomIdentity : IO (Option Keys.PrivKey) := do
  let some seed ← OpenSsl.randomBytes 32 | return none
  return some { keyType := .ed25519, raw := seed }

def main : IO UInt32 := do
  let addr :=
    match Multiaddr.parse? "/ip4/127.0.0.1/tcp/0" with
    | some a => a
    | none => { components := [] }

  /- Host A: the listener (real keys; the Noise handshake needs a fresh
  static X25519 key per host). -/
  let some idA ← randomIdentity | do IO.eprintln "no randomness"; return 1
  let some idB ← randomIdentity | do IO.eprintln "no randomness"; return 1

  let mkHost (key : Keys.PrivKey) : IO (Option Host) := do
    let some static ← OpenSsl.randomBytes 32 | return none
    Host.new { key := key, listenAddr := addr } Tcp.transport
      [Noise.security key static] [YamuxChoice, MplexChoice]

  let some hA ← mkHost idA | do IO.eprintln "host A init failed"; return 1
  let some hB ← mkHost idB | do IO.eprintln "host B init failed"; return 1

  hA.setStreamHandler Ping.protocol Ping.handle
  hA.setStreamHandler Identify.protocol fun s => do
    let some pub ← idA.publicKey | s.close
    Identify.respondAndSend pub (← hA.addrs) [Ping.protocol, Identify.protocol]
      none "leanp2p" s
  hA.setStreamHandler "/demo/echo/1.0.0" fun s => do
    match ← s.read with
    | none => s.close
    | some b => do s.write b; s.close

  let some _ ← hA.listen | do IO.eprintln "listen failed"; return 1
  let some lA := (← hA.listeners.get).head? | do IO.eprintln "no listener"; return 1

  /- Host B dials A by PeerId through the peerstore. -/
  hB.peerstore.addAddrs hA.id [lA.addr]
  let some sess ← hB.dialPeer hA.id | do IO.eprintln "dial failed"; return 1
  IO.println s!"dialed {PeerId.toBase58 hA.id} (noise + yamux, remote verified)"

  /- Ping over the negotiated session. -/
  match ← hB.newStreamTo hA.id Ping.protocol with
  | none => IO.eprintln "ping stream failed"; return 1
  | some s => do
    let payload ← match ← OpenSsl.randomBytes 32 with
      | some b => pure b
      | none => pure (Bytes.ofNatList (List.replicate 32 0x42))
    match ← Ping.ping s payload with
    | none => IO.eprintln "ping failed"; return 1
    | some ms => IO.println s!"ping rtt: {ms} ms"
    s.close

  /- Identify: the responder's key derives the peer id we dialed. -/
  match ← hB.newStreamTo hA.id Identify.protocol with
  | none => IO.eprintln "identify stream failed"; return 1
  | some s => do
    match ← Identify.request s with
    | none => IO.eprintln "identify failed"; return 1
    | some (msg, pid) =>
      IO.println s!"identified: {PeerId.toBase58 pid}, {msg.listenAddrs.length} addr(s), {msg.protocols.length} protocol(s)"

  /- Echo. -/
  match ← hB.newStreamTo hA.id "/demo/echo/1.0.0" with
  | none => IO.eprintln "echo stream failed"; return 1
  | some s => do
    s.write (Bytes.ofString "echo-me")
    match ← s.read with
    | none => IO.eprintln "echo failed"; return 1
    | some b => IO.println s!"echo: {(Bytes.toString? b).getD "<binary>"}"
    s.close

  /- Shutdown joins every task. -/
  hB.close
  hA.close
  return 0
