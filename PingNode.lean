import LeanP2P

/-!
# pingnode — the phase 4 step 24 interop node

A minimal real node for the go-libp2p loopback ping evidence
(`scripts/ping-interop.sh`):

- `pingnode serve <port>` - host on `127.0.0.1:<port>`, upgrades inbound
  connections exactly like the demo (multistream `/noise`, Noise XX with
  extension-based muxer selection, yamux/mplex), serves `/ipfs/ping/1.0.0`
  and prints `ADDR <multiaddr> <peerid>`; exits when stdin closes.
- `pingnode dial <multiaddr>` - dials the peer (multiaddr with the
  `/p2p/<id>` suffix; the suffix is used as the expected identity),
  negotiates the stack, pings once, prints `PING OK rtt=<ms>ms`.
-/

open LeanP2P

def randomIdentity : IO (Option Keys.PrivKey) := do
  let some seed ← OpenSsl.randomBytes 32 | return none
  return some { keyType := .ed25519, raw := seed }

def mkNode (addr : Multiaddr) (muxers : List MuxChoice) : IO (Option Host) := do
  let some id ← randomIdentity | return none
  let some static ← OpenSsl.randomBytes 32 | return none
  Host.new { key := id, listenAddr := addr } Tcp.transport
    [Noise.security id static (muxers.map (·.name))] muxers

def serveMode (port : Nat) : IO UInt32 := do
  let addr : Multiaddr :=
    { components := [AddrComponent.ip4 127 0 0 1, AddrComponent.tcp port] }
  let some h ← mkNode addr [YamuxChoice, MplexChoice] | do
    IO.eprintln "node init failed"; return 1
  h.setStreamHandler Ping.protocol Ping.handle
  h.setStreamHandler Identify.protocol fun s => do
    let some pub ← h.cfg.key.publicKey | s.close
    Identify.respondAndSend pub (← h.addrs) [Ping.protocol, Identify.protocol]
      none "leanp2p" s
  let some _ ← h.listen | do IO.eprintln "listen failed"; return 1
  let addrs ← h.addrs
  match addrs.head? with
  | none => IO.eprintln "no addrs"; return 1
  | some a => do
    IO.println s!"ADDR {Multiaddr.toString a} {PeerId.toBase58 h.id}"
    let stdout ← IO.getStdout
    stdout.flush
    -- the driver closes stdin to shut us down
    let stdin ← IO.getStdin
    let mut line ← stdin.getLine
    while !line.isEmpty do
      line ← stdin.getLine
    h.close
    return 0

def dialMode (addrStr : String) : IO UInt32 := do
  let some addr := Multiaddr.parse? addrStr | do
    IO.eprintln s!"bad multiaddr: {addrStr}"; return 1
  let some h ← mkNode { components := [] } [YamuxChoice, MplexChoice] | do
    IO.eprintln "node init failed"; return 1
  match ← h.dial addr none with
  | none => IO.eprintln "dial failed"; return 1
  | some sess => do
    match ← h.newStreamTo sess.remotePeer Ping.protocol with
    | none => IO.eprintln "ping stream failed"; return 1
    | some s => do
      let payload ← match ← OpenSsl.randomBytes 32 with
        | some b => pure b
        | none => pure (Bytes.ofNatList (List.replicate 32 0x42))
      match ← Ping.ping s payload with
      | none => IO.eprintln "ping failed"; return 1
      | some ms => IO.println s!"PING OK rtt={ms}ms"
      s.close
    h.close
    return 0

def usage : IO UInt32 := do
  IO.eprintln "usage: pingnode serve <port> | pingnode dial <multiaddr>"
  return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | "serve" :: portStr :: _ =>
      match portStr.toNat? with
      | some port => serveMode port
      | none => usage
  | "dial" :: addrStr :: _ => dialMode addrStr
  | _ => usage
