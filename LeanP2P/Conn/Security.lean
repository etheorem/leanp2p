import LeanP2P.Net.Transport
import LeanP2P.Conn.Reader
import LeanP2P.Crypto.PeerId
import LeanP2P.Crypto.Keys
import LeanP2P.Crypto.Sha256
/-!
# Security transport interface

`handshake` upgrades a raw connection into an encrypted, peer-authenticated
`SecureConn`. The spike ships only a toy (the "KEX" is NOT secure — it
exists to exercise the composition shape where Noise/TLS would plug in).

The handshake receives the *same* `BufReader` the multistream-select
negotation used: bytes that coalesced past the selection reply stay in
that buffer and must reach the handshake (a lazy dialer sends its first
handshake message together with the proposal). A fresh reader here would
silently drop them.
-/

namespace LeanP2P

inductive Role where
  | initiator
  | responder
  deriving Repr, BEq, DecidableEq

/-- A connection with an established identity, post-handshake. `remoteMuxers`
carries the stream muxers the peer advertised during the security
handshake (the Noise extensions); empty when the security protocol has no
such extension, in which case the muxer falls back to multistream-select. -/
structure SecureConn extends Connection where
  localPeer : PeerId
  remotePeer : PeerId
  remoteMuxers : List String := []

structure SecurityProtocol where
  name : String
  handshake : Role → BufReader → IO (Option SecureConn)

/-- XOR-stream wrapper over a raw connection. The keystream position is
tracked per direction, so this stays correct over real transports where
reads do not align with writes (the sim preserves write boundaries; TCP
does not - the original per-chunk XOR desynced there). -/
def NoiseSim.xorConn (shared : ByteArray) (conn : Connection) :
    IO Connection := do
  let rp ← IO.mkRef 0
  let wp ← IO.mkRef 0
  let n := shared.size
  let xorAt (pos : IO.Ref Nat) (b : ByteArray) : IO ByteArray := do
    if n = 0 then return b
    let p ← pos.get
    let out := ByteArray.mk
      (b.data.mapIdx fun i v => v ^^^ shared[(p + i) % n]!)
    pos.set (p + b.size)
    return out
  let read : IO (Option ByteArray) := do
    match ← conn.read with
    | none => pure none
    | some b => some <$> xorAt rp b
  let write := fun b => do
    conn.write (← xorAt wp b)
  return { read := read, write := write, close := conn.close
           localAddr := conn.localAddr, remoteAddr := conn.remoteAddr }

/-- Peer id of raw key bytes: the spec derivation (identity inlining for
Ed25519), with the spike's sha256 derivation as fallback for bytes that
are not a `PublicKey` protobuf. -/
def NoiseSim.peerIdOf (raw : ByteArray) : PeerId :=
  match Keys.unmarshalPubKey? raw with
  | some k => PeerId.ofPublicKey k
  | none => PeerId.derive (PubKey.mk raw)

/-- Toy "noise": exchange pubkey bytes, derive a symmetric shared secret
(XOR of both sha256 key digests — order-independent). Everyone can read
this traffic; it only demonstrates the interface. Reads go through the
negotiation reader so coalesced bytes are not lost. -/
def NoiseSim.handshake (key : PubKey) (role : Role) (r : BufReader) :
    IO (Option SecureConn) := do
  let conn := r.conn
  let other? ←
    match role with
    | .initiator => do
      conn.write key.bytes
      BufReader.readExactly r key.bytes.size
    | .responder => do
      match ← BufReader.readExactly r key.bytes.size with
      | none => pure none
      | some a =>
        conn.write key.bytes
        pure (some a)
  match other? with
  | none => return none
  | some other =>
    let dA := Bytes.ofNatList (Sha256.digest (Bytes.toNatList key.bytes))
    let dB := Bytes.ofNatList (Sha256.digest (Bytes.toNatList other))
    let c ← NoiseSim.xorConn (Bytes.xorWith dA dB) conn
    return some
      { toConnection := c
        localPeer := NoiseSim.peerIdOf key.bytes
        remotePeer := NoiseSim.peerIdOf other
        remoteMuxers := [] }

def NoiseSim.security (key : PubKey) : SecurityProtocol where
  name := "noise-sim/1.0.0"
  handshake := NoiseSim.handshake key

end LeanP2P
