import LeanP2P.Crypto.Bytes
import LeanP2P.Crypto.Multihash
/-!
# Peer identity

`PeerId` is a multihash over the serialized public key, exactly the libp2p
shape: for non-inlined keys it is `0x12 0x20 <sha256(pubkey)>`. The spike's
"pubkey" is seed bytes (no real keygen), but the identifier layer is
spec-shaped.
-/

namespace LeanP2P

deriving instance Repr for ByteArray

structure PubKey where
  bytes : ByteArray
deriving Repr, BEq

/-- Deterministic toy key material. PLACEHOLDER for ed25519 keygen. -/
def PubKey.ofSeed (seed : String) : PubKey where
  bytes := Bytes.ofString seed

structure PeerId where
  bytes : ByteArray
deriving Repr, BEq

/-- libp2p peer id: sha2-256 multihash of the key bytes. -/
def PeerId.derive (k : PubKey) : PeerId where
  bytes := Bytes.ofNatList (Multihash.sha256 (Bytes.toNatList k.bytes))

/-- Peer id as raw multihash bytes (for /p2p multiaddr components). -/
def PeerId.digestBytes (p : PeerId) : List Nat :=
  Bytes.toNatList p.bytes

end LeanP2P
