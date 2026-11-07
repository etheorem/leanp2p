import Libp2p.Identity

/-!
# Identity fixtures for protocol transcripts

The transcripts need distinct validated peer ids without a native crypto
call. Each id is an identity multihash of one byte. Seed-derived keys
belong to the identity and crypto suites.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Identity

/-- A validated identity multihash for one transcript peer. -/
def peer (n : Nat) : Libp2p.Identity.PeerId :=
  Libp2p.Identity.PeerId.inline (ByteArray.mk #[n.toUInt8]) (by
    simp [ByteArray.size, Libp2p.Identity.maxInlineKeyBytes])

/-- A sized public key for policy tests that control verification. -/
def publicKey (n : Nat) : Libp2p.Identity.PubKey :=
  Libp2p.Identity.PubKey.ofEd25519
    ⟨ByteArray.mk (Array.replicate 32 n.toUInt8), by simp [ByteArray.size]⟩

end Tests.Gossipsub.Identity
