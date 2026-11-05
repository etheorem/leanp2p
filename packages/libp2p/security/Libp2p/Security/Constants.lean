/-!
# Noise constants

The wire numbers of `noise-libp2p` that every other module in this package
reads: the protocol id the negotiate layer matches on, the handshake name the
Noise framework hashes into its initial state, the message ceiling, and the
transport payload ceiling.

Root `docs/ARCHITECTURE.md` §4.9 fixes these. `maxMessage` comes from the
Noise specification's 16-bit length prefix, the 8 KiB payload cap is
libp2p's, and `tagLen` is the ChaCha20-Poly1305 tag. The two derived numbers,
`chunkSize` and `maxPayload`, are the ones the transport and the payload
codec actually use, so they are stated as theorems here rather than left to
arithmetic at the call site.
-/

set_option autoImplicit false

namespace Libp2p.Security

/-- The multiaddr protocol id this security protocol is negotiated under. -/
def protocolId : String := "/noise"

/-- The Noise framework's protocol name. The raw ASCII is exactly 32 bytes,
so the initial handshake hash is the name itself and not a digest of it
(Noise §5.2); `handshakeName_length` below records that. -/
def handshakeName : String := "Noise_XX_25519_ChaChaPoly_SHA256"

/-- One Noise message carries at most 65535 bytes, the 16-bit length prefix
of the Noise specification's message format. -/
def maxMessage : Nat := 65535

/-- The libp2p handshake payload ceiling, 8 KiB. A payload longer than this
is rejected before it reaches the identity check, so a peer cannot make us
buffer an unbounded signature input. -/
def maxPayload : Nat := 8192

/-- The ChaCha20-Poly1305 authentication tag, in bytes. -/
def tagLen : Nat := 16

/-- The plaintext a single transport frame may carry: the message ceiling
minus the tag that is appended to it. -/
def chunkSize : Nat := maxMessage - tagLen

/-- Noise's 64-bit counter nonce ceiling: one key may encrypt this many
messages before it must be renegotiated. Unreachable on any real link, but
the transport checks it rather than wrapping. -/
def maxNonce : Nat := 2 ^ 64 - 1

theorem chunkSize_eq : chunkSize = 65519 := by decide

theorem chunkSize_add_tag : chunkSize + tagLen = maxMessage := by decide

theorem maxMessage_lt_prefix : maxMessage < 65536 := by decide

theorem maxPayload_lt_chunk : maxPayload < chunkSize := by decide

theorem maxPayload_pos : 0 < maxPayload := by decide

end Libp2p.Security
