import Crypto
import Libp2p.Security.Mock.Core

/-!
# The Noise constants

The numbers and strings of the noise-libp2p spec (`vendor/specs/noise`)
that this package uses, each with one home (PRINCIPLES 1.5). The
spec fixes the protocol id, the Noise protocol name, the 2-byte frame
length, the signature prefix, and the payload field numbers. The 8 KiB
payload cap comes from the package ARCHITECTURE, owned contract 2. The
two queue sizes of the transport come from the rust and nim read paths
and from the count of the posters; each docstring says which.
-/

set_option autoImplicit false

namespace Libp2p.Security.Noise

/-- The id that multistream-select negotiates for Noise. -/
def protocolId : Mock.Core.ProtocolId := ⟨"/noise"⟩

/-- The Noise protocol name, the one cipher suite of the spec ("Noise
Protocol Name"). It is exactly 32 bytes long, so the symmetric state
takes it as `h` with no hash and no padding. -/
def protocolName : String := "Noise_XX_25519_ChaChaPoly_SHA256"

/-- The largest Noise message: the 2-byte big-endian length prefix
carries at most 65535 ("Wire Format"). -/
def maxMessage : Nat := 65535

/-- The largest plaintext of one transport message. The Poly1305 tag
counts against `maxMessage`, so a writer chunks plaintext at this size
(owned contract 3). -/
def maxPlaintext : Nat := maxMessage - Crypto.aeadTagLen

/-- The largest handshake payload the decoder accepts: 8 KiB (root
§5.1). The spec and the references set no limit below `maxMessage`
(package ARCHITECTURE, owned contract 2, note). -/
def maxPayload : Nat := 8192

/-- The length of an X25519 public key, the `e` and `s` tokens on the
wire (RFC 7748 §5). -/
def dhLen : Nat := 32

/-- The nonce the Noise spec reserves: a cipher state with this nonce
refuses to encrypt or decrypt (Noise spec §5.1). -/
def reservedNonce : Nat := 2 ^ 64 - 1

/-- The prefix of the signed data: the UTF-8 string, then the static
Noise public key ("The libp2p Handshake Payload"). -/
def staticKeyPrefix : String := "noise-libp2p-static-key:"

/-! ## The transport queues -/

/-- The decrypted chunks that wait for the reader of a secure
connection: one. rust-libp2p holds one decrypted frame in
`Output.recv_buffer` and decrypts the next one only when the reader has
drained it (`vendor/rust-libp2p/transports/noise/src/io.rs`, lines 73
to 94). nim-libp2p decrypts in `readMessage`, on the reader's demand
(`vendor/nim-libp2p/libp2p/protocols/secure/noise.nim`, line 450). Here
one chunk is the plaintext of one connection read, so the transport
reads no further ahead than one read. -/
def inboxChunks : Nat := 1

/-- The events that wait for the transport loop. The posters are the
reader, which holds at most `inboxChunks` credits, so it posts at most
one read at a time, and the writers of the secure connection, each
parked on its own write. The one muxer of the stack writes from one
task (the yamux ARCHITECTURE, "Three tasks, and one writer"). So the
queue holds both posters, and a third poster parks. -/
def eventQueueCap : Nat := inboxChunks + 1

/-! ## The `NoiseHandshakePayload` message -/

/-- `optional bytes identity_key = 1`. -/
def identityKeyField : Nat := 1

/-- `optional bytes identity_sig = 2`. -/
def identitySigField : Nat := 2

/-- `optional NoiseExtensions extensions = 4`. -/
def extensionsField : Nat := 4

end Libp2p.Security.Noise
