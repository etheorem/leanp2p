/-!
# Sized byte strings

The proof-carrying newtypes of root ARCHITECTURE §3.7 that cross this
package's FFI edge. Each one is a `ByteArray` and a proof of its size.
The Lean side checks the size once, where the bytes enter, and the shim
reads the bytes without a second check (contract 2 of the package
ARCHITECTURE).

`Key32` serves every 32-byte secret or public key the shim takes: the
ChaCha20-Poly1305 key, the Ed25519 seed, the X25519 private and public
keys, and the raw secp256k1 scalar. `Nonce12` is the RFC 8439 nonce.
Lean erases the proof field at runtime, so a newtype costs nothing.
-/

set_option autoImplicit false

namespace Backend

/-- Exactly 32 bytes. -/
structure Key32 where
  bytes : ByteArray
  sizeEq : bytes.size = 32

/-- Exactly 12 bytes: the ChaCha20-Poly1305 nonce of RFC 8439 §2.8. -/
structure Nonce12 where
  bytes : ByteArray
  sizeEq : bytes.size = 12

/-- The bytes as a `Key32`, or `none` when the size is not 32. `none` has
the one meaning "wrong size". -/
def Key32.ofByteArray? (b : ByteArray) : Option Key32 :=
  -- `if h : …` binds the decided proposition as `h`, so the `then`
  -- branch holds the proof the structure field asks for.
  if h : b.size = 32 then some ⟨b, h⟩ else none

/-- The bytes as a `Nonce12`, or `none` when the size is not 12. -/
def Nonce12.ofByteArray? (b : ByteArray) : Option Nonce12 :=
  if h : b.size = 12 then some ⟨b, h⟩ else none

instance : BEq Key32 := ⟨fun a b => a.bytes == b.bytes⟩
instance : BEq Nonce12 := ⟨fun a b => a.bytes == b.bytes⟩

example : (Key32.ofByteArray? (ByteArray.mk (Array.replicate 32 0))).isSome := by decide
example : (Key32.ofByteArray? (ByteArray.mk (Array.replicate 31 0))).isNone := by decide

end Backend
