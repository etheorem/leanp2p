import Tests.Support
import Bytes
import Crypto

/-!
# The facade check and the `Rng` seam (unit W3.3)

The checks of `packages/crypto/docs/PLAN.md`, "Test milestones", that
need only the facade. This module imports `Crypto` and no source
package, as a caller above the crypto group does.

* The facade check: the `example` blocks below name every route of the
  facade ARCHITECTURE table. Each route that leaves the backend, or
  that is an interim fallback, appears at its stated type. The build
  fails on a missing or retyped name.
* The `Rng` seam: replay, seed separation, lengths, the cap, and draws
  from two tasks at once.
-/

set_option autoImplicit false

namespace Tests

open Bytes Crypto

/-! ## The facade check -/

example : Type × Type × Type × Type := (CryptoError, Key32, Nonce12, Certificate)
example := (Key32.ofByteArray?, Nonce12.ofByteArray?, Certificate.validAt)
example := (randomBytes, maxRandomBytes)
example := (ed25519Generate, x25519Generate, secp256k1Generate, p256Generate, rsaGenerate)
example := (sha1, sha512, hmacSha256, hkdfSha256, hkdfSha256MaxLen)
example : ByteArray → Except CryptoError ByteArray := sha256
example : ByteArray → ByteArray := keccak256
example := (chachaSeal, chachaOpen, aeadTagLen, aeadMaxLen, x25519PublicKey, x25519)
example := (ed25519PublicKey, ed25519Sign, ed25519Verify, ed25519SigLen)
example := (rsaPublicKey, rsaPkcs1, rsaSign, rsaVerify, rsaMinBits, rsaMaxBits)
example := (p256PublicKey, p256Sec1, p256Sign)
example := (secp256k1PublicKey, secp256k1PointValid, secp256k1Sign, secp256k1Verify)
example : ByteArray → ByteArray → ByteArray → Bool := p256Verify
example := (inspect, selfSigned)
example := (Rng.system, Rng.seeded)

/-! ## The `Rng` seam -/

/-- The bytes of each draw of `sizes`, in order. A failed draw fails
the run. -/
private def drawAll (rng : Rng) (sizes : List Nat) : IO (List ByteArray) :=
  sizes.mapM fun n => do
    match ← (rng.bytes n).run with
    | .ok b => pure b
    | .error e => throw <| IO.userError s!"Rng draw of {n} bytes failed: {repr e}"

/-- True when the draw of `n` bytes fails with `invalidInput`. -/
private def refuses (rng : Rng) (n : Nat) : IO Bool := do
  return failsWith .invalidInput (← (rng.bytes n).run)

def Facade.run (r : Runner) : IO Unit := do
  r.section "crypto facade" "root ARCHITECTURE §3.1, §3.6"

  -- Replay: the sizes cross the 32-byte block edges and include zero.
  let sizes := [5, 32, 0, 100, 1, 64, 33]
  let seed := ofString "the seeded rng"
  let a ← drawAll (← Rng.seeded seed) sizes
  let b ← drawAll (← Rng.seeded seed) sizes
  r.check "Rng.seeded: one seed replays the same draws" (a == b)
  r.check "Rng.seeded: each draw has the requested length" (a.map (·.size) == sizes)
  let mine ← drawAll (← Rng.seeded seed) [32]
  -- The construction of the facade ARCHITECTURE: block 0 is
  -- SHA-256(seed ‖ the counter 0 as 8 bytes).
  let block0 := sha256 (seed ++ ByteArray.mk (Array.replicate 8 0))
  r.check "Rng.seeded: the first 32 bytes are SHA-256(seed ‖ 0⁸)"
    (succeedsWith (mine.getD 0 .empty) block0)
  let other ← drawAll (← Rng.seeded (ofString "another seed")) [32]
  r.check "Rng.seeded: two seeds give different bytes" (mine != other)
  let split ← drawAll (← Rng.seeded seed) [5, 11, 16, 50]
  let whole ← drawAll (← Rng.seeded seed) [82]
  r.check "Rng.seeded: split draws give the bytes of one joined draw"
    (split.foldl (· ++ ·) ByteArray.empty == whole.getD 0 .empty)
  let firstTwo ← drawAll (← Rng.seeded seed) [32, 32]
  r.check "Rng.seeded: two draws in a row differ" (firstTwo.getD 0 .empty != firstTwo.getD 1 .empty)

  -- Two tasks draw from one value at once. No two draws may repeat.
  let shared ← Rng.seeded seed
  let worker : IO (List ByteArray) := drawAll shared (List.replicate 16 32)
  let t1 ← IO.asTask worker
  let t2 ← IO.asTask worker
  let d1 ← IO.ofExcept (← IO.wait t1)
  let d2 ← IO.ofExcept (← IO.wait t2)
  let all := d1 ++ d2
  r.check "Rng.seeded: 32 draws from two tasks are all distinct"
    (all.length == 32 && all.eraseDups.length == 32)

  -- The cap is the same on both values.
  r.check "Rng.seeded: a draw past maxRandomBytes is invalidInput"
    (← refuses (← Rng.seeded seed) (maxRandomBytes + 1))
  r.check "Rng.system: a draw past maxRandomBytes is invalidInput"
    (← refuses Rng.system (maxRandomBytes + 1))

  -- The production value.
  let s ← drawAll Rng.system [32, 32, 7]
  r.check "Rng.system: each draw has the requested length" (s.map (·.size) == [32, 32, 7])
  r.check "Rng.system: two draws differ" (s.getD 0 .empty != s.getD 1 .empty)

end Tests
