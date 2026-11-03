import Backend
import Conc

/-!
# The `Rng` seam

Randomness reaches the cores as an input (root ARCHITECTURE §3.3). The
shell draws bytes through this seam and passes them in the event that
needs them. §3.1 gives every seam two values from the start, and §3.6
puts this one in the facade:

* `Rng.system`, the production value, draws from the OpenSSL DRBG
  through `Backend.randomBytes`.
* `Rng.seeded`, the test value, gives a fixed sequence of bytes for a
  seed. A suite above the facade can then replay a handshake byte for
  byte.

Both values share one failure shape: a draw past `maxRandomBytes` is
`invalidInput`. A test that passes on the seeded value then exercises
the same cap as production.

**The shared position.** The seeded value keeps its position in the
sequence in a `Conc.OnceRef`. Two tasks may draw from one value at the
same time. Each draw claims its part of the sequence with one
`updateGet`, so no two draws receive the same bytes (§4.1, rule 3).
-/

set_option autoImplicit false

namespace Crypto

/-- The random source of a shell (§3.1). `bytes n` gives `n` bytes. It
fails with `invalidInput` past `Backend.maxRandomBytes`. -/
structure Rng where
  bytes : Nat → ExceptT Backend.CryptoError IO ByteArray

namespace Rng

/-- The production value: the OpenSSL DRBG. -/
def system : Rng := ⟨Backend.randomBytes⟩

/-- `n` as 8 big-endian bytes, the counter form of `block`. -/
private def be64 (n : Nat) : ByteArray :=
  ByteArray.mk ((List.range 8).reverse.map fun i => ((n / 256 ^ i) % 256).toUInt8).toArray

/-- The size of one `block`, the SHA-256 digest size. -/
def blockSize : Nat := 32

/-- Block `i` of the seeded sequence: SHA-256(`seed` ‖ `i` as 8
big-endian bytes), 32 bytes. SHA-256 is a fixed function, so the bytes
are the same on every machine (facade ARCHITECTURE, "Decisions"). A
SHA-256 fault is a fault of the draw. -/
def block (seed : ByteArray) (i : Nat) : Except Backend.CryptoError ByteArray :=
  Backend.sha256 (seed ++ be64 i)

/-- One draw of `n` bytes from the seeded sequence of `seed`. `pos`
holds the position. The caller has checked `n` against the cap.

The sequence is one byte stream, `block 0 ‖ block 1 ‖ …`, and `pos` is
the byte offset into it. A draw claims the range `[o, o + n)` with one
`updateGet`. The bytes then depend only on how many bytes came before.
Two draws of 16 bytes give the bytes of one draw of 32. A caller may
then split or join its draws and keep its fixtures (facade
ARCHITECTURE, contract 4). -/
def draw (seed : ByteArray) (pos : Conc.OnceRef Nat) (n : Nat) :
    ExceptT Backend.CryptoError IO ByteArray := do
  let start ← pos.updateGet fun o => (o, o + n)
  -- The blocks that cover `[start, start + n)`, then the range inside them.
  let first := start / blockSize
  let stop := (start + n + blockSize - 1) / blockSize
  let mut covered := ByteArray.empty
  for k in [first:stop] do
    -- `ExceptT.mk (pure e)` lifts the pure `Except` of `block` into the
    -- draw's monad, so a fault ends the draw.
    covered := covered ++ (← ExceptT.mk (pure (block seed k)))
  let skip := start % blockSize
  pure (covered.extract skip (skip + n))

/-- The test value: the fixed sequence of `seed`, from its start. Two
values from one seed give the same bytes for the same draws. -/
def seeded (seed : ByteArray) : BaseIO Rng := do
  let pos ← Conc.OnceRef.new 0
  pure ⟨fun n => do
    if n > Backend.maxRandomBytes then throw .invalidInput
    draw seed pos n⟩

end Rng

end Crypto
