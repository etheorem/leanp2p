import Tests.Support
import Tests.Backend
import Bytes
import Backend
import Crypto
import Crypto.Mock.Pure

/-!
# The W3.3 cross-check

The checks of `packages/crypto/docs/PLAN.md`, "Test milestones", that
compare two implementations. This is the one module that imports both:
the facade, which names the production path, and the pure copies
(root ARCHITECTURE §3.6, §4.6). It also imports `Backend`, for
the P-256 differential against the backend verifier.

* **The swap demonstration.** One line routes `sha256` to the pure copy
  at the type the facade states. One call-site text elaborates against
  each route, and the two give the same bytes.
* **Direction one, the vector decides.** The RFC and multihash entries
  run through the pure copy and the production path. Both answers
  must match the expected bytes. The sweep lengths of the pure plan run
  through both, and the answers must agree.
* **Direction two, the production path decides.** Inputs from
  `Rng.system` run through the production path first. The pure copy
  must give the same bytes.
* **The P-256 route.** The etheorem route against `Backend.p256Verify`,
  case by case.
* **The secp256k1 recovery route.** Fresh backend keys and signatures:
  the etheorem recovery gives back each signer's point, for the low S
  and for its high-S twin.

**The mock.** W3.1 (`crypto/pure`) has not merged, so the pure names
resolve to `Crypto.Mock.CryptoPure` through `open Crypto.Mock`
(RULES.md, "Working ahead of the tree"). At integration this module
imports `CryptoPure` in place of `Crypto.Mock.Pure` and drops the
`open`. No call below changes.
-/

set_option autoImplicit false

namespace Tests

open Bytes
-- The pure names (`CryptoPure.Sha256.digestB`, …) resolve through this
-- namespace while the mock stands in for W3.1.
open Crypto.Mock

/-- The answer of a production call, or the run fails. A production
fault on a valid input fails the check, and the message names it. -/
private def okX {α : Type} (where_ : String) : Except Crypto.CryptoError α → IO α
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"{where_}: production call failed: {repr e}"

/-- The hex text of a production answer, or the error's name. A
production fault then shows as a mismatch, and the run continues. -/
private def prodHex : Except Crypto.CryptoError ByteArray → String
  | .ok b => toHex b
  | .error e => s!"error {repr e}"

/-- The sweep input of length `n`: the bytes `i % 251`, so no block of
the input repeats the block before it. -/
private def sweepB (n : Nat) : ByteArray :=
  ofNatList ((List.range n).map (· % 251))

/-- HMAC-SHA-256 through the pure copy, over bytes. -/
private def pureHmac (key msg : ByteArray) : ByteArray :=
  ofNatList (CryptoPure.Hmac.sha256 (toNatList key) (toNatList msg))

/-- HKDF-SHA-256 through the pure copy: extract, then expand. `none`
past 255 blocks. -/
private def pureHkdf (salt ikm info : ByteArray) (len : Nat) : Option ByteArray :=
  let prk := CryptoPure.Hkdf.extractSha256 (toNatList salt) (toNatList ikm)
  (CryptoPure.Hkdf.expandSha256 prk (toNatList info) len).map ofNatList

/-- True when the pure HKDF and the production HKDF agree: the same
bytes, or `none` on the pure side where production answers
`invalidInput`. -/
private def hkdfAgree (salt ikm info : ByteArray) (len : Nat) : Bool :=
  match pureHkdf salt ikm info len, Crypto.hkdfSha256 salt ikm info len with
  | some p, .ok q => p == q
  | none, .error .invalidInput => true
  | _, _ => false

/-! ## The swap demonstration

The production call site opens only the facade's `sha256`. The swapped
namespace declares its own `sha256`, the one changed line, and opens
nothing. The two call-site bodies are the same text. -/

namespace FacadeSwap

section Production
open Crypto (sha256)

/-- The call site, against the facade route. -/
def callSite (b : ByteArray) : Except Crypto.CryptoError ByteArray := do
  let d ← sha256 b
  sha256 (d ++ b)

end Production

namespace Swapped

/-- The one-line swap: SHA-256 routed to the pure copy, at the type the
facade states for `Crypto.sha256`. -/
abbrev sha256 : ByteArray → Except Crypto.CryptoError ByteArray :=
  fun b => .ok (CryptoPure.Sha256.digestB b)

/-- The call site, against the swapped route: the same text. -/
def callSite (b : ByteArray) : Except Crypto.CryptoError ByteArray := do
  let d ← sha256 b
  sha256 (d ++ b)

end Swapped

end FacadeSwap

private def swap (r : Runner) : IO Unit := do
  let inputs := [ByteArray.empty, ofString "abc", sweepB 55, sweepB 64, sweepB 1000]
  let same := inputs.all fun b =>
    match FacadeSwap.callSite b, FacadeSwap.Swapped.callSite b with
    | .ok x, .ok y => x == y
    | _, _ => false
  r.check "facade swap: one call-site text, two routes, the same digests" same

/-! ## Direction one: the vector decides -/

private def rfcVectors (r : Runner) : IO Unit := do
  let rfc := "hashes-rfc.json"
  let j ← loadJson rfc
  for v in ← jArr rfc j "sha512" do
    let name ← jStr rfc v "name"
    let input ← unhex rfc (← jStr rfc v "inputHex")
    let want ← jStr rfc v "digestHex"
    r.check s!"cross SHA-512 {name}: pure and production match the vector"
      (toHex (CryptoPure.Sha512.digestB input) == want && prodHex (Crypto.sha512 input) == want)
  for v in ← jArr rfc j "hmacSha256" do
    let name ← jStr rfc v "name"
    let key ← unhex rfc (← jStr rfc v "keyHex")
    let msg ← unhex rfc (← jStr rfc v "dataHex")
    let want ← jStr rfc v "macHex"
    r.check s!"cross HMAC-SHA-256 {name}: pure and production match the vector"
      (toHex (pureHmac key msg) == want && prodHex (Crypto.hmacSha256 key msg) == want)
  for v in ← jArr rfc j "hkdfSha256" do
    let name ← jStr rfc v "name"
    let ikm ← unhex rfc (← jStr rfc v "ikmHex")
    let salt ← unhex rfc (← jStr rfc v "saltHex")
    let info ← unhex rfc (← jStr rfc v "infoHex")
    let len ← jNat rfc v "l"
    let wantPrk ← jStr rfc v "prkHex"
    let want ← jStr rfc v "okmHex"
    -- The pure side checks extract on its own too: the production
    -- binding is one-shot, so only the pure copy exposes the PRK.
    let prk := ofNatList (CryptoPure.Hkdf.extractSha256 (toNatList salt) (toNatList ikm))
    r.check s!"cross HKDF-SHA-256 {name}: the pure extract matches the PRK" (toHex prk == wantPrk)
    r.check s!"cross HKDF-SHA-256 {name}: pure and production match the vector"
      ((pureHkdf salt ikm info len).map toHex == some want &&
        prodHex (Crypto.hkdfSha256 salt ikm info len) == want)

/-- The multihash spec digests over "multihash". The code byte and the
length byte frame the digest, so the digest starts at byte 2. -/
private def multihashVectors (r : Runner) : IO Unit := do
  let mh := "multihash-examples.json"
  let mj ← loadJson mh
  let mut seen : List String := []
  for c in ← jArr mh mj "cases" do
    let alg ← jStr mh c "algorithm"
    let input := ofString (← jStr mh c "input")
    for e in ← jArr mh c "encodings" do
      unless (← jStr mh e "kind") == "hex" do continue
      let framed ← unhex mh (← jStr mh e "value")
      let want := framed.extract 2 framed.size
      match alg with
      | "sha2-256" =>
        seen := alg :: seen
        r.check "cross multihash sha2-256: pure and production match"
          (CryptoPure.Sha256.digestB input == want && prodHex (Crypto.sha256 input) == toHex want)
      | "sha1" =>
        seen := alg :: seen
        r.check "cross multihash sha1: pure and production match"
          (CryptoPure.Sha1.digestB input == want && prodHex (Crypto.sha1 input) == toHex want)
      | _ => pure ()
  r.check "cross multihash: the file holds the sha2-256 and sha1 cases"
    (seen.contains "sha2-256" && seen.contains "sha1")

/-- One digest family over a list of lengths: the pure copy and the
production path agree on `sweepB n` for every `n`. -/
private def sweep (r : Runner) (name : String) (lens : List Nat)
    (pureD : ByteArray → ByteArray)
    (prodD : ByteArray → Except Crypto.CryptoError ByteArray) : IO Unit := do
  let misses := lens.filter fun n => prodHex (prodD (sweepB n)) != toHex (pureD (sweepB n))
  r.check s!"cross {name} sweep over {lens.length} lengths: pure and production agree (misses at {misses})"
    misses.isEmpty

/-- The sweeps of the pure plan, "Test milestones". -/
private def sweeps (r : Runner) : IO Unit := do
  -- The 64-byte block edges of SHA-256, and of SHA-1, which shares the
  -- block and the padding rule.
  let lens64 := [0, 1, 55, 56, 63, 64, 65, 119, 120, 128, 1000]
  sweep r "SHA-256" lens64 CryptoPure.Sha256.digestB Crypto.sha256
  sweep r "SHA-1" lens64 CryptoPure.Sha1.digestB Crypto.sha1
  sweep r "SHA-512" (List.range 301 ++ [511, 512, 513, 1000, 4096])
    CryptoPure.Sha512.digestB Crypto.sha512
  -- HMAC key lengths around the 64-byte block. HMAC hashes a key
  -- longer than the block first (RFC 2104).
  let msg := ofString "the HMAC key-length sweep"
  let keyMisses := [0, 1, 63, 64, 65, 128, 200].filter fun k =>
    prodHex (Crypto.hmacSha256 (sweepB k) msg) != toHex (pureHmac (sweepB k) msg)
  r.check s!"cross HMAC-SHA-256 key-length sweep: pure and production agree (misses at {keyMisses})"
    keyMisses.isEmpty
  -- HKDF output lengths around the 32-byte block, up to the 255-block
  -- limit and one past it (RFC 5869 §2.3).
  let max := Crypto.hkdfSha256MaxLen
  let lenMisses := [0, 1, 31, 32, 33, 64, 1000, max - 1, max, max + 1].filter fun n =>
    !hkdfAgree (sweepB 13) (sweepB 22) (sweepB 10) n
  r.check s!"cross HKDF-SHA-256 length sweep: pure and production agree (misses at {lenMisses})"
    lenMisses.isEmpty
  r.check "cross HKDF-SHA-256: one byte past 255 blocks fails on both sides"
    ((pureHkdf (sweepB 13) (sweepB 22) (sweepB 10) (max + 1)).isNone &&
      failsWith .invalidInput (Crypto.hkdfSha256 (sweepB 13) (sweepB 22) (sweepB 10) (max + 1)))

/-! ## Direction two: the production path decides -/

/-- `n` fresh bytes from the production `Rng`. -/
private def fresh (n : Nat) : IO ByteArray := do
  okX "Rng.system" (← (Crypto.Rng.system.bytes n).run)

/-- A fresh length below `bound`, from two fresh bytes. -/
private def freshLen (bound : Nat) : IO Nat := do
  let b ← fresh 2
  return ((b.get! 0).toNat * 256 + (b.get! 1).toNat) % bound

/-- How many generated inputs each family runs. -/
private def generatedCount : Nat := 48

private def generated (r : Runner) : IO Unit := do
  let mut misses : Array String := #[]
  for _ in [0:generatedCount] do
    -- Lengths up to 300 cross the 64-byte and 128-byte block edges.
    let m ← fresh (← freshLen 300)
    let sha1 ← okX "sha1" (Crypto.sha1 m)
    if sha1 != CryptoPure.Sha1.digestB m then misses := misses.push s!"sha1/{m.size}"
    let sha256 ← okX "sha256" (Crypto.sha256 m)
    if sha256 != CryptoPure.Sha256.digestB m then misses := misses.push s!"sha256/{m.size}"
    let sha512 ← okX "sha512" (Crypto.sha512 m)
    if sha512 != CryptoPure.Sha512.digestB m then misses := misses.push s!"sha512/{m.size}"
    -- Key lengths up to 200 cross the 64-byte key rule.
    let key ← fresh (← freshLen 200)
    let mac ← okX "hmacSha256" (Crypto.hmacSha256 key m)
    if mac != pureHmac key m then misses := misses.push s!"hmac/{key.size}/{m.size}"
    let salt ← fresh (← freshLen 80)
    let info ← fresh (← freshLen 40)
    let len ← freshLen 600
    let okm ← okX "hkdfSha256" (Crypto.hkdfSha256 salt key info len)
    if some okm != pureHkdf salt key info len then
      misses := misses.push s!"hkdf/{salt.size}/{key.size}/{info.size}/{len}"
  r.check s!"cross: {generatedCount} generated inputs per family, the pure copies reproduce production (misses: {misses})"
    misses.isEmpty

/-! ## The P-256 route against the backend verifier -/

/-- The P-256 group order n (FIPS 186-5, D.1.2.3). -/
private def p256Order : Nat :=
  0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

/-- The 26-byte head of the SPKI of a compressed P-256 point: the
uncompressed head with a 33-byte BIT STRING and no `0x04` tag. -/
private def compressedHead : ByteArray := ByteArray.mk #[
  0x30, 0x39, 0x30, 0x13,
  0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01,
  0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07,
  0x03, 0x22, 0x00]

/-- The answers of the backend verifier and of the facade route. -/
private def both (spki msg sig : ByteArray) : Bool × Bool :=
  (Backend.p256Verify spki msg sig, Crypto.p256Verify spki msg sig)

/-- The go fixture and the cases built from it. -/
private def p256Fixture (r : Runner) : IO Unit := do
  let file := "keys-go-libp2p.json"
  let j ← loadJson file
  let msg ← unhex file (← jStr file j "messageHex")
  let mut found := false
  for c in ← jArr file j "cases" do
    let name ← jStr file c "name"
    if name == "rsa" then
      let rsaPub ← unhex file (← jStr file c "pubRawHex")
      let rsaSig ← unhex file (← jStr file c "sigHex")
      r.check "P-256 route: an RSA key and signature, both reject"
        (both rsaPub msg rsaSig == (false, false))
    unless name == "ecdsa" do continue
    found := true
    let pub ← unhex file (← jStr file c "pubRawHex")
    let sig ← unhex file (← jStr file c "sigHex")
    let (sr, ss) ← Ecdsa.derSig file sig
    r.check "P-256 route: the fixture SPKI parses to a point" (Crypto.P256.spkiPoint? pub).isSome
    r.check "P-256 route: the go fixture, both accept" (both pub msg sig == (true, true))
    r.check "P-256 route: a tampered message, both reject"
      (both pub (msg.push 0) sig == (false, false))
    r.check "P-256 route: the high-S twin, both accept"
      (both pub msg (Ecdsa.derSigOf sr (p256Order - ss)) == (true, true))
    -- A second zero byte in front of r: the value is the same, and the
    -- encoding is not minimal.
    let rInt := Ecdsa.derInt sr
    let rLong := ByteArray.mk #[0x02, (rInt.size - 1).toUInt8, 0x00] ++ rInt.extract 2 rInt.size
    let sInt := Ecdsa.derInt ss
    let nonMinimal := ByteArray.mk #[0x30, (rLong.size + sInt.size).toUInt8] ++ rLong ++ sInt
    r.check "P-256 route: a non-minimal INTEGER, both reject"
      (both pub msg nonMinimal == (false, false))
    let negative := ByteArray.mk #[0x30, (3 + sInt.size).toUInt8, 0x02, 0x01, 0xff] ++ sInt
    r.check "P-256 route: a negative INTEGER, both reject" (both pub msg negative == (false, false))
    r.check "P-256 route: a trailing byte, both reject" (both pub msg (sig.push 0) == (false, false))
    -- The SEQUENCE rules of strict DER (X.690 §10.1, RFC 3279 §2.2.3).
    -- The fixture uses the short length form, so its body starts at 2.
    let body := sig.extract 2 sig.size
    let longForm := ByteArray.mk #[0x30, 0x81, body.size.toUInt8] ++ body
    r.check "P-256 route: a long-form SEQUENCE length, both reject"
      (both pub msg longForm == (false, false))
    let threeInts := ByteArray.mk #[0x30, (body.size + 3).toUInt8] ++ body ++
      ByteArray.mk #[0x02, 0x01, 0x01]
    r.check "P-256 route: a third INTEGER in the SEQUENCE, both reject"
      (both pub msg threeInts == (false, false))
    r.check "P-256 route: a SET tag in place of the SEQUENCE tag, both reject"
      (both pub msg (sig.set! 0 0x31) == (false, false))
    -- r with a 33-byte magnitude: 0x01 then 32 bytes, a value past 2^256.
    let rWide := ByteArray.mk #[0x02, 0x21, 0x01] ++ Ecdsa.bytesOfNat 32 sr
    let wide := ByteArray.mk #[0x30, (rWide.size + sInt.size).toUInt8] ++ rWide ++ sInt
    r.check "P-256 route: an INTEGER longer than 32 bytes, both reject"
      (both pub msg wide == (false, false))
    -- The compressed point: the parity of y picks the prefix 0x02 or
    -- 0x03 (SEC 1 §2.3.3).
    let x := pub.extract 27 59
    let compressed := compressedHead.push (0x02 ||| (pub.get! 90 &&& 1)) ++ x
    r.check "P-256 route: a compressed SPKI, both reject (go rejects)"
      (both compressed msg sig == (false, false))
    -- The hybrid form (SEC 1 §2.3.3, X9.62): the uncompressed layout
    -- with the tag 0x06 or 0x07 by the parity of y.
    let hybrid := pub.set! 26 (0x06 ||| (pub.get! 90 &&& 1))
    r.check "P-256 route: a hybrid SPKI, both reject (go rejects)"
      (both hybrid msg sig == (false, false))
    r.check "P-256 route: a byte string that is no SPKI, both reject"
      (both (ByteArray.mk #[0x00]) msg sig == (false, false))
  r.check "P-256 route: the go fixture file has an ecdsa case" found

/-- A secp256k1 key under the P-256 verifier, and fresh P-256 keys. -/
private def p256Generated (r : Runner) : IO Unit := do
  let fx := "backend-strictness.json"
  let fj ← loadFixture fx
  let fmsg ← unhex fx (← jStr fx fj "messageHex")
  let k1 ← jObj fx fj "secp256k1Spki"
  r.check "P-256 route: a secp256k1 SPKI key, both reject"
    (both (← unhex fx (← jStr fx k1 "spkiHex")) fmsg (← unhex fx (← jStr fx k1 "sigHex"))
      == (false, false))
  let draws := 8
  let mut good := 0
  for _ in [0:draws] do
    let priv ← okX "p256Generate" (← Crypto.p256Generate.run)
    let pub ← okX "p256PublicKey" (Crypto.p256PublicKey priv)
    let own ← okX "p256Sign" (← (Crypto.p256Sign priv fmsg).run)
    if both pub fmsg own == (true, true) && both pub (fmsg.push 0) own == (false, false) then
      good := good + 1
  r.check s!"P-256 route: {draws} fresh keys and signatures, both accept and both reject a tamper ({good} did)"
    (good == draws)

/-- The secp256k1 recovery route. The backend binds no recovery, so the
backend derivation is the reference: some recovery id from 0 to 3 must
give back the signer's point. A high S recovers too, which the route's
docstring tells callers. -/
private def k1Recover (r : Runner) : IO Unit := do
  let msg := ofString "the secp256k1 recovery route"
  let hash ← okX "sha256" (Crypto.sha256 msg)
  -- The SEC1 compressed form of `x ‖ y`: 0x02 or 0x03 by the parity of
  -- y, then x.
  let compress (k : ByteArray) : ByteArray :=
    ByteArray.mk #[0x02 ||| (k.get! 63 &&& 1)] ++ k.extract 0 32
  let recovers (point sr ss : ByteArray) : Bool :=
    [0, 1, 2, 3].any fun (id : UInt32) =>
      let k := Crypto.secp256k1Recover hash sr ss id
      k.size == 64 && compress k == point
  let draws := 8
  let mut low := 0
  let mut high := 0
  for _ in [0:draws] do
    let scalar ← okX "secp256k1Generate" (← Crypto.secp256k1Generate.run)
    let point ← okX "secp256k1PublicKey" (Crypto.secp256k1PublicKey scalar)
    let (sr, ss) ← Ecdsa.derSig "secp256k1Sign" (← okX "secp256k1Sign" (Crypto.secp256k1Sign scalar msg))
    let srB := Ecdsa.bytesOfNat 32 sr
    if recovers point srB (Ecdsa.bytesOfNat 32 ss) then low := low + 1
    if recovers point srB (Ecdsa.bytesOfNat 32 (Ecdsa.secp256k1Order - ss)) then high := high + 1
  r.check s!"secp256k1 recovery route: {draws} fresh signatures recover the signer's point ({low} did)"
    (low == draws)
  r.check s!"secp256k1 recovery route: their high-S twins recover it too ({high} did)"
    (high == draws)
  r.check "secp256k1 recovery route: a recovery id past 3 gives the empty answer"
    (Crypto.secp256k1Recover hash (Ecdsa.bytesOfNat 32 1) (Ecdsa.bytesOfNat 32 1) 4).isEmpty

def CryptoCross.run (r : Runner) : IO Unit := do
  r.section "crypto cross-check"
    "RFC 4231, RFC 5869, FIPS 180-4, multihash README, go-libp2p core/crypto/test_data"
  swap r
  rfcVectors r
  multihashVectors r
  sweeps r
  generated r
  p256Fixture r
  p256Generated r
  k1Recover r

end Tests
