import Tests.Support
import LeanP2P.Crypto.Sha512
import LeanP2P.Crypto.Hmac
import LeanP2P.Crypto.Hkdf
import LeanP2P.Crypto.OpenSsl

/-!
# Hash and KDF suites (VECTOR_TEST_PLAN.md, phase 2 step 14)

- SHA-512: FIPS 180-4 example vectors + a size sweep cross-checked against
  OpenSSL (the pure `List Nat` implementation is the production reference;
  the sweep keeps it anchored at every padding boundary).
- HMAC-SHA-256: RFC 4231 TC1/TC2 + OpenSSL cross-check.
- HKDF-SHA-256: RFC 5869 TC1/TC3 (extract and expand) + OpenSSL cross-check.
- SHA-256: the `ByteArray` entry point must agree with the `List Nat`
  original on every run, and both with OpenSSL.
-/

open LeanP2P Tests

namespace Tests

/-- Deterministic test buffer of `n` bytes: `i * mult mod 256`. -/
private def patternBA (n mult : Nat) : ByteArray :=
  (List.range n).foldl
    (fun a i => a.push (UInt8.ofNat ((i * mult) % 256))) ByteArray.empty

private def optBytes (name : String) (b : IO (Option ByteArray)) :
    IO ByteArray := do
  match ← b with
  | some x => pure x
  | none => throw <| IO.userError s!"backend failure: {name}"

def Hashes.run (r : Runner) : IO Unit := do
  r.section "sha512 / hmac / hkdf" "RFC 4634 examples, RFC 4231, RFC 5869 \
(pinned in Tests/vectors/hashes-rfc.json); OpenSSL cross-checks"

  let j ← loadJson "hashes-rfc.json"

  -- SHA-512 spec examples
  for e in (← jArr "hashes-rfc.json" j "sha512") do
    let name ← jStr "hashes-rfc.json" e "name"
    let input ← hexBytes (← jStr "hashes-rfc.json" e "inputHex")
    let digest ← jStr "hashes-rfc.json" e "digestHex"
    r.check s!"sha512 {name}" (Sha512.digest input == (← hexBytes digest))

  -- SHA-512 sweep against OpenSSL: every padding boundary from 0 to 300
  -- bytes, plus a large multi-block message
  let sweep := (List.range 301) ++ [511, 512, 513, 1000, 4096]
  let mut sweepOk := true
  for n in sweep do
    let msg := patternBA n 7
    let pure := Bytes.ofNatList (Sha512.digest (Bytes.toNatList msg))
    let backend ← optBytes "sha512 sweep" (OpenSsl.sha512 msg)
    if pure != backend then
      sweepOk := false
      r.check s!"sha512 sweep {n} (pure = openssl)" false
  if sweepOk then
    r.check "sha512 sweep (0..300, 511..513, 1000, 4096) pure = openssl" true

  -- HMAC-SHA-256 RFC 4231
  for e in (← jArr "hashes-rfc.json" j "hmacSha256") do
    let name ← jStr "hashes-rfc.json" e "name"
    let key ← hexBytes (← jStr "hashes-rfc.json" e "keyHex")
    let data ← hexBytes (← jStr "hashes-rfc.json" e "dataHex")
    let mac ← hexBytes (← jStr "hashes-rfc.json" e "macHex")
    r.check s!"hmac-sha256 {name}" (Hmac.hmac key data == mac)
    let backend ← optBytes "hmac" (OpenSsl.hmacSha256
      (Bytes.ofNatList key) (Bytes.ofNatList data))
    r.check s!"hmac-sha256 {name} (openssl cross-check)" (backend == Bytes.ofNatList mac)

  -- long-key and block-boundary HMAC cases against OpenSSL
  for n in [0, 1, 63, 64, 65, 128, 200] do
    let key := patternBA n 11
    let msg := Bytes.ofNatList [0x68, 0x69]
    let pure := Bytes.ofNatList
      (Hmac.hmac (Bytes.toNatList key) (Bytes.toNatList msg))
    let backend ← optBytes "hmac sweep" (OpenSsl.hmacSha256 key msg)
    r.check s!"hmac-sha256 key len {n} (openssl cross-check)" (pure == backend)

  -- HKDF-SHA-256 RFC 5869
  for e in (← jArr "hashes-rfc.json" j "hkdfSha256") do
    let name ← jStr "hashes-rfc.json" e "name"
    let ikm ← hexBytes (← jStr "hashes-rfc.json" e "ikmHex")
    let salt ← hexBytes (← jStr "hashes-rfc.json" e "saltHex")
    let info ← hexBytes (← jStr "hashes-rfc.json" e "infoHex")
    let l ← jNat "hashes-rfc.json" e "l"
    let prk ← hexBytes (← jStr "hashes-rfc.json" e "prkHex")
    let okm ← hexBytes (← jStr "hashes-rfc.json" e "okmHex")
    r.check s!"hkdf-sha256 {name} extract" (Hkdf.extract salt ikm == prk)
    r.check s!"hkdf-sha256 {name} expand" (Hkdf.expand prk info l == okm)
    r.check s!"hkdf-sha256 {name} one-shot" (Hkdf.expand (Hkdf.extract salt ikm) info l == okm)
    let backend ← optBytes "hkdf" (OpenSsl.hkdfSha256
      (Bytes.ofNatList salt) (Bytes.ofNatList ikm) (Bytes.ofNatList info)
      l.toUSize)
    r.check s!"hkdf-sha256 {name} (openssl cross-check)"
      (backend == Bytes.ofNatList okm)

  -- SHA-256: ByteArray entry point = List Nat original = OpenSSL
  for n in [0, 1, 55, 56, 63, 64, 65, 119, 120, 128, 1000] do
    let msg := patternBA n 31
    let viaList := Bytes.ofNatList (Sha256.digest (Bytes.toNatList msg))
    r.check s!"sha256 bytearray entry {n} = list model" (Sha256.digestB msg == viaList)
    let backend ← optBytes "sha256" (OpenSsl.sha256 msg)
    r.check s!"sha256 {n} (openssl cross-check)" (viaList == backend)

end Tests
