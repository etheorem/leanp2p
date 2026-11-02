import Tests.Support
import CryptoPure

/-!
# Hash, HMAC, and HKDF suite

Mirrors `hashes-rfc.json`, which holds the FIPS 180-4 SHA-512 examples
and the HMAC and HKDF vectors. RFC 4231 TC6 and TC7 check long keys
with SHA-256 and SHA-512. The SHA-256 cases also include TC1 and TC2,
and HKDF-SHA-256 uses RFC 5869 TC1 and TC3.

The suite also checks the digest bytes in the `sha1` and `sha2-256`
cases of `multihash-examples.json`, after their two-byte prefix. The
NIST SHA-256 examples and the SHA-1 `abc` example are inline. Each
digest vector runs through both forms of the pure copy, the model
`digest` and its `ByteArray` form `digestB`, against the published
bytes.

The sweeps are this package's own tests. Each length checks the model
pin of `digestB` and the digest size. Named length lists let the W3.3
cross-check run the same inputs through the production path.
-/

set_option autoImplicit false

namespace Tests

open CryptoPure

/-- A deterministic test buffer of `n` bytes: byte `i` is `i * mult mod 256`. -/
def Hashes.pattern (n mult : Nat) : List Nat :=
  (List.range n).map fun i => i * mult % 256

/-- The spike's SHA-256 and SHA-1 lengths around padding and block
boundaries. -/
def Hashes.sha256Lengths : List Nat :=
  [0, 1, 55, 56, 63, 64, 65, 119, 120, 128, 1000]

/-- The spike's SHA-512 lengths: 0 to 300, the lengths around 512, and
two larger messages. -/
def Hashes.sha512Lengths : List Nat :=
  List.range 301 ++ [511, 512, 513, 1000, 4096]

/-- The spike's HMAC-SHA-256 key lengths, including empty keys and keys
below, at, and above the block size. -/
def Hashes.hmacKeyLengths : List Nat :=
  [0, 1, 63, 64, 65, 128, 200]

/-- Reads a hex vector field as model bytes. Invalid hex is a corpus
error, so it throws. -/
private def hexField (file : String) (j : Lean.Json) (k : String) : IO (List Nat) := do
  let h ← jStr file j k
  match Mock.Bytes.ofHex? h with
  | some b => pure (Mock.Bytes.toNatList b)
  | none => throw <| IO.userError s!"{file}: bad hex in {k}"

/-- Checks that `digestB` agrees with the model and has the expected size. -/
private def pinHolds (digest : List Nat → List Nat) (digestB : ByteArray → ByteArray)
    (size : Nat) (msg : ByteArray) : Bool :=
  let viaModel := Mock.Bytes.ofNatList (digest (Mock.Bytes.toNatList msg))
  digestB msg == viaModel && (digestB msg).size == size

/-- Checks a digest vector through both forms of the pure copy: the
model `digest` and its `ByteArray` form `digestB`. -/
private def bothForms (digest : List Nat → List Nat) (digestB : ByteArray → ByteArray)
    (input expected : List Nat) : Bool :=
  digest input == expected &&
    digestB (Mock.Bytes.ofNatList input) == Mock.Bytes.ofNatList expected

/-- Runs the RFC, NIST, and multihash vectors, the HKDF cap checks, and
the length sweeps. -/
def Hashes.run (r : Runner) : IO Unit := do
  r.section "hashes" "hashes-rfc.json (FIPS 180-4, RFC 4231, RFC 5869); \
multihash-examples.json (sha1, sha2-256); NIST SHA-256/SHA-1 examples"

  let file := "hashes-rfc.json"
  let j ← loadJson file

  for e in (← jArr file j "sha512") do
    let name ← jStr file e "name"
    let input ← hexField file e "inputHex"
    let expected ← hexField file e "digestHex"
    r.check s!"sha512 {name}" (bothForms Sha512.digest Sha512.digestB input expected)

  let hmacFamilies : List (String × (List Nat → List Nat → List Nat)) :=
    [("hmacSha256", Hmac.sha256), ("hmacSha512", Hmac.sha512)]
  for (family, hmac) in hmacFamilies do
    for e in (← jArr file j family) do
      let name ← jStr file e "name"
      let mac := hmac (← hexField file e "keyHex") (← hexField file e "dataHex")
      r.check s!"{family} {name}" (mac == (← hexField file e "macHex"))

  for e in (← jArr file j "hkdfSha256") do
    let name ← jStr file e "name"
    let ikm ← hexField file e "ikmHex"
    let salt ← hexField file e "saltHex"
    let info ← hexField file e "infoHex"
    let l ← jNat file e "l"
    let prk ← hexField file e "prkHex"
    let okm ← hexField file e "okmHex"
    r.check s!"hkdf-sha256 {name} extract" (Hkdf.extractSha256 salt ikm == prk)
    r.check s!"hkdf-sha256 {name} expand" (Hkdf.expandSha256 prk info l == some okm)
    r.check s!"hkdf-sha256 {name} one-shot"
      (Hkdf.expandSha256 (Hkdf.extractSha256 salt ikm) info l == some okm)

  -- RFC 5869 §2.3 caps the output at 255 × 32 bytes for SHA-256.
  let prk := Hashes.pattern 32 1
  r.check "hkdf-sha256 expand at the cap gives 8160 bytes"
    ((Hkdf.expandSha256 prk [] 8160).map List.length == some 8160)
  r.check "hkdf-sha256 expand past the cap is none"
    (Hkdf.expandSha256 prk [] 8161 == none)

  let nist : List (String × (List Nat → List Nat) × (ByteArray → ByteArray) ×
      String × String) :=
    [("sha256", Sha256.digest, Sha256.digestB, "",
       "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
     ("sha256", Sha256.digest, Sha256.digestB, "abc",
       "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
     ("sha256", Sha256.digest, Sha256.digestB,
       "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
       "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
     ("sha1", Sha1.digest, Sha1.digestB, "abc", "a9993e364706816aba3e25717850c26c9cd0d89d")]
  for (alg, digest, digestB, msg, want) in nist do
    let wantBytes := (Mock.Bytes.ofHex? want).map Mock.Bytes.toNatList
    let input := Mock.Bytes.toNatList (Mock.Bytes.ofString msg)
    r.check s!"{alg} nist \"{msg}\"" (wantBytes.any (bothForms digest digestB input))

  -- The multihash value is the code byte, the length byte, then the digest.
  let mhFile := "multihash-examples.json"
  let mh ← loadJson mhFile
  for c in (← jArr mhFile mh "cases") do
    let alg ← jStr mhFile c "algorithm"
    let msg := Mock.Bytes.toNatList (Mock.Bytes.ofString (← jStr mhFile c "input"))
    for enc in (← jArr mhFile c "encodings") do
      if (← jStr mhFile enc "kind") == "hex" then
        let digestBytes := (← hexField mhFile enc "value").drop 2
        match alg with
        | "sha1" =>
          r.check "multihash sha1 digest bytes"
            (bothForms Sha1.digest Sha1.digestB msg digestBytes)
        | "sha2-256" =>
          r.check "multihash sha2-256 digest bytes"
            (bothForms Sha256.digest Sha256.digestB msg digestBytes)
        | other => r.skip s!"multihash {other}" "no pure copy of this hash"

  let sweep (name : String) (lengths : List Nat) (mult : Nat) (digest : List Nat → List Nat)
      (digestB : ByteArray → ByteArray) (size : Nat) : IO Unit := do
    let bad := lengths.filter fun n =>
      !pinHolds digest digestB size (Mock.Bytes.ofNatList (Hashes.pattern n mult))
    r.check s!"{name} digestB pin and size over {lengths.length} lengths (failing: {bad})"
      bad.isEmpty
  sweep "sha256" Hashes.sha256Lengths 31 Sha256.digest Sha256.digestB Sha256.digestSize
  sweep "sha1" Hashes.sha256Lengths 31 Sha1.digest Sha1.digestB Sha1.digestSize
  sweep "sha512" Hashes.sha512Lengths 7 Sha512.digest Sha512.digestB Sha512.digestSize

  let badKeys := Hashes.hmacKeyLengths.filter fun n =>
    (Hmac.sha256 (Hashes.pattern n 11) [0x68, 0x69]).length != Sha256.digestSize
  r.check s!"hmac-sha256 key lengths {Hashes.hmacKeyLengths} give 32-byte MACs (failing: {badKeys})"
    badKeys.isEmpty

end Tests
