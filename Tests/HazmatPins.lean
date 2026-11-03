import Tests.Support
import Tests.Backend
import Bytes
import Backend
import LeanHazmatKeccak
import LeanHazmatP256
import LeanHazmatSecp256k1

/-!
# The etheorem pin checks (unit W3.2, sub-unit 1a)

The pinned etheorem hazmat families (root ARCHITECTURE §4.6) build on
this repo's toolchain, link, and answer. `LeanHazmatSha256` is not
pinned. SHA-256 falls back to the backend binding (the backend PLAN,
"Pin outcomes"), and the hashes below come from it.

* `LeanHazmatKeccak`: the well-known keccak-256 digests of the empty
  string and of `abc`, two named fixed cases. The package's own suite
  is the family's main anchor. The W6.1 record fixture pins the
  end-to-end path through the facade.
* `LeanHazmatP256`: the go ECDSA fixture of `keys-go-libp2p.json`,
  verified through the family's raw `(r, s, qx, qy)` interface.
* `LeanHazmatSecp256k1`: the go secp256k1 fixture. The check recovers
  its key through `ecdsaRecover`, compares it with the fixture's
  compressed point, then verifies the signature.

The last check records why secp256k1 verification stays on the
backend. The family normalizes a high S before it verifies, so it
accepts the high-S twin of a valid signature. The low-S rule of §4.6
rejects that twin, and so does the backend verifier.
-/

set_option autoImplicit false

namespace Tests

open Bytes

def HazmatPins.run (r : Runner) : IO Unit := do
  r.section "etheorem hazmat pins" "etheorem/etheorem packages/hazmat at the pinned rev"

  -- Keccak-256 uses the pre-standard padding, which SHA3-256 changed.
  r.check "LeanHazmatKeccak: keccak-256 of the empty string"
    (toHex (LeanHazmat.Keccak.keccak256 .empty) ==
      "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
  r.check "LeanHazmatKeccak: keccak-256 of abc"
    (toHex (LeanHazmat.Keccak.keccak256 (ofString "abc")) ==
      "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45")

  -- The two ECDSA families over the go fixtures, with SHA-256 from the
  -- backend binding.
  let sha256 (b : ByteArray) : IO ByteArray :=
    match Backend.sha256 b with
    | .ok d => pure d
    | .error e => throw <| IO.userError s!"backend SHA-256 failed: {repr e}"
  let file := "keys-go-libp2p.json"
  let j ← loadJson file
  let msg ← unhex file (← jStr file j "messageHex")
  let hash ← sha256 msg
  let otherHash ← sha256 (ofString "abc")
  for c in ← jArr file j "cases" do
    let name ← jStr file c "name"
    -- RSA has no etheorem family. Only the two ECDSA cases parse a DER
    -- signature.
    unless name == "ecdsa" || name == "secp256k1" do continue
    let pub ← unhex file (← jStr file c "pubRawHex")
    let (r', s') ← Ecdsa.derSig file (← unhex file (← jStr file c "sigHex"))
    let sr := Ecdsa.bytesOfNat 32 r'
    let ss := Ecdsa.bytesOfNat 32 s'
    match name with
    | "ecdsa" =>
      -- The SPKI DER of an uncompressed P-256 key ends in `x ‖ y`.
      let qx := pub.extract (pub.size - 64) (pub.size - 32)
      let qy := pub.extract (pub.size - 32) pub.size
      r.check "LeanHazmatP256: verifies the go ECDSA fixture"
        (LeanHazmat.P256.p256Verify hash sr ss qx qy)
      r.check "LeanHazmatP256: a wrong hash fails"
        (!LeanHazmat.P256.p256Verify otherHash sr ss qx qy)
    | "secp256k1" =>
      -- Recover the 64-byte `x ‖ y` key. The right recovery id gives
      -- the fixture's compressed point (prefix 0x02 | parity of y).
      let compress (k : ByteArray) : ByteArray :=
        (ByteArray.mk #[0x02 ||| (k.get! 63 &&& 1)]) ++ k.extract 0 32
      let keys := [0, 1].map fun (id : UInt32) => LeanHazmat.Secp256k1.ecdsaRecover hash sr ss id
      match keys.find? fun k => k.size == 64 && compress k == pub with
      | none => r.check "LeanHazmatSecp256k1: recovers the go fixture key" false
      | some full =>
        r.check "LeanHazmatSecp256k1: recovers the go fixture key" true
        r.check "LeanHazmatSecp256k1: verifies the go fixture"
          (LeanHazmat.Secp256k1.ecdsaVerify hash sr ss full)
        -- The evidence for root §4.6: the etheorem verifier accepts a
        -- high S, so secp256k1 verification stays on the backend shim.
        let highS := Ecdsa.bytesOfNat 32 (Ecdsa.secp256k1Order - s')
        r.check "LeanHazmatSecp256k1 accepts the high-S twin (so verification stays on the backend)"
          (LeanHazmat.Secp256k1.ecdsaVerify hash sr highS full)
    | _ => pure ()

end Tests
