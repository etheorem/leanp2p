import Tests.Support
import Libp2p.Identity

/-!
# Identity signatures

The peer-ids specification fixes the signature schemes. Go fixtures pin the
three SHA-256 schemes; RFC 8032 pins Ed25519 over the original message.
These checks enter through checked identity keys and the real Crypto facade.
-/

set_option autoImplicit false

namespace Tests.KeySignatures

open Libp2p.Identity

private def privateKey (name : String) (keyType : KeyType) (raw : ByteArray) : IO PrivKey :=
  match PrivKey.ofData? keyType raw with
  | some key => pure key
  | none => throw <| IO.userError s!"invalid private fixture {name}"

private def publicKey (name : String) (keyType : KeyType) (raw : ByteArray) : IO PubKey :=
  match PubKey.ofData? keyType raw with
  | some key => pure key
  | none => throw <| IO.userError s!"invalid public fixture {name}"

private def checkVerification (r : Runner) (name : String) (key : PubKey)
    (msg sig : ByteArray) : IO Unit := do
  r.check s!"identity verifies {name}" (key.verify msg sig)
  r.check s!"identity rejects changed message {name}" (!key.verify (msg.push 0) sig)
  r.check s!"identity rejects changed signature {name}"
    (!key.verify msg (sig.set! 0 (sig[0]! ^^^ 1)))
  r.check s!"identity rejects empty signature {name}" (!key.verify msg .empty)
  r.check s!"identity rejects truncated signature {name}"
    (!key.verify msg (sig.extract 0 (sig.size - 1)))

def run (r : Runner) : IO Unit := do
  r.section "identity signatures" "peer-ids.md: Keys; Go crypto fixtures; RFC 8032 section 7.1"
  let file := "keys-go-libp2p.json"
  let goKeys ← loadJson file
  let msg ← unhex file (← jStr file goKeys "messageHex")
  for entry in (← jArr file goKeys "cases") do
    let name ← jStr file entry "name"
    let privBytes ← unhex name (← jStr file entry "privHex")
    let pubBytes ← unhex name (← jStr file entry "pubHex")
    let .ok priv := unmarshalPrivKey? privBytes
      | throw <| IO.userError s!"invalid private fixture {name}"
    let .ok pub := unmarshalPubKey? pubBytes
      | throw <| IO.userError s!"invalid public fixture {name}"
    let sig ← unhex name (← jStr file entry "sigHex")
    checkVerification r name pub msg sig
    match ← (priv.sign msg).run with
    | .error error => r.check s!"identity signs {name}: {repr error}" false
    | .ok own =>
        r.check s!"identity fresh signature verifies {name}" (pub.verify msg own)
        if priv.keyType == .rsa || priv.keyType == .secp256k1 then
          r.check s!"identity reproduces deterministic Go signature {name}" (own == sig)
          r.check s!"identity re-sign is byte-identical {name}"
            (succeedsWith sig (← (priv.sign msg).run))

    if priv.keyType == .ecdsa then
      -- RFC 5208 PrivateKeyInfo: version 0, id-ecPublicKey/prime256v1,
      -- then the fixture's 121-byte SEC1 key as an OCTET STRING.
      let pkcs8 := (← unhex "P-256 PKCS#8 header"
        "308193020100301306072a8648ce3d020106082a8648ce3d0301070479") ++ priv.raw
      let imported ← privateKey "P-256 PKCS#8" .ecdsa pkcs8
      r.check "identity preserves imported P-256 PKCS#8 bytes" (imported.raw == pkcs8)
      r.check "identity derives the P-256 PKCS#8 public key"
        (match derivePubKey imported with
         | .ok derived => derived.raw == pub.raw
         | .error _ => false)
      match ← (imported.sign msg).run with
      | .error error => r.check s!"identity signs P-256 PKCS#8: {repr error}" false
      | .ok own => r.check "identity verifies a P-256 PKCS#8 signature" (pub.verify msg own)

  let rfcFile := "keys-rfc8032.json"
  let rfc ← loadJson rfcFile
  for entry in (← jArr rfcFile rfc "ed25519") do
    let name ← jStr rfcFile entry "name"
    let seed ← unhex name (← jStr rfcFile entry "seedHex")
    let pubBytes ← unhex name (← jStr rfcFile entry "pubHex")
    let message ← unhex name (← jStr rfcFile entry "msgHex")
    let sig ← unhex name (← jStr rfcFile entry "sigHex")
    let pub ← publicKey name .ed25519 pubBytes
    checkVerification r name pub message sig
    for raw in [seed, seed ++ pubBytes, seed ++ pubBytes ++ pubBytes] do
      let priv ← privateKey name .ed25519 raw
      r.check s!"identity reproduces RFC signature {name}, private length {raw.size}"
        (succeedsWith sig (← (priv.sign message).run))

  let badDer := ByteArray.mk #[0x30, 0, 0, 0, 0, 0, 0, 0]
  for keyType in [KeyType.rsa, .ecdsa, .secp256k1] do
    let raw := if keyType == .secp256k1 then ByteArray.mk (Array.replicate 32 0) else badDer
    let priv ← privateKey "invalid backend key" keyType raw
    r.check s!"identity propagates invalid signing key {repr keyType}"
      (failsWith (.invalidKey : Crypto.CryptoError) (← (priv.sign msg).run))
  for keyType in [KeyType.rsa, .ecdsa] do
    let pub ← publicKey "invalid DER" keyType badDer
    r.check s!"identity rejects invalid verification key {repr keyType}"
      (!pub.verify msg (ByteArray.mk (Array.replicate 64 1)))

end Tests.KeySignatures
