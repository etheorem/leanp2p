import Tests.Support
import Libp2p.Identity

/-!
# Key and peer-id suite

The key-type codes follow `vendor/specs/peer-ids/peer-ids.md`.
-/

set_option autoImplicit false

namespace Tests

open Libp2p.Identity

def Keys.run (r : Runner) : IO Unit := do
  r.section "key types" "libp2p/specs peer-ids.md: KeyType"
  for (code, keyType) in
      ([(0, .rsa), (1, .ed25519), (2, .secp256k1), (3, .ecdsa)] :
        List (Nat × KeyType)) do
    r.check s!"key type encodes as {code}" (keyType.toCode == code)
    r.check s!"key type decodes from {code}" (KeyType.ofCode? code == some keyType)
  r.check "key type rejects code 4" (KeyType.ofCode? 4 == none)

end Tests
