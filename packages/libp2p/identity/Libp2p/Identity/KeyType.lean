import Std

/-!
# Key types

The four key types and their codes from `vendor/specs/peer-ids/peer-ids.md`.
-/

set_option autoImplicit false

namespace Libp2p.Identity

inductive KeyType where
  | rsa
  | ed25519
  | secp256k1
  | ecdsa
  deriving BEq, DecidableEq, Hashable, Ord, Repr

instance : ToString KeyType where
  toString
    | .rsa => "rsa"
    | .ed25519 => "ed25519"
    | .secp256k1 => "secp256k1"
    | .ecdsa => "ecdsa"

def KeyType.toCode : KeyType → Nat
  | .rsa => 0
  | .ed25519 => 1
  | .secp256k1 => 2
  | .ecdsa => 3

def KeyType.ofCode? : Nat → Option KeyType
  | 0 => some .rsa
  | 1 => some .ed25519
  | 2 => some .secp256k1
  | 3 => some .ecdsa
  | _ => none

theorem KeyType.ofCode?_toCode (t : KeyType) : ofCode? (toCode t) = some t := by
  cases t <;> decide

end Libp2p.Identity
