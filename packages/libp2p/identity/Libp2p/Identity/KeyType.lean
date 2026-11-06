/-!
# The key types

The `KeyType` enum of the peer-ids spec, as a closed set (ARCHITECTURE
§3.4). The spec schema, which go-libp2p carries verbatim in
`core/crypto/pb/crypto.proto`:

```
enum KeyType { RSA = 0; Ed25519 = 1; Secp256k1 = 2; ECDSA = 3; }
```

The wire carries the code as a protobuf varint. `ofCode?` is the one
place where a code becomes a member, and a code outside the table is
`none`, so no bare `Nat` stands for a key type past that point.
-/

set_option autoImplicit false

namespace Libp2p.Identity

/-- The four key types of the peer-ids spec. -/
inductive KeyType where
  /-- RSA: SPKI DER public keys, PKCS#1 DER private keys. -/
  | rsa
  /-- Ed25519: raw 32-byte public keys. -/
  | ed25519
  /-- secp256k1: SEC1 compressed public points, raw 32-byte scalars. -/
  | secp256k1
  /-- ECDSA over P-256: SPKI DER public keys, SEC1 DER private keys. -/
  | ecdsa
  deriving DecidableEq, Repr, Hashable, Ord

namespace KeyType

/-- The wire code of a key type. -/
def toCode : KeyType → Nat
  | .rsa => 0
  | .ed25519 => 1
  | .secp256k1 => 2
  | .ecdsa => 3

/-- The key type of a wire code; `none` for every code the spec does
not assign. -/
def ofCode? : Nat → Option KeyType
  | 0 => some .rsa
  | 1 => some .ed25519
  | 2 => some .secp256k1
  | 3 => some .ecdsa
  | _ => none

-- Core Lean has no `Fintype`, so `decide` cannot quantify over the
-- constructors; `cases` splits the goal into one closed goal each, and
-- `decide` closes each one.

/-- The conformance proof of the table (§3.4). -/
theorem ofCodeToCode (t : KeyType) : ofCode? (toCode t) = some t := by
  cases t <;> decide

/-- A code the table accepts is the code of its key type. -/
theorem toCodeOfOfCode {n : Nat} {t : KeyType} (h : ofCode? n = some t) : toCode t = n := by
  unfold ofCode? at h
  split at h <;> cases h <;> rfl

/-- Every code fits one varint byte. -/
theorem toCodeLt (t : KeyType) : toCode t < 4 := by
  cases t <;> decide

/-- The name of the key type in the spec schema (`enum KeyType`). Lean
cannot derive `ToString`, and §3.2 asks for one that prints the text
form of the spec, so it is written out. -/
def name : KeyType → String
  | .rsa => "RSA"
  | .ed25519 => "Ed25519"
  | .secp256k1 => "Secp256k1"
  | .ecdsa => "ECDSA"

instance : ToString KeyType := ⟨name⟩

example : toString KeyType.secp256k1 = "Secp256k1" := rfl

end KeyType

/-- The first unassigned code is not a key type: the strict-rejection
milestone of the package plan. -/
example : KeyType.ofCode? 4 = none := rfl

end Libp2p.Identity
