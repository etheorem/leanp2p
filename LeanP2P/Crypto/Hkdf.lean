import LeanP2P.Crypto.Hmac
/-!
# HKDF-SHA-256 (RFC 5869)

`extract` and `expand` over the `List Nat` model. Verified against the RFC
5869 test vectors in `Tests/Hashes` (the Noise handshake in phase 3 uses
exactly this construction with `salt = handshake hash`).
-/

namespace LeanP2P.Hkdf

def extract (salt ikm : List Nat) : List Nat :=
  Hmac.hmac (if salt = [] then List.replicate 32 0 else salt) ikm

private partial def go (prk info : List Nat) (l i : Nat) (acc : List Nat) :
    List Nat :=
  if acc.length ≥ l then acc.take l
  else
    -- previous output block; the first round has none (RFC 5869, step 2)
    let prev := acc.drop (acc.length - 32)
    let block := Hmac.hmac prk (prev ++ info ++ [i])
    go prk info l (i + 1) (acc ++ block)

def expand (prk : List Nat) (info : List Nat) (l : Nat) : List Nat :=
  go prk info l 1 []

end LeanP2P.Hkdf
