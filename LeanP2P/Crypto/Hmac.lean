import LeanP2P.Crypto.Sha256
/-!
# HMAC-SHA-256 (RFC 2104)

Pure construction over the `List Nat` model, block size 64 bytes.
Verified against the RFC 4231 test vectors in `Tests/Hashes` and
cross-checked against OpenSSL at the IO edge.
-/

namespace LeanP2P.Hmac

def blockSize : Nat := 64

/-- Key normalization: keys longer than the block are hashed, then the
result is zero-padded to the block size (RFC 2104). -/
def normKey (key : List Nat) : List Nat :=
  let k := if key.length > blockSize then Sha256.digest key else key
  k ++ List.replicate (blockSize - k.length) 0

def hmac (key : List Nat) (msg : List Nat) : List Nat :=
  let k := normKey key
  let ipad := k.map (fun b => b ^^^ 0x36)
  let opad := k.map (fun b => b ^^^ 0x5c)
  Sha256.digest (opad ++ Sha256.digest (ipad ++ msg))

end LeanP2P.Hmac
