/-!
# Base58BTC

Bitcoin-alphabet base58 as used by libp2p peer ids (`Qm...`, `12D3KooW...`).
Nat arithmetic (bignum) keeps this simple; fine at peer-id scale.
-/

namespace LeanP2P.Base58

/-- Bitcoin base58 alphabet (also used by multibase base58btc). -/
def alphabet58 : String :=
  "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

private def alphabet : List Char := alphabet58.toList

private def toNatBE (bs : List Nat) : Nat :=
  bs.foldl (fun n b => n * 256 + b) 0

private def natToBE : Nat → List Nat
  | 0 => []
  | n+1 => natToBE ((n+1) / 256) ++ [(n+1) % 256]
termination_by n => n
decreasing_by omega

private def digit? (c : Char) : Option Nat :=
  alphabet.findIdx? (· == c)

private def digitsOf : Nat → List Char
  | 0 => []
  | n+1 => digitsOf ((n+1) / 58) ++ [alphabet.getD ((n+1) % 58) '1']
termination_by n => n
decreasing_by omega

/-- Base58btc encoding of raw bytes (each leading zero byte becomes '1'). -/
def encode (bs : List Nat) : String :=
  let zeros := (bs.takeWhile (· == 0)).length
  let n := toNatBE bs
  String.ofList (List.replicate zeros '1' ++ digitsOf n)

/-- Base58btc decoding to raw bytes. -/
def decode? (s : String) : Option (List Nat) := do
  let cs := s.toList
  let zeros := (cs.takeWhile (· == '1')).length
  let body := cs.dropWhile (· == '1')
  let n ← body.foldlM (fun n c => (fun d => n * 58 + d) <$> digit? c) 0
  let bytes := if n = 0 then [] else natToBE n
  some (List.replicate zeros 0 ++ bytes)

end LeanP2P.Base58
