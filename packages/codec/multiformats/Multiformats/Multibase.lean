import Multiformats.Tables
import Multiformats.Base58
import Multiformats.BitBase

/-!
# Registered multibase encodings

The prefix is a Unicode character. Reserved registry rows are rejected.
Base45 follows RFC 9285. Proquint follows the pinned sixteen-bit word
format and adds the required `ro-` after the `p` prefix. Its checked
encoder rejects an odd byte count instead of silently padding data.
-/

set_option autoImplicit false

namespace Multiformats.Multibase

/-- Optional alphabet lookup becomes a typed parser failure. -/
private def require {α : Type} (value : Option α) (error : Error) : Except Error α :=
  match value with
  | some value => .ok value
  | none => .error error

/-- The RFC 4648 base32 alphabet, shared by both case variants. -/
private def b32 : String := "abcdefghijklmnopqrstuvwxyz234567"

/-- The extended-hex variant keeps the same bit layout. -/
private def b32hex : String := "0123456789abcdefghijklmnopqrstuv"

/-- The z-base-32 alphabet is case-sensitive. -/
private def b32z : String := "ybndrfg8ejkmcpqxot1uwisza345h769"

/-- The standard base64 alphabet. -/
private def b64 : String := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

/-- The URL form replaces the two punctuation digits. -/
private def b64url : String := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"

/-- Base45 uses the QR alphanumeric character set in the RFC's order. -/
private def b45 : List Char := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:".toList

/-- A byte pair uses three little-endian base45 digits; a final byte uses two. -/
private def encode45 : List UInt8 → List Char
  | [] => []
  | [a] => [b45.getD (a.toNat % 45) '?', b45.getD (a.toNat / 45) '?']
  | a :: b :: rest =>
      let value := a.toNat * 256 + b.toNat
      [b45.getD (value % 45) '?', b45.getD (value / 45 % 45) '?',
        b45.getD (value / 2025) '?'] ++ encode45 rest

/-- Numeric bounds distinguish a final byte from a pair and reject overflow. -/
private def decode45 : List Char → Except Error (List Nat)
  | [] => .ok []
  | [_] => .error .badBaseValue
  | [a, b] => do
      let x ← require (b45.findIdx? (· == a)) .badBaseValue
      let y ← require (b45.findIdx? (· == b)) .badBaseValue
      let value := x + y * 45
      if value ≥ 256 then .error .badBaseValue else .ok [value]
  | a :: b :: c :: rest => do
      let x ← require (b45.findIdx? (· == a)) .badBaseValue
      let y ← require (b45.findIdx? (· == b)) .badBaseValue
      let z ← require (b45.findIdx? (· == c)) .badBaseValue
      let value := x + y * 45 + z * 2025
      if value ≥ 65536 then .error .badBaseValue
      else .ok ([value / 256, value % 256] ++ (← decode45 rest))

/-- Four bits per consonant and two bits per vowel make one sixteen-bit word. -/
private def consonants : List Char := "bdfghjklmnprstvz".toList

/-- The original specification uses four vowels. -/
private def vowels : List Char := "aiou".toList

/-- A word is rendered most-significant group first. -/
private def quint (n : Nat) : String := String.ofList [
  consonants.getD (n / 4096 % 16) '?', vowels.getD (n / 1024 % 4) '?',
  consonants.getD (n / 64 % 16) '?', vowels.getD (n / 16 % 4) '?',
  consonants.getD (n % 16) '?']

/-- Only whole sixteen-bit words have a representation in the pinned Proquint format. -/
private def proquintWords : List UInt8 → Except Error (List String)
  | [] => .ok []
  | [_] => .error .badBaseValue
  | a :: b :: rest => do
      .ok (quint (a.toNat * 256 + b.toNat) :: (← proquintWords rest))

/-- Every position has its own alphabet, so a malformed word is rejected. -/
private def readQuint (s : String) : Except Error (List Nat) := do
  match s.toList with
  | [a, b, c, d, e] =>
      let a ← require (consonants.findIdx? (· == a)) .badBaseValue
      let b ← require (vowels.findIdx? (· == b)) .badBaseValue
      let c ← require (consonants.findIdx? (· == c)) .badBaseValue
      let d ← require (vowels.findIdx? (· == d)) .badBaseValue
      let e ← require (consonants.findIdx? (· == e)) .badBaseValue
      let n := a * 4096 + b * 1024 + c * 64 + d * 16 + e
      .ok [n / 256, n % 256]
  | _ => .error .badBaseValue

/-- The checked entry point makes the Proquint input domain explicit. -/
def encode? (base : Base) (data : ByteArray) : Except Error String := do
  let body ← match base with
    | .base2 => .ok (BitBase.encode 1 "01" 0 data)
    | .base8 => .ok (BitBase.encode 3 "01234567" 0 data)
    | .base10 => .ok (Radix.encode "0123456789" data)
    | .base16 => .ok (BitBase.encode 4 "0123456789abcdef" 0 data)
    | .base16upper => .ok (BitBase.encode 4 "0123456789ABCDEF" 0 data)
    | .base32 => .ok (BitBase.encode 5 b32 0 data)
    | .base32upper => .ok (BitBase.encode 5 b32.toUpper 0 data)
    | .base32hex => .ok (BitBase.encode 5 b32hex 0 data)
    | .base32hexupper => .ok (BitBase.encode 5 b32hex.toUpper 0 data)
    | .base32pad => .ok (BitBase.encode 5 b32 8 data)
    | .base32padupper => .ok (BitBase.encode 5 b32.toUpper 8 data)
    | .base32hexpad => .ok (BitBase.encode 5 b32hex 8 data)
    | .base32hexpadupper => .ok (BitBase.encode 5 b32hex.toUpper 8 data)
    | .base32z => .ok (BitBase.encode 5 b32z 0 data)
    | .base36 => .ok (Radix.encode "0123456789abcdefghijklmnopqrstuvwxyz" data)
    | .base36upper => .ok ((Radix.encode "0123456789abcdefghijklmnopqrstuvwxyz" data).toUpper)
    | .base58btc => .ok (Base58.encode data)
    | .base58flickr => .ok (Base58.encodeFlickr data)
    | .base64 => .ok (BitBase.encode 6 b64 0 data)
    | .base64pad => .ok (BitBase.encode 6 b64 4 data)
    | .base64url => .ok (BitBase.encode 6 b64url 0 data)
    | .base64urlpad => .ok (BitBase.encode 6 b64url 4 data)
    | .base45 => .ok (String.ofList (encode45 data.toList))
    | .proquint => do .ok ("ro-" ++ String.intercalate "-" (← proquintWords data.toList))
    | .base256emoji => .ok (String.ofList (data.toList.map fun b => emojiAlphabet.getD b.toNat '?'))
  .ok (String.singleton base.prefixChar ++ body)

/-- The fixed base32 encoder cannot reach Proquint's domain error. -/
def encodeBase32 (data : ByteArray) : String :=
  match h : encode? .base32 data with
  | .ok text => text
  | .error _ => by simp [encode?, Bind.bind, Except.bind] at h

/-- Prefix dispatch follows the generated registry and retains the chosen base. -/
def decode? (text : String) : Except Error (Base × ByteArray) := do
  match text.toList with
  | [] => .error .unknownBase
  | codepoint :: chars =>
      let base ← require (Base.ofCode? codepoint.toNat) .unknownBase
      let body := String.ofList chars
      let bytes ← match base with
        | .base2 => BitBase.decode? 1 "01" false 0 body
        | .base8 => BitBase.decode? 3 "01234567" false 0 body
        | .base10 => Radix.decode? "0123456789" false body
        | .base16 | .base16upper => BitBase.decode? 4 "0123456789abcdef" true 0 body
        | .base32 | .base32upper => BitBase.decode? 5 b32 true 0 body
        | .base32hex | .base32hexupper => BitBase.decode? 5 b32hex true 0 body
        | .base32pad | .base32padupper => BitBase.decode? 5 b32 true 8 body
        | .base32hexpad | .base32hexpadupper => BitBase.decode? 5 b32hex true 8 body
        | .base32z => BitBase.decode? 5 b32z false 0 body
        | .base36 | .base36upper => Radix.decode? "0123456789abcdefghijklmnopqrstuvwxyz" true body
        | .base58btc => Base58.decode? body
        | .base58flickr => Base58.decodeFlickr? body
        | .base64 => BitBase.decode? 6 b64 false 0 body
        | .base64pad => BitBase.decode? 6 b64 false 4 body
        | .base64url => BitBase.decode? 6 b64url false 0 body
        | .base64urlpad => BitBase.decode? 6 b64url false 4 body
        | .base45 => Bytes.ofNatList <$> decode45 chars
        | .proquint => do
            if !body.startsWith "ro-" then .error .badBaseValue
            else
              let words := String.ofList (chars.drop 3)
              let values ← if words.isEmpty then pure [] else (words.splitOn "-").mapM readQuint
              .ok (Bytes.ofNatList values.flatten)
        | .base256emoji => do
            let values ← chars.mapM fun c => require (emojiAlphabet.findIdx? (· == c)) .badBaseValue
            .ok (Bytes.ofNatList values)
      .ok (base, bytes)

end Multiformats.Multibase
