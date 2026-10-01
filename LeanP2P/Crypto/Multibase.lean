import LeanP2P.Crypto.Bytes
import LeanP2P.Crypto.Base58
/-!
# Multibase

`Multibase.encode : Base → ByteArray → String` and
`decode? : String → Option (Base × ByteArray)` for the bases of the
multiformats/multibase table (README, "Multibase registry"): identity, base2,
base8, base10, base16 (both cases), base32 (lower/upper, pad/no-pad, hex
variants, z), base36 (both cases), base58btc, base58flickr, base64,
base64pad, base64url, base64urlpad and base256emoji.

Conformance notes (validated against `multiformats/multibase/tests/*.csv`,
pinned in VECTORS.lock):

- power-of-two bases (2, 8, 16, 32, 32hex, 32z, 64) are bit sliced
  MSB-first; the final group is zero-padded on the right, and pad variants
  append `=` to a multiple of 8 (base32) / 4 (base64) digits;
- big-integer bases (10, 36, 58btc, 58flickr) convert the whole byte string
  as one big-endian number and emit one zero digit per leading zero byte;
- decoding is case-insensitive exactly for the alphabets where case carries
  no information (16, 32, 32hex, 36); base58btc / base58flickr / base64 are
  case-sensitive;
- base256emoji maps each byte to a fixed codepoint (rfcs/Base256Emoji.md).

`identity` is the pass-through "base": its string form is the payload bytes
themselves, so round-tripping is only meaningful for valid UTF-8 payloads.
-/

namespace LeanP2P.Multibase

inductive Base where
  | identity | base2 | base8 | base10
  | base16 | base16upper
  | base32 | base32upper
  | base32hex | base32hexupper
  | base32pad | base32padupper
  | base32hexpad | base32hexpadupper
  | base32z
  | base36 | base36upper
  | base58btc | base58flickr
  | base64 | base64pad | base64url | base64urlpad
  | base256emoji
deriving Repr, BEq, DecidableEq

/-- Multibase prefix codepoint (registry column "key"). -/
def prefixChar : Base → Char
  | .identity => '\x00'
  | .base2 => '0'
  | .base8 => '7'
  | .base10 => '9'
  | .base16 => 'f'
  | .base16upper => 'F'
  | .base32 => 'b'
  | .base32upper => 'B'
  | .base32hex => 'v'
  | .base32hexupper => 'V'
  | .base32pad => 'c'
  | .base32padupper => 'C'
  | .base32hexpad => 't'
  | .base32hexpadupper => 'T'
  | .base32z => 'h'
  | .base36 => 'k'
  | .base36upper => 'K'
  | .base58btc => 'z'
  | .base58flickr => 'Z'
  | .base64 => 'm'
  | .base64pad => 'M'
  | .base64url => 'u'
  | .base64urlpad => 'U'
  | .base256emoji => '🚀'

/-! ## Alphabets -/

def alphabetB32 : String := "abcdefghijklmnopqrstuvwxyz234567"
def alphabetB32Hex : String := "0123456789abcdefghijklmnopqrstuv"
def alphabetB32Z : String := "ybndrfg8ejkmcpqxot1uwisza345h769"
def alphabetB36 : String := "0123456789abcdefghijklmnopqrstuvwxyz"
def alphabetB58Flickr : String :=
  "123456789abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ"
def alphabetB64 : String :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
def alphabetB64Url : String :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"

/-- The base256emoji table: `emojiOfByte b` is the codepoint encoding byte
`b` (rfcs/Base256Emoji.md). -/
def emojiOfByte : Nat → Char
  | 0 => '🚀'
  | 1 => '🪐'
  | 2 => '\u2604'
  | 3 => '🛰'
  | 4 => '🌌'
  | 5 => '🌑'
  | 6 => '🌒'
  | 7 => '🌓'
  | 8 => '🌔'
  | 9 => '🌕'
  | 10 => '🌖'
  | 11 => '🌗'
  | 12 => '🌘'
  | 13 => '🌍'
  | 14 => '🌏'
  | 15 => '🌎'
  | 16 => '🐉'
  | 17 => '\u2600'
  | 18 => '💻'
  | 19 => '🖥'
  | 20 => '💾'
  | 21 => '💿'
  | 22 => '😂'
  | 23 => '\u2764'
  | 24 => '😍'
  | 25 => '🤣'
  | 26 => '😊'
  | 27 => '🙏'
  | 28 => '💕'
  | 29 => '😭'
  | 30 => '😘'
  | 31 => '👍'
  | 32 => '😅'
  | 33 => '👏'
  | 34 => '😁'
  | 35 => '🔥'
  | 36 => '🥰'
  | 37 => '💔'
  | 38 => '💖'
  | 39 => '💙'
  | 40 => '😢'
  | 41 => '🤔'
  | 42 => '😆'
  | 43 => '🙄'
  | 44 => '💪'
  | 45 => '😉'
  | 46 => '\u263a'
  | 47 => '👌'
  | 48 => '🤗'
  | 49 => '💜'
  | 50 => '😔'
  | 51 => '😎'
  | 52 => '😇'
  | 53 => '🌹'
  | 54 => '🤦'
  | 55 => '🎉'
  | 56 => '💞'
  | 57 => '\u270c'
  | 58 => '\u2728'
  | 59 => '🤷'
  | 60 => '😱'
  | 61 => '😌'
  | 62 => '🌸'
  | 63 => '🙌'
  | 64 => '😋'
  | 65 => '💗'
  | 66 => '💚'
  | 67 => '😏'
  | 68 => '💛'
  | 69 => '🙂'
  | 70 => '💓'
  | 71 => '🤩'
  | 72 => '😄'
  | 73 => '😀'
  | 74 => '🖤'
  | 75 => '😃'
  | 76 => '💯'
  | 77 => '🙈'
  | 78 => '👇'
  | 79 => '🎶'
  | 80 => '😒'
  | 81 => '🤭'
  | 82 => '\u2763'
  | 83 => '😜'
  | 84 => '💋'
  | 85 => '👀'
  | 86 => '😪'
  | 87 => '😑'
  | 88 => '💥'
  | 89 => '🙋'
  | 90 => '😞'
  | 91 => '😩'
  | 92 => '😡'
  | 93 => '🤪'
  | 94 => '👊'
  | 95 => '🥳'
  | 96 => '😥'
  | 97 => '🤤'
  | 98 => '👉'
  | 99 => '💃'
  | 100 => '😳'
  | 101 => '\u270b'
  | 102 => '😚'
  | 103 => '😝'
  | 104 => '😴'
  | 105 => '🌟'
  | 106 => '😬'
  | 107 => '🙃'
  | 108 => '🍀'
  | 109 => '🌷'
  | 110 => '😻'
  | 111 => '😓'
  | 112 => '\u2b50'
  | 113 => '\u2705'
  | 114 => '🥺'
  | 115 => '🌈'
  | 116 => '😈'
  | 117 => '🤘'
  | 118 => '💦'
  | 119 => '\u2714'
  | 120 => '😣'
  | 121 => '🏃'
  | 122 => '💐'
  | 123 => '\u2639'
  | 124 => '🎊'
  | 125 => '💘'
  | 126 => '😠'
  | 127 => '\u261d'
  | 128 => '😕'
  | 129 => '🌺'
  | 130 => '🎂'
  | 131 => '🌻'
  | 132 => '😐'
  | 133 => '🖕'
  | 134 => '💝'
  | 135 => '🙊'
  | 136 => '😹'
  | 137 => '🗣'
  | 138 => '💫'
  | 139 => '💀'
  | 140 => '👑'
  | 141 => '🎵'
  | 142 => '🤞'
  | 143 => '😛'
  | 144 => '🔴'
  | 145 => '😤'
  | 146 => '🌼'
  | 147 => '😫'
  | 148 => '\u26bd'
  | 149 => '🤙'
  | 150 => '\u2615'
  | 151 => '🏆'
  | 152 => '🤫'
  | 153 => '👈'
  | 154 => '😮'
  | 155 => '🙆'
  | 156 => '🍻'
  | 157 => '🍃'
  | 158 => '🐶'
  | 159 => '💁'
  | 160 => '😲'
  | 161 => '🌿'
  | 162 => '🧡'
  | 163 => '🎁'
  | 164 => '\u26a1'
  | 165 => '🌞'
  | 166 => '🎈'
  | 167 => '\u274c'
  | 168 => '\u270a'
  | 169 => '👋'
  | 170 => '😰'
  | 171 => '🤨'
  | 172 => '😶'
  | 173 => '🤝'
  | 174 => '🚶'
  | 175 => '💰'
  | 176 => '🍓'
  | 177 => '💢'
  | 178 => '🤟'
  | 179 => '🙁'
  | 180 => '🚨'
  | 181 => '💨'
  | 182 => '🤬'
  | 183 => '\u2708'
  | 184 => '🎀'
  | 185 => '🍺'
  | 186 => '🤓'
  | 187 => '😙'
  | 188 => '💟'
  | 189 => '🌱'
  | 190 => '😖'
  | 191 => '👶'
  | 192 => '🥴'
  | 193 => '\u25b6'
  | 194 => '\u27a1'
  | 195 => '\u2753'
  | 196 => '💎'
  | 197 => '💸'
  | 198 => '\u2b07'
  | 199 => '😨'
  | 200 => '🌚'
  | 201 => '🦋'
  | 202 => '😷'
  | 203 => '🕺'
  | 204 => '\u26a0'
  | 205 => '🙅'
  | 206 => '😟'
  | 207 => '😵'
  | 208 => '👎'
  | 209 => '🤲'
  | 210 => '🤠'
  | 211 => '🤧'
  | 212 => '📌'
  | 213 => '🔵'
  | 214 => '💅'
  | 215 => '🧐'
  | 216 => '🐾'
  | 217 => '🍒'
  | 218 => '😗'
  | 219 => '🤑'
  | 220 => '🌊'
  | 221 => '🤯'
  | 222 => '🐷'
  | 223 => '\u260e'
  | 224 => '💧'
  | 225 => '😯'
  | 226 => '💆'
  | 227 => '👆'
  | 228 => '🎤'
  | 229 => '🙇'
  | 230 => '🍑'
  | 231 => '\u2744'
  | 232 => '🌴'
  | 233 => '💣'
  | 234 => '🐸'
  | 235 => '💌'
  | 236 => '📍'
  | 237 => '🥀'
  | 238 => '🤢'
  | 239 => '👅'
  | 240 => '💡'
  | 241 => '💩'
  | 242 => '👐'
  | 243 => '📸'
  | 244 => '👻'
  | 245 => '🤐'
  | 246 => '🤮'
  | 247 => '🎼'
  | 248 => '🥵'
  | 249 => '🚩'
  | 250 => '🍎'
  | 251 => '🍊'
  | 252 => '👼'
  | 253 => '💍'
  | 254 => '📣'
  | 255 => '🥂'
  | _ => '🚀'

/-- Reverse lookup for `emojiOfByte`. -/
def emojiToByte? (c : Char) : Option Nat :=
  emojiToByteTable.findIdx? (· == c)
where
  emojiToByteTable : List Char := "🚀🪐☄🛰🌌🌑🌒🌓🌔🌕🌖🌗🌘🌍🌏🌎🐉☀💻🖥💾💿😂❤😍🤣😊🙏💕😭😘👍😅👏😁🔥🥰💔💖💙😢🤔😆🙄💪😉☺👌🤗💜😔😎😇🌹🤦🎉💞✌✨🤷😱😌🌸🙌😋💗💚😏💛🙂💓🤩😄😀🖤😃💯🙈👇🎶😒🤭❣😜💋👀😪😑💥🙋😞😩😡🤪👊🥳😥🤤👉💃😳✋😚😝😴🌟😬🙃🍀🌷😻😓⭐✅🥺🌈😈🤘💦✔😣🏃💐☹🎊💘😠☝😕🌺🎂🌻😐🖕💝🙊😹🗣💫💀👑🎵🤞😛🔴😤🌼😫⚽🤙☕🏆🤫👈😮🙆🍻🍃🐶💁😲🌿🧡🎁⚡🌞🎈❌✊👋😰🤨😶🤝🚶💰🍓💢🤟🙁🚨💨🤬✈🎀🍺🤓😙💟🌱😖👶🥴▶➡❓💎💸⬇😨🌚🦋😷🕺⚠🙅😟😵👎🤲🤠🤧📌🔵💅🧐🐾🍒😗🤑🌊🤯🐷☎💧😯💆👆🎤🙇🍑❄🌴💣🐸💌📍🥀🤢👅💡💩👐📸👻🤐🤮🎼🥵🚩🍎🍊👼💍📣🥂".toList

/-! ## Encoding -/

private def digitOf (alpha : String) (i : Nat) : Char :=
  alpha.toList.getD i '?'

/-- Bit-slice encoder for power-of-two bases: MSB-first groups of `bits`,
final group zero-padded, then `=` padding to a multiple of `padTo`
(pass 0 for the unpadded forms). -/
private def pow2Encode (bits : Nat) (alpha : String) (padTo : Nat)
    (bs : ByteArray) : String :=
  Id.run do
    let mut out := ""
    let mut acc : Nat := 0
    let mut accBits := 0
    for b in bs do
      acc := acc * 256 + b.toNat
      accBits := accBits + 8
      while accBits ≥ bits do
        let shift := accBits - bits
        let d := (acc / (2 ^ shift)) % (2 ^ bits)
        out := out.push (digitOf alpha d)
        acc := acc % (2 ^ shift)
        accBits := shift
    if accBits > 0 then
      let d := (acc * 2 ^ (bits - accBits)) % (2 ^ bits)
      out := out.push (digitOf alpha d)
      accBits := 0
    if padTo > 0 then
      while out.length % padTo != 0 do
        out := out.push '='
    return out

/-- Big-integer encoder for the non-power-of-two bases: one zero digit per
leading zero byte, then the whole value in base `radix`. -/
private def bigEncode (radix : Nat) (alpha : String) (bs : ByteArray) : String :=
  let zeros := (bs.toList.takeWhile (fun b => b == 0)).length
  let n := bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0
  Id.run do
    let mut out := ""
    let mut v := n
    while v != 0 do
      out := String.singleton (digitOf alpha (v % radix)) ++ out
      v := v / radix
    String.ofList (List.replicate zeros (alpha.toList.getD 0 '0')) ++ out

/-- `Multibase.encode base data`: the prefixed text form of `data`. -/
def encode (base : Base) (data : ByteArray) : String :=
  String.singleton (prefixChar base) ++
    match base with
    | .identity => (String.fromUTF8? data).getD ""
    | .base2 => pow2Encode 1 "01" 0 data
    | .base8 => pow2Encode 3 "01234567" 0 data
    | .base10 => bigEncode 10 "0123456789" data
    | .base16 => Bytes.toHex data
    | .base16upper => (Bytes.toHex data).toUpper
    | .base32 => pow2Encode 5 alphabetB32 0 data
    | .base32upper => pow2Encode 5 alphabetB32.toUpper 0 data
    | .base32hex => pow2Encode 5 alphabetB32Hex 0 data
    | .base32hexupper => pow2Encode 5 alphabetB32Hex.toUpper 0 data
    | .base32pad => pow2Encode 5 alphabetB32 8 data
    | .base32padupper => pow2Encode 5 alphabetB32.toUpper 8 data
    | .base32hexpad => pow2Encode 5 alphabetB32Hex 8 data
    | .base32hexpadupper => pow2Encode 5 alphabetB32Hex.toUpper 8 data
    | .base32z => pow2Encode 5 alphabetB32Z 0 data
    | .base36 => bigEncode 36 alphabetB36 data
    | .base36upper => bigEncode 36 alphabetB36.toUpper data
    | .base58btc => bigEncode 58 LeanP2P.Base58.alphabet58 data
    | .base58flickr => bigEncode 58 alphabetB58Flickr data
    | .base64 => pow2Encode 6 alphabetB64 0 data
    | .base64pad => pow2Encode 6 alphabetB64 4 data
    | .base64url => pow2Encode 6 alphabetB64Url 0 data
    | .base64urlpad => pow2Encode 6 alphabetB64Url 4 data
    | .base256emoji =>
        String.ofList (data.toList.map (emojiOfByte ·.toNat))

/-! ## Decoding -/

private def digitVal? (alpha : String) (ci : Bool) (c : Char) : Option Nat :=
  match alpha.toList.findIdx? (· == c) with
  | some i => some i
  | none =>
      if ci then
        (if c.isUpper then alpha.toList.findIdx? (· == c.toLower)
         else alpha.toList.findIdx? (· == c.toUpper))
      else none

/-- Bit-slice decoder (inverse of `pow2Encode`). Lenient about leftover
group bits (Go's non-strict base32/base64, which the certhash vectors
need); padded forms are checked separately by `padOk`. -/
private def pow2Decode (bits : Nat) (alpha : String) (ci : Bool) (s : String) :
    Option ByteArray :=
  if s.any (· == '=') then none else
  Id.run do
    let mut out := ByteArray.empty
    let mut acc : Nat := 0
    let mut accBits := 0
    for c in s.toList do
      match digitVal? alpha ci c with
      | none => return none
      | some d =>
        acc := acc * (2 ^ bits) + d
        accBits := accBits + bits
        if accBits ≥ 8 then
          let shift := accBits - 8
          out := out.push (UInt8.ofNat ((acc / 2 ^ shift) % 256))
          acc := acc % (2 ^ shift)
          accBits := shift
    if accBits > 7 ∨ acc % (2 ^ accBits) != 0 then
      return none
    return out

/-- Padded multibase forms are canonical: the body must contain no `=`,
and the total length (body + `=`) must fill whole groups with exactly the
required padding (`grp` = 8 for base32, 4 for base64). -/
private def padOk (s : String) (grp : Nat) : Option String :=
  let cs := s.toList
  let body := cs.takeWhile (fun c => c != '=')
  let pad := cs.drop body.length
  let need := (grp - body.length % grp) % grp
  if pad.length = need ∧ pad.all (fun c => c == '=') then
    if body.any (fun c => c == '=') then none else some (String.ofList body)
  else none

private def natToBE : Nat → List Nat
  | 0 => []
  | n + 1 => natToBE ((n + 1) / 256) ++ [(n + 1) % 256]
termination_by n => n
decreasing_by omega

/-- Big-integer decoder (inverse of `bigEncode`): leading zero digits become
zero bytes. -/
private def bigDecode (radix : Nat) (alpha : String) (ci : Bool) (s : String) :
    Option ByteArray :=
  let zeros := (s.toList.takeWhile (· == alpha.toList.getD 0 '0')).length
  let body := s.toList.drop zeros
  match body.foldlM (fun n c => (· + n * radix) <$> digitVal? alpha ci c) 0 with
  | none => none
  | some n =>
      some (Bytes.ofNatList (List.replicate zeros 0 ++ natToBE n))

private def hexNibble? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def hexDecode (s : String) : Option ByteArray :=
  let cs := s.toList
  if cs.length % 2 != 0 then none
  else
    let rec go (acc : ByteArray) : List Char -> Option ByteArray
      | [] => some acc
      | a :: b :: rest => do
          let hi <- hexNibble? a
          let lo <- hexNibble? b
          go (acc.push (UInt8.ofNat (hi * 16 + lo))) rest
      | [_] => none
    go ByteArray.empty cs

/-- All bases, for prefix lookup. -/
def allBases : List Base :=
  [.identity, .base2, .base8, .base10, .base16, .base16upper,
   .base32, .base32upper, .base32hex, .base32hexupper,
   .base32pad, .base32padupper, .base32hexpad, .base32hexpadupper,
   .base32z, .base36, .base36upper, .base58btc, .base58flickr,
   .base64, .base64pad, .base64url, .base64urlpad, .base256emoji]

private def baseOfPrefix (c : Char) : Option Base :=
  allBases.find? (fun b => prefixChar b == c)

/-- `Multibase.decode? s`: the base and the decoded bytes, or `none`. -/
def decode? (s : String) : Option (Base × ByteArray) := do
  match s.toList with
  | [] => none
  | p :: body =>
    let base ← baseOfPrefix p
    let rest := String.ofList body
    let bytes ←
      match base with
      | .identity => some rest.toUTF8
      | .base2 => pow2Decode 1 "01" false rest
      | .base8 => pow2Decode 3 "01234567" false rest
      | .base10 => bigDecode 10 "0123456789" false rest
      | .base16 => hexDecode rest
      | .base16upper => hexDecode rest
      | .base32 => pow2Decode 5 alphabetB32 true rest
      | .base32upper => pow2Decode 5 alphabetB32 true rest
      | .base32hex => pow2Decode 5 alphabetB32Hex true rest
      | .base32hexupper => pow2Decode 5 alphabetB32Hex true rest
      | .base32pad => (padOk rest 8).bind (pow2Decode 5 alphabetB32 true)
      | .base32padupper => (padOk rest 8).bind (pow2Decode 5 alphabetB32 true)
      | .base32hexpad => (padOk rest 8).bind (pow2Decode 5 alphabetB32Hex true)
      | .base32hexpadupper => (padOk rest 8).bind (pow2Decode 5 alphabetB32Hex true)
      | .base32z => pow2Decode 5 alphabetB32Z false rest
      | .base36 => bigDecode 36 alphabetB36 true rest
      | .base36upper => bigDecode 36 alphabetB36 true rest
      | .base58btc => bigDecode 58 LeanP2P.Base58.alphabet58 false rest
      | .base58flickr => bigDecode 58 alphabetB58Flickr false rest
      | .base64 => pow2Decode 6 alphabetB64 false rest
      | .base64pad => (padOk rest 4).bind (pow2Decode 6 alphabetB64 false)
      | .base64url => pow2Decode 6 alphabetB64Url false rest
      | .base64urlpad => (padOk rest 4).bind (pow2Decode 6 alphabetB64Url false)
      | .base256emoji =>
          (rest.toList.mapM (fun c => emojiToByte? c)).map
            (fun l => Bytes.ofNatList l)
    return (base, bytes)

end LeanP2P.Multibase
