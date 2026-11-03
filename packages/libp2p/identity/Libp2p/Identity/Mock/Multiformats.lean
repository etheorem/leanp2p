import Bytes

/-!
# The mock of the W2.3 multiaddr and multibase surface

Unit W2.3 (`codec/multiformats`, etheorem/leanp2p#36) has not merged.
RULES.md, "Working ahead of the tree", tells a unit to build against a
mock of the frozen interface of a dependency that has not merged. The
multiformats ARCHITECTURE freezes these names, and the ENR modules use
them only:

* `Protocol`, the closed set of the protocol table, with `toCode`.
  The mapping needs `ip4` (4), `tcp` (6), `udp` (273), and `ip6` (41).
* `Multiaddr`, the validated component list, with `toByteArray` and
  `ofByteArray?` as the binary boundary (root ARCHITECTURE §7, row 5).
* `Multibase.Base`, the closed registry, with `encode : Base →
  ByteArray → String` and `decode? : String → Except Error (Base ×
  ByteArray)`. The text form of a record needs `base64url` (prefix
  `u`, RFC 4648 §5 with no padding).

The binary form is the multiaddr spec's: each component is the varint
code, then the value. The four protocols above have fixed sizes, so no
length prefix follows the code.

**Why the opaques have values.** The mapping test builds and reads
addresses, and the text test reads the EIP-778 text, so the mock
computes. `ofByteArray?` accepts the four protocols above only; the
real decoder takes the whole table. `Base` holds the one base the
module uses; the real registry holds all of `multibase.csv`. The
base64url decoder is canonical, as the W2.3 decoder is: an `=`, a
character outside the alphabet, a length of `4k + 1`, and non-zero
trailing bits each fail.

**Integration.** When W2.3 merges, the ENR modules import
`Multiformats` in place of this module and open `Multiformats` in
place of `Mock.Multiformats`. The names above are the frozen ones of
the multiformats ARCHITECTURE, and the integration deletes this
module.
-/

set_option autoImplicit false

namespace Libp2p.Identity.Mock.Multiformats

/-- The protocols the mapping uses. -/
inductive Protocol where
  | ip4
  | tcp
  | udp
  | ip6
  deriving DecidableEq, Repr

/-- The multicodec of a protocol. -/
def Protocol.toCode : Protocol → Nat
  | .ip4 => 4
  | .tcp => 6
  | .udp => 273
  | .ip6 => 41

/-- A multiaddr, held as its binary form. -/
structure Multiaddr where
  bytes : ByteArray

/-- Why a multiformats decode failed. -/
inductive Error where
  | malformed
  /-- The first character names no base of the registry. -/
  | unknownBase
  /-- The body is not a canonical encoding under its base. -/
  | badBaseValue
  deriving DecidableEq, Repr

/-- The multibase registry, cut to the base the ENR text form uses. -/
inductive Multibase.Base where
  | base64url
  deriving DecidableEq, Repr

namespace Impl

/-- The value size of a protocol code that the mock knows. -/
def size? : Nat → Option Nat
  | 4 => some 4
  | 6 => some 2
  | 273 => some 2
  | 41 => some 16
  | _ => none

/-- Walk the components: a one- or two-byte varint code, then the
fixed-size value. -/
def check (b : List Nat) (fuel : Nat) : Bool :=
  match fuel, b with
  | _, [] => true
  | 0, _ => false
  | f + 1, c :: rest =>
    let (code, rest) :=
      if c < 0x80 then (c, rest)
      else match rest with
        | c2 :: rest' => (c - 0x80 + 128 * c2, rest')
        | [] => (0, [])
    match size? code with
    | some k => rest.length ≥ k && check (rest.drop k) f
    | none => false

def ofByteArray? (b : ByteArray) : Except Error Multiaddr :=
  if b.size > 0 && check (Bytes.toNatList b) b.size then .ok ⟨b⟩ else .error .malformed

/-- The RFC 4648 §5 alphabet. -/
def b64url : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toList

/-- `u`, then the 6-bit groups of the bytes, most significant first,
with the last group zero-filled on the right and no padding. -/
def encode (_ : Multibase.Base) (b : ByteArray) : String :=
  let bits := b.size * 8
  let n := Bytes.toNatList b |>.foldl (fun acc x => acc * 256 + x) 0
  let groups := (bits + 5) / 6
  let v := n * 2 ^ (groups * 6 - bits)
  String.ofList ('u' :: (List.range groups).reverse.map fun i => b64url.getD (v / 64 ^ i % 64) 'A')

/-- The bytes of a canonical base64url body, or `badBaseValue`. -/
def decodeBody (cs : List Char) : Except Error ByteArray := do
  let vals ← cs.mapM fun c =>
    match b64url.idxOf? c with
    | some i => .ok i
    | none => .error .badBaseValue
  let bits := vals.length * 6
  let bytes := bits / 8
  let extra := bits - bytes * 8
  -- A body of `4k + 1` characters leaves a lone group of 6 bits, which
  -- spells no byte.
  if extra ≥ 6 then throw .badBaseValue
  let v := vals.foldl (fun acc x => acc * 64 + x) 0
  if v % 2 ^ extra != 0 then throw .badBaseValue
  let w := v / 2 ^ extra
  .ok (Bytes.ofNatList ((List.range bytes).reverse.map fun i => w / 256 ^ i % 256))

def decode? (s : String) : Except Error (Multibase.Base × ByteArray) :=
  match s.toList with
  | 'u' :: cs => (decodeBody cs).map fun b => (.base64url, b)
  | _ => .error .unknownBase

end Impl

/-- The multibase text of the bytes under `base`. -/
opaque Multibase.encode : Multibase.Base → ByteArray → String := Impl.encode

/-- The base and the bytes of a multibase text. -/
opaque Multibase.decode? : String → Except Error (Multibase.Base × ByteArray) := Impl.decode?

/-- Decode a binary multiaddr. -/
opaque Multiaddr.ofByteArray? : ByteArray → Except Error Multiaddr := Impl.ofByteArray?

/-- The binary form of a multiaddr. -/
opaque Multiaddr.toByteArray : Multiaddr → ByteArray := Multiaddr.bytes

end Libp2p.Identity.Mock.Multiformats
