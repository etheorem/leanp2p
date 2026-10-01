/-!
# Byte helpers (IO boundary)

The verified protocol cores (multiaddr, framing) work over `List Nat` byte
models so arithmetic proofs stay in `omega` territory. This module converts
between that model and `ByteArray` / `String`, and holds the toy crypto
primitives used at the IO edge.
-/
namespace LeanP2P

/-- Build a `ByteArray` from the `List Nat` byte model. Values are taken mod 256. -/
def Bytes.ofNatList (l : List Nat) : ByteArray :=
  (l.map (fun n => UInt8.ofNat (n % 256))).toByteArray

/-- Convert a `ByteArray` back to the `List Nat` byte model. -/
def Bytes.toNatList (b : ByteArray) : List Nat :=
  b.toList.map (·.toNat)

def Bytes.ofString (s : String) : ByteArray := s.toUTF8

def Bytes.toString? (b : ByteArray) : Option String := String.fromUTF8? b

private def digitHex (n : Nat) : String :=
  if n < 10 then toString (Char.ofNat ('0'.toNat + n)) else toString (Char.ofNat ('a'.toNat + n - 10))

def Bytes.toHex (b : ByteArray) : String :=
  b.toList.foldl (fun acc x =>
    acc ++ digitHex (x.toNat / 16) ++ digitHex (x.toNat % 16)) ""

private def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def Bytes.ofHex? (s : String) : Option ByteArray :=
  if s.length % 2 != 0 then none
  else
    let rec go (acc : ByteArray) : List Char → Option ByteArray
      | [] => some acc
      | [_] => none
      | a :: b :: rest => do
          let hi ← hexVal a
          let lo ← hexVal b
          go (acc.push (UInt8.ofNat (hi * 16 + lo))) rest
    go ByteArray.empty s.toList

/-- XOR each byte with a repeating key. Placeholder for real cipher constructions. -/
def Bytes.xorWith (key : ByteArray) (data : ByteArray) : ByteArray :=
  let ks := key.size
  if ks = 0 then data
  else
    Id.run do
      let mut out := ByteArray.empty
      for i in [0:data.size] do
        out := out.push (data.get! i ^^^ key.get! (i % ks))
      out

/-- FNV-1a 32-bit over bytes. PLACEHOLDER for blake2b/sha256 in the real stack. -/
def Bytes.fnv1a (b : ByteArray) : UInt32 :=
  b.toList.foldl (fun acc x => (acc ^^^ x.toUInt32) * 16777619) 2166136261

end LeanP2P
