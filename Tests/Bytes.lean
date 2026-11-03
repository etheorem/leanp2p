import Tests.Support
import Bytes

/-!
# Byte conversion suite

Package PLAN unit 1 supplies these milestones. Generated samples pin the
byte model and text boundaries. A tagged fixture exercises both errors
and the generic harness before the first protocol codec arrives.

The fixture carries a `UInt8` payload on purpose. A codec whose model
symbols are arbitrary `Nat` values cannot be pinned to a `ByteArray`
path, because the bytes cannot carry a value at or above 256.
-/

set_option autoImplicit false

namespace Bytes

/-- A fixture owns its codec instance, as ARCHITECTURE §3.2 requires. -/
structure TestValue where
  value : UInt8
  deriving Repr, DecidableEq

private def decodeTest : List Nat → Except DecodeError (TestValue × List Nat)
  | [] => .error .truncated
  | tag :: rest =>
    if tag = 42 then
      match rest with
      | [] => .error .truncated
      | n :: tail =>
        if n < 256 then .ok (⟨UInt8.ofNat n⟩, tail) else .error .malformed
    else .error .malformed

instance : Codec TestValue where
  encode a := [42, a.value.toNat]
  decode? := decodeTest

instance : LawfulCodec TestValue where
  decodeEncode a := by
    obtain ⟨v⟩ := a
    have hv : v.toNat < 256 := by
      have h := UInt8.toNat_lt v
      omega
    simp [Codec.decode?, Codec.encode, decodeTest, hv, UInt8.ofNat_toNat]
  encodeDecode bs a rest h := by
    cases bs with
    | nil => simp [Codec.decode?, decodeTest] at h
    | cons tag tail =>
      by_cases ht : tag = 42
      · subst ht
        cases tail with
        | nil => simp [Codec.decode?, decodeTest] at h
        | cons n tl =>
          by_cases hn : n < 256
          · simp [Codec.decode?, decodeTest, hn] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [Codec.encode, Nat.mod_eq_of_lt hn]
          · simp [Codec.decode?, decodeTest, hn] at h
      · simp [Codec.decode?, decodeTest, ht] at h

private def decodeTestBytes (b : ByteArray) : Except DecodeError (TestValue × List Nat) :=
  if b.size = 0 then .error .truncated
  else if b[0]! != 42 then .error .malformed
  else if b.size < 2 then .error .truncated
  else .ok (⟨b[1]!⟩, (b.data.toList.drop 2).map (·.toNat))

private def generated (seed : Nat) : List Nat :=
  (List.range (seed % 65)).map fun i => (seed * 73 + i * 19) % 256

/-- Run each milestone through the shared runner so a failure sets the exit code. -/
def runTests (r : Tests.Runner) : IO Unit := do
  r.section "bytes" "spike Crypto/Bytes.lean; base/bytes PLAN unit 1"
  for seed in List.range 256 do
    let l := generated seed
    let b := ofNatList l
    r.check s!"model list round-trip {seed}" (toNatList b == l)
    r.check s!"model byte round-trip {seed}" (ofNatList (toNatList b) == b)
    r.check s!"standard byte list bridge {seed}" (toNatList b == b.toList.map (·.toNat))
    r.check s!"hex round-trip {seed}" (ofHex? (toHex b) == some b)
    let s := String.ofList (l.map fun n => Char.ofNat (32 + n))
    r.check s!"string round-trip {seed}" (toString? (ofString s) == some s)
    let key := ofNatList (generated (seed + 1))
    r.check s!"xor involution {seed}" (xorWith key (xorWith key b) == b)
    r.check s!"xor empty key {seed}" (xorWith ByteArray.empty b == b)
  -- The bridge to ByteArray.toList is the theorem toNatListEqToListMap. These
  -- checks pin the runtime path over arrays that ofNatList did not build.
  let pushed := (List.range 17).foldl (fun acc i => acc.push (UInt8.ofNat (i * 13))) ByteArray.empty
  let built : List ByteArray :=
    [ ByteArray.empty
    , ByteArray.mk ((List.range 40).map (fun i => UInt8.ofNat (i * 5 + 3))).toArray
    , pushed
    , pushed.append (ofNatList [9, 8, 7])
    , (ofHex? "deadbeef").getD ByteArray.empty
    ]
  for b in built do
    r.check s!"bridge to ByteArray.toList, size {b.size}"
      (toNatList b == b.toList.map (fun x => x.toNat))
  r.check "model reduces modulo 256" (toNatList (ofNatList [256, 257, 511]) == [0, 1, 255])
  r.check "invalid UTF8 C3" (toString? (ofNatList [0xC3]) == none)
  for s in ["", "ASCII", "é", "中文", "🙂", "a\u0000b"] do
    r.check s!"UTF8 boundary {s}" (toString? (ofString s) == some s)
  -- Code points that need 1, 2, 3, and 4 UTF-8 bytes.
  for cp in [0x41, 0x7F, 0x80, 0xE9, 0x7FF, 0x800, 0x4E2D, 0xFFFF, 0x10000, 0x1F600, 0x10FFFF] do
    let s := String.ofList [Char.ofNat cp]
    r.check s!"UTF8 width {cp}" (toString? (ofString s) == some s)
  r.check "hex odd length" (ofHex? "abc" == none)
  r.check "hex invalid digit" (ofHex? "0g" == none)
  r.check "hex lowercase output" (toHex (ofNatList [0, 15, 16, 171, 255]) == "000f10abff")
  r.check "hex uppercase rejected like spike" (ofHex? "AF" == none)
  let key := ofNatList [17, 128, 255]
  let data := ofNatList [0, 1, 2, 3, 4, 5, 6]
  let out := xorWith key data
  r.check "xor length" (out.size == data.size)
  for i in List.range 7 do
    r.check s!"xor key index {i}" (out[i]! == (data[i]! ^^^ key[i % key.size]!))
  r.check "codec truncated" (match Codec.decode? (α := TestValue) [42] with | .error .truncated => true | _ => false)
  r.check "codec malformed" (match Codec.decode? (α := TestValue) [41, 0] with | .error .malformed => true | _ => false)
  r.check "codec malformed non-byte payload"
    (match Codec.decode? (α := TestValue) [42, 300] with | .error .malformed => true | _ => false)
  let values := (List.range 256).map (fun n => TestValue.mk (UInt8.ofNat n))
  r.check "generic round-trip harness" (checkRoundTrips values)
  let samples := [ByteArray.empty, ofNatList [42]] ++
    ((List.range 256).flatMap fun n =>
      [ofNatList [n, n, 9], ofNatList [42, n], ofNatList [42, n, 9]]) ++
    ((List.range 8).map fun seed => ofNatList (generated seed))
  r.check "generic model pin" (checkModelPins decodeTestBytes samples)
  r.check "model pin detects wrong production result"
    (!(checkModelPins (α := TestValue) (fun _ => .error .malformed) [ofNatList [42, 7]]))

end Bytes
