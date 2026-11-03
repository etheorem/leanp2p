import Std

/-!
# The byte model

The `List Nat` byte model and its conversions to `ByteArray`
(ARCHITECTURE §4.2). One model value is one byte, taken mod 256 on the
way out.

The model exists for the proofs. The verified codec cores state their
round-trip and inverse theorems over `List Nat`, where `omega` closes
the arithmetic (ARCHITECTURE §4.2, §6). The production path runs on
`ByteArray`; `Bytes.Harness` pins it to the model.

## Why the read goes through `ByteArray.data`

`ByteArray.toList` runs a loop, and `List.toByteArray` runs another
loop. The two loops are not definitionally inverse. `ByteArray.toList` unfolds
once to `ByteArray.toList.loop b 0 []`, and that loop carries
`@[irreducible]`, so `unfold` stalls. Lean still generates the equation lemma
`ByteArray.toList.loop.eq_1`, and `toListLoopSpec` inducts on it, which yields
the bridge theorem `toNatListEqToListMap`. This module builds its
`ByteArray` values through `ByteArray.mk` and reads them through
`data.toList`, where `List.toArray` is `fun xs => { toList := xs }` and
`Array.toList` is `fun self => self.1`. Both are `reducible`, so the
round trip closes on `Array.toList_inj` without any loop induction.
The externally visible behavior is the same byte sequence.
-/

set_option autoImplicit false

namespace Bytes

/-- Build a `ByteArray` from the `List Nat` byte model. Each model
value becomes one byte, taken mod 256. -/
def ofNatList (l : List Nat) : ByteArray :=
  ⟨(l.map (fun n => UInt8.ofNat (n % 256))).toArray⟩

/-- The array constructor emits the same bytes as the reference list builder. -/
theorem ofNatListEqToByteArray (l : List Nat) :
    ofNatList l = (l.map (fun n => UInt8.ofNat (n % 256))).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [ofNatList]

/-- Read a `ByteArray` back as the `List Nat` byte model: one `Nat`
per byte, each below 256, in order. The read goes through
`ByteArray.data.toList` for the reason in the module docstring. -/
def toNatList (b : ByteArray) : List Nat :=
  b.data.toList.map (fun x => x.toNat)

/-- The bytes of `ofNatList l`, read back. Holds by definition, and it
is the bridge the round-trip theorems rewrite with. -/
theorem ofNatListData (l : List Nat) :
    (ofNatList l).data.toList = l.map (fun n => UInt8.ofNat (n % 256)) := rfl

/-- The specification of the loop that `ByteArray.toList` runs: at index `i`,
the loop has emitted `acc` in reverse, before the remaining bytes.

`ByteArray.toList.loop` carries `@[irreducible]`, so `unfold` cannot enter it.
Lean still generates the equation lemma `ByteArray.toList.loop.eq_1`, and that
lemma carries this induction. -/
private theorem toListLoopSpec (b : ByteArray) (i : Nat) (acc : List UInt8) :
    ByteArray.toList.loop b i acc = acc.reverse ++ b.data.toList.drop i := by
  rw [ByteArray.toList.loop.eq_1]
  split
  · next h =>
    have hlt : i < b.data.toList.length := h
    rw [toListLoopSpec b (i + 1) (b.get! i :: acc)]
    have hget : b.get! i = b.data.toList[i] := by
      simp [ByteArray.get!, getElem!_pos b.data i h]
    rw [hget, List.reverse_cons, List.append_assoc, List.singleton_append,
      ← List.drop_eq_getElem_cons hlt]
  · next h =>
    have hge : b.data.toList.length ≤ i := Nat.le_of_not_lt h
    rw [List.drop_of_length_le hge, List.append_nil]
  termination_by b.size - i
  decreasing_by omega

/-- The public accessor returns the same bytes as `data.toList`. -/
theorem toListEqDataToList (b : ByteArray) : b.toList = b.data.toList := by
  unfold ByteArray.toList
  rw [toListLoopSpec, List.reverse_nil, List.nil_append, List.drop_zero]

/-- The documented reading of a `ByteArray`, through the public accessor. -/
theorem toNatListEqToListMap (b : ByteArray) :
    toNatList b = b.toList.map (fun x => x.toNat) := by
  unfold toNatList
  rw [toListEqDataToList]

/-- A byte read from the model value that produced it. -/
theorem toNatOfNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp

/-- A byte survives the model round trip. -/
theorem ofNatToNatMod (x : UInt8) : UInt8.ofNat (x.toNat % 256) = x := by
  have hlt : x.toNat < 256 := by
    have h := UInt8.toNat_lt x
    omega
  rw [Nat.mod_eq_of_lt hlt, UInt8.ofNat_toNat]

/-- Raising a list of bytes into the model and lowering it again returns
the list unchanged. -/
theorem mapOfNatToNat (xs : List UInt8) :
    (xs.map (fun x => x.toNat)).map (fun n => UInt8.ofNat (n % 256)) = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.map_cons] at ih ⊢
      rw [ih, ofNatToNatMod x]

/-- The model round trip, byte sequence first: every `ByteArray` comes
back unchanged. -/
theorem ofNatListToNatList (b : ByteArray) : ofNatList (toNatList b) = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  show (ofNatList (toNatList b)).data.toList = b.data.toList
  rw [ofNatListData]
  exact mapOfNatToNat b.data.toList

/-- The model round trip without the bound: values come back reduced mod
256. -/
theorem toNatListOfNatList (l : List Nat) :
    toNatList (ofNatList l) = l.map (fun n => n % 256) := by
  unfold toNatList
  rw [ofNatListData, List.map_map]
  apply List.map_congr_left
  intro n _
  simp only [Function.comp_apply]
  rw [toNatOfNat (n % 256), Nat.mod_mod]

/-- The model round trip, model first: values below 256 come back
unchanged. -/
theorem toNatListOfNatListOfLt (l : List Nat) (h : ∀ n ∈ l, n < 256) :
    toNatList (ofNatList l) = l := by
  rw [toNatListOfNatList]
  calc l.map (fun n => n % 256) = l.map id := by
        apply List.map_congr_left
        intro n hn
        exact Nat.mod_eq_of_lt (h n hn)
    _ = l := List.map_id l

/-- XOR each byte of the data with a repeating key. An empty key returns
the data unchanged.

The byte at index `i` of the result is `data[i] ^^^ key[i % key.size]`.
The indexed map keeps each key position fixed across both applications. -/
def xorWith (key data : ByteArray) : ByteArray :=
  match key.data.toList with
  | [] => data
  | ks =>
      ⟨(data.data.toList.mapIdx
          (fun i x => x ^^^ ks.getD (i % ks.length) 0)).toArray⟩

/-- An empty key leaves the data alone. -/
theorem xorWithEmpty (data : ByteArray) : xorWith ByteArray.empty data = data := rfl

/-- Applying the same key twice restores every byte. -/
theorem xorWithInvolution (key data : ByteArray) :
    xorWith key (xorWith key data) = data := by
  cases h : key.data.toList with
  | nil => simp [xorWith, h]
  | cons k ks =>
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp only [xorWith, h, List.mapIdx_mapIdx, Function.comp_def,
      UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]
    exact List.ext_getElem (by simp) (by intros; simp)

end Bytes