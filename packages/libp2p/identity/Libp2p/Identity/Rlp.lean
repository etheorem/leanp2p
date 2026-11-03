import Bytes

/-!
# RLP, the package's own small codec

Recursive Length Prefix, the serialization that EIP-778 records use
(`vendor/eips/EIPS/eip-778.md`, "RLP Encoding"). An RLP item is a byte
string or a list of items. The first byte of an encoding names the
kind and the length of the payload:

| first byte | meaning |
|---|---|
| `0x00`–`0x7f` | the byte itself, a one-byte string |
| `0x80`–`0xb7` | a string of `b - 0x80` bytes, 0 to 55 |
| `0xb8`–`0xbf` | a string whose length takes the next `b - 0xb7` bytes, big-endian |
| `0xc0`–`0xf7` | a list whose payload is `b - 0xc0` bytes, 0 to 55 |
| `0xf8`–`0xff` | a list whose payload length takes the next `b - 0xf7` bytes |

The decoder is strict, as the canonical form demands. It rejects a
one-byte string below `0x80` in a `0x81` header, a long length with a
leading zero, and a long length below 56. The ethereum/tests
`invalidRLPTest.json` cases pin each rule.

This module is the recorded fallback of the package ARCHITECTURE: the
etheorem `LeanRlp` package has its item codec on `main`, and its
vector runner and round-trip theorems have not landed. The module holds
the item tree, the model codec over `List Nat`, the proof of the
`LawfulCodec` law, and the `ByteArray` decoder that the harness pins to
the model.

**Why a fuel argument.** The decoder of a list payload decodes an item,
then the rest of the payload. Each step consumes bytes, but Lean cannot
see that inside one mutual definition. A fuel argument makes both
functions structural on a `Nat`. Two units of fuel per input byte are
enough, and `decodeItemEncode` proves it.
-/

set_option autoImplicit false

namespace Libp2p.Identity.Rlp

open Bytes

/-! ## Big-endian scalars

RLP writes lengths and integers as big-endian bytes with no leading
zero. Zero is the empty byte string. The proofs run on the
little-endian list, where the recursion peels the low byte first. -/

/-- The little-endian bytes of `n`, with no high zero byte. -/
def leBytes (n : Nat) : List Nat :=
  if n = 0 then [] else n % 256 :: leBytes (n / 256)
termination_by n
decreasing_by omega

/-- The value of little-endian bytes. -/
def leNat : List Nat → Nat
  | [] => 0
  | b :: t => b + 256 * leNat t

/-- The minimal big-endian bytes of `n`: empty for zero. -/
def beBytes (n : Nat) : List Nat := (leBytes n).reverse

/-- The value of big-endian bytes. -/
def beNat (l : List Nat) : Nat := leNat l.reverse

theorem leNatLeBytes (n : Nat) : leNat (leBytes n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [leBytes]
    split
    · simp [leNat]; omega
    · simp only [leNat]
      rw [ih (n / 256) (by omega)]
      omega

theorem beNatBeBytes (n : Nat) : beNat (beBytes n) = n := by
  simp [beNat, beBytes, leNatLeBytes]

theorem ltOfMemLeBytes {n x : Nat} (h : x ∈ leBytes n) : x < 256 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [leBytes] at h
    split at h
    · simp at h
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · omega
      · exact ih (n / 256) (by omega) h

theorem ltOfMemBeBytes {n x : Nat} (h : x ∈ beBytes n) : x < 256 :=
  ltOfMemLeBytes (List.mem_reverse.mp h)

theorem lengthLeBytesLe {n : Nat} (k : Nat) (h : n < 256 ^ k) : (leBytes n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simp at h; omega
    subst this
    simp [leBytes]
  | succ k ih =>
    rw [leBytes]
    split
    · simp
    · have hdiv : n / 256 < 256 ^ k := by
        rw [Nat.pow_succ] at h
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
      simp only [List.length_cons]
      have := ih hdiv
      omega

theorem leBytesNeNil {n : Nat} (h : n ≠ 0) : leBytes n ≠ [] := by
  rw [leBytes]; simp [h]

/-- The top byte of `leBytes n` is never zero. -/
theorem getLastLeBytesNe (n : Nat) : (leBytes n).getLast? ≠ some 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [leBytes]
    split
    · simp
    · next hn =>
      by_cases hq : n / 256 = 0
      · rw [hq, leBytes]
        simp only [↓reduceIte, List.getLast?_singleton, ne_eq, Option.some.injEq]
        omega
      · have hne := leBytesNeNil hq
        have hrec := ih (n / 256) (by omega)
        obtain ⟨y, hy⟩ := List.getLast?_isSome.mpr hne |> Option.isSome_iff_exists.mp
        rw [List.getLast?_cons, hy]
        rw [hy] at hrec
        simpa using hrec

/-- A nonempty little-endian list whose top byte is nonzero has a
nonzero value. -/
theorem leNatPos : ∀ (l : List Nat), l ≠ [] → l.getLast? ≠ some 0 → 0 < leNat l
  | [], h, _ => absurd rfl h
  | [b], _, hl => by simp [leNat] at hl ⊢; omega
  | b :: c :: t, _, hl => by
    have := leNatPos (c :: t) (by simp) (by simpa [List.getLast?_cons_cons] using hl)
    simp only [leNat] at this ⊢
    omega

/-- A canonical little-endian list comes back from its value. -/
theorem leBytesLeNat : ∀ (l : List Nat), (∀ b ∈ l, b < 256) → l.getLast? ≠ some 0 →
    leBytes (leNat l) = l
  | [], _, _ => by simp [leNat, leBytes]
  | [b], hb, hl => by
    have hb' : b < 256 := hb b (by simp)
    have h0 : b ≠ 0 := by simpa using hl
    simp only [leNat]
    rw [leBytes]
    simp only [Nat.mul_zero, Nat.add_zero, h0, ↓reduceIte, List.cons.injEq]
    refine ⟨Nat.mod_eq_of_lt hb', ?_⟩
    rw [Nat.div_eq_of_lt hb', leBytes]; simp
  | b :: c :: t, hb, hl => by
    have hb' : b < 256 := hb b (by simp)
    have hl' : (c :: t).getLast? ≠ some 0 := by simpa [List.getLast?_cons_cons] using hl
    have hpos := leNatPos (c :: t) (by simp) hl'
    have ih := leBytesLeNat (c :: t) (fun x hx => hb x (List.mem_cons_of_mem b hx)) hl'
    -- `leNat (c :: t)` stays folded: the recursive case only needs its
    -- value, positive, and the induction hypothesis on it.
    show leBytes (b + 256 * leNat (c :: t)) = b :: c :: t
    generalize hv : leNat (c :: t) = v at hpos ih
    rw [leBytes]
    simp only [show b + 256 * v ≠ 0 by omega, ↓reduceIte, List.cons.injEq]
    refine ⟨by omega, ?_⟩
    rw [show (b + 256 * v) / 256 = v by omega, ih]

/-- A canonical big-endian list comes back from its value. -/
theorem beBytesBeNat (l : List Nat) (hb : ∀ b ∈ l, b < 256) (hl : l.head? ≠ some 0) :
    beBytes (beNat l) = l := by
  unfold beBytes beNat
  rw [leBytesLeNat l.reverse (by simpa using hb) (by simpa [List.getLast?_reverse] using hl)]
  simp

theorem headBeBytesNe (n : Nat) : (beBytes n).head? ≠ some 0 := by
  simpa [beBytes, List.head?_reverse] using getLastLeBytesNe n

theorem lengthBeBytesLe {n : Nat} (k : Nat) (h : n < 256 ^ k) : (beBytes n).length ≤ k := by
  simpa [beBytes] using lengthLeBytesLe k h

theorem lengthBeBytesPos {n : Nat} (h : n ≠ 0) : 0 < (beBytes n).length := by
  have := leBytesNeNil h
  simp [beBytes]
  exact List.length_pos_iff.mpr this

/-! ## Items -/

/-- An RLP item: a byte string or a list of items. The byte model is
`List Nat`, so an item can hold a value that is not a byte; `valid`
rules that out. -/
inductive Item where
  /-- A byte string. -/
  | bytes (b : List Nat)
  /-- A list of items. -/
  | list (items : List Item)
  deriving Repr, Inhabited

mutual
/-- Equality of items. Lean does not derive `DecidableEq` for an
inductive that nests itself under `List`, so the two functions decide
it by structural recursion. -/
def Item.decEq : (a b : Item) → Decidable (a = b)
  | .bytes x, .bytes y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .list x, .list y =>
    match Item.decEqList x y with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .bytes _, .list _ => isFalse (by intro e; cases e)
  | .list _, .bytes _ => isFalse (by intro e; cases e)

/-- Equality of item lists, the second half of `Item.decEq`. -/
def Item.decEqList : (a b : List Item) → Decidable (a = b)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match Item.decEq x y, Item.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq Item := Item.decEq

/-! ## The encoder -/

/-- The header of a payload of `len` bytes. `offset` is `0x80` for a
string and `0xc0` for a list. A payload of 56 bytes or more takes the
long form: the count of length bytes, then the length. -/
def header (offset len : Nat) : List Nat :=
  if len < 56 then [offset + len]
  else (offset + 55 + (beBytes len).length) :: beBytes len

/-- `true` for a one-byte string below `0x80`, the one string that is
its own encoding. -/
def isSingleLow : List Nat → Bool
  | [b] => b < 0x80
  | _ => false

/-- The encoding of a byte string. -/
def encodeBytes (bs : List Nat) : List Nat :=
  if isSingleLow bs then bs else header 0x80 bs.length ++ bs

mutual
/-- The encoding of an item. -/
def encode : Item → List Nat
  | .bytes bs => encodeBytes bs
  | .list is => header 0xc0 (encodeList is).length ++ encodeList is

/-- The concatenated encodings of a list payload. -/
def encodeList : List Item → List Nat
  | [] => []
  | i :: is => encode i ++ encodeList is
end

/-! ## Validity

The long form spends at most 8 length bytes, so a payload holds fewer
than `256 ^ 8` bytes. An item is valid when every string value is a
byte and every payload fits that bound. Only a valid item encodes to
bytes that decode back to it. -/

/-- The first payload length that the long form cannot carry. -/
def maxPayload : Nat := 256 ^ 8

mutual
/-- The validity check of an item. -/
def Item.valid : Item → Bool
  | .bytes bs => bs.all (· < 256) && decide (bs.length < maxPayload)
  | .list is => Item.validList is && decide ((encodeList is).length < maxPayload)

/-- The validity check of every item in a list. -/
def Item.validList : List Item → Bool
  | [] => true
  | i :: is => i.valid && Item.validList is
end

/-- A valid item: the value type of the codec. The proof field is the
fact of ARCHITECTURE §3.7, and Lean erases it at run time. -/
structure Value where
  /-- The item. -/
  item : Item
  /-- The item fits the byte model and the length bound. -/
  isValid : item.valid = true
  deriving DecidableEq

/-! ## The decoder -/

/-- What a header says about the item that follows. -/
inductive Head where
  /-- A byte below `0x80`, its own one-byte string. -/
  | single (b : Nat)
  /-- A string of `len` bytes. -/
  | str (len : Nat)
  /-- A list with a payload of `len` bytes. -/
  | list (len : Nat)
  deriving Repr, DecidableEq

/-- The long-form length: `k` big-endian bytes at the front of `rest`.
The bytes must be canonical: no leading zero, and a value that the
short form cannot carry. -/
def longLength (k : Nat) (rest : List Nat) : Except DecodeError (Nat × List Nat) :=
  if rest.length < k then .error .truncated
  else
    let lb := rest.take k
    if lb.head? = some 0 then .error .malformed
    else if !(lb.all (· < 256)) then .error .malformed
    else if beNat lb < 56 then .error .malformed
    else .ok (beNat lb, rest.drop k)

/-- The header at the front of the input. -/
def decodeHead : List Nat → Except DecodeError (Head × List Nat)
  | [] => .error .truncated
  | b :: rest =>
    if 256 ≤ b then .error .malformed
    else if b < 0x80 then .ok (.single b, rest)
    else if b < 0xb8 then .ok (.str (b - 0x80), rest)
    else if b < 0xc0 then
      match longLength (b - 0xb7) rest with
      | .error e => .error e
      | .ok (n, r) => .ok (.str n, r)
    else if b < 0xf8 then .ok (.list (b - 0xc0), rest)
    else
      match longLength (b - 0xf7) rest with
      | .error e => .error e
      | .ok (n, r) => .ok (.list n, r)

/-- The `len` payload bytes at the front of `rest`. -/
def takePayload (len : Nat) (rest : List Nat) : Except DecodeError (List Nat × List Nat) :=
  if rest.length < len then .error .truncated else .ok (rest.take len, rest.drop len)

mutual
/-- One item at the front of the input, and the rest. An error inside
a list payload is `malformed`: the payload is complete, so no later
byte can finish an element that crosses its end. -/
def decodeItem : Nat → List Nat → Except DecodeError (Item × List Nat)
  | 0, _ => .error .malformed
  | n + 1, l =>
    match decodeHead l with
    | .error e => .error e
    | .ok (.single b, rest) => .ok (.bytes [b], rest)
    | .ok (.str len, rest) =>
      match takePayload len rest with
      | .error e => .error e
      | .ok (p, r) => if isSingleLow p then .error .malformed else .ok (.bytes p, r)
    | .ok (.list len, rest) =>
      match takePayload len rest with
      | .error e => .error e
      | .ok (p, r) =>
        match decodeSeq n p with
        | .error _ => .error .malformed
        | .ok is => .ok (.list is, r)

/-- Every item of a list payload, which must end exactly at the last
item. -/
def decodeSeq : Nat → List Nat → Except DecodeError (List Item)
  | _, [] => .ok []
  | 0, _ :: _ => .error .malformed
  | n + 1, l@(_ :: _) =>
    match decodeItem n l with
    | .error e => .error e
    | .ok (i, r) =>
      match decodeSeq n r with
      | .error e => .error e
      | .ok is => .ok (i :: is)
end

/-- The fuel for an input: two units per byte, and two more. -/
def fuel (l : List Nat) : Nat := 2 * l.length + 2

/-- One valid item at the front of the input, and the rest. -/
def decode? (l : List Nat) : Except DecodeError (Value × List Nat) :=
  match decodeItem (fuel l) l with
  | .error e => .error e
  | .ok (i, r) => if h : i.valid = true then .ok (⟨i, h⟩, r) else .error .malformed

/-! ## The lemmas behind the law -/

theorem lengthHeaderPos (offset len : Nat) : 0 < (header offset len).length := by
  unfold header; split <;> simp

theorem lengthEncodePos : ∀ (i : Item), 0 < (encode i).length
  | .bytes bs => by
    simp only [encode, encodeBytes]
    split
    · next h =>
      match bs, h with
      | [_], _ => simp
    · simp only [List.length_append]
      have := lengthHeaderPos 0x80 bs.length
      omega
  | .list is => by
    simp only [encode, List.length_append]
    have := lengthHeaderPos 0xc0 (encodeList is).length
    omega

/-- The long form of a length reads back. -/
theorem longLengthBeBytes {len : Nat} (h56 : 56 ≤ len) (t : List Nat) :
    longLength (beBytes len).length (beBytes len ++ t) = .ok (len, t) := by
  unfold longLength
  simp only [List.length_append, show ¬(beBytes len).length + t.length < (beBytes len).length
    by omega, ↓reduceIte, List.take_left', List.drop_left']
  have hz := headBeBytesNe len
  have hall : (beBytes len).all (· < 256) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro x hx; exact ltOfMemBeBytes hx
  simp only [hz, ↓reduceIte, hall, Bool.not_true, Bool.false_eq_true, beNatBeBytes,
    show ¬len < 56 by omega]

/-- A string header reads back. -/
theorem decodeHeadStr {len : Nat} (hlen : len < maxPayload) (t : List Nat) :
    decodeHead (header 0x80 len ++ t) = .ok (.str len, t) := by
  unfold header
  split
  · next h =>
    simp only [List.singleton_append, decodeHead]
    simp only [show ¬256 ≤ 0x80 + len by omega, show ¬0x80 + len < 0x80 by omega,
      show 0x80 + len < 0xb8 by omega, ↓reduceIte, show 0x80 + len - 0x80 = len by omega]
  · next h =>
    have hk := lengthBeBytesLe 8 (n := len) hlen
    have hk0 := lengthBeBytesPos (n := len) (by omega)
    simp only [List.cons_append, decodeHead]
    simp only [show ¬256 ≤ 0x80 + 55 + (beBytes len).length by omega,
      show ¬0x80 + 55 + (beBytes len).length < 0x80 by omega,
      show ¬0x80 + 55 + (beBytes len).length < 0xb8 by omega,
      show 0x80 + 55 + (beBytes len).length < 0xc0 by omega, ↓reduceIte]
    rw [show 0x80 + 55 + (beBytes len).length - 0xb7 = (beBytes len).length by omega,
      longLengthBeBytes (by omega)]

/-- A list header reads back. -/
theorem decodeHeadList {len : Nat} (hlen : len < maxPayload) (t : List Nat) :
    decodeHead (header 0xc0 len ++ t) = .ok (.list len, t) := by
  unfold header
  split
  · next h =>
    simp only [List.singleton_append, decodeHead]
    simp only [show ¬256 ≤ 0xc0 + len by omega, show ¬0xc0 + len < 0x80 by omega,
      show ¬0xc0 + len < 0xb8 by omega, show ¬0xc0 + len < 0xc0 by omega,
      show 0xc0 + len < 0xf8 by omega, ↓reduceIte, show 0xc0 + len - 0xc0 = len by omega]
  · next h =>
    have hk := lengthBeBytesLe 8 (n := len) hlen
    have hk0 := lengthBeBytesPos (n := len) (by omega)
    simp only [List.cons_append, decodeHead]
    simp only [show ¬256 ≤ 0xc0 + 55 + (beBytes len).length by omega,
      show ¬0xc0 + 55 + (beBytes len).length < 0x80 by omega,
      show ¬0xc0 + 55 + (beBytes len).length < 0xb8 by omega,
      show ¬0xc0 + 55 + (beBytes len).length < 0xc0 by omega,
      show ¬0xc0 + 55 + (beBytes len).length < 0xf8 by omega, ↓reduceIte]
    rw [show 0xc0 + 55 + (beBytes len).length - 0xf7 = (beBytes len).length by omega,
      longLengthBeBytes (by omega)]

theorem takePayloadAppend (p t : List Nat) : takePayload p.length (p ++ t) = .ok (p, t) := by
  simp [takePayload]

mutual
/-- A valid item decodes back from its encoding, with any rest after
it, when the fuel covers two units per encoded byte. -/
theorem decodeItemEncode : ∀ (i : Item), i.valid = true → ∀ (m : Nat) (rest : List Nat),
    2 * (encode i).length ≤ m → decodeItem m (encode i ++ rest) = .ok (i, rest)
  | .bytes bs, hv, m, rest, hm => by
    have hpos := lengthEncodePos (.bytes bs)
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Item.valid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hbyte, hlen⟩ := hv
    simp only [encode, encodeBytes] at hm ⊢
    split
    · next hs =>
      match bs, hs with
      | [b], hs =>
        simp only [isSingleLow, decide_eq_true_eq] at hs
        have hb : b < 256 := hbyte b (by simp)
        simp only [List.singleton_append, decodeItem, decodeHead,
          show ¬256 ≤ b by omega, hs, ↓reduceIte]
    · next hs =>
      rw [List.append_assoc]
      simp only [decodeItem, decodeHeadStr hlen, takePayloadAppend, hs, Bool.false_eq_true,
        ↓reduceIte]
  | .list is, hv, m, rest, hm => by
    have hpos := lengthEncodePos (.list is)
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Item.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hvl, hlen⟩ := hv
    have hh := lengthHeaderPos 0xc0 (encodeList is).length
    simp only [encode, List.length_append] at hm
    simp only [encode]
    rw [List.append_assoc]
    simp only [decodeItem, decodeHeadList hlen, takePayloadAppend]
    rw [decodeSeqEncode is hvl m (by omega)]

/-- A valid list payload decodes back to its items. -/
theorem decodeSeqEncode : ∀ (is : List Item), Item.validList is = true → ∀ (m : Nat),
    2 * (encodeList is).length + 1 ≤ m → decodeSeq m (encodeList is) = .ok is
  | [], _, m, _ => by
    cases m <;> simp [encodeList, decodeSeq]
  | i :: is, hv, m, hm => by
    simp only [Item.validList, Bool.and_eq_true] at hv
    obtain ⟨hvi, hvl⟩ := hv
    have hpos := lengthEncodePos i
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [encodeList, List.length_append] at hm
    obtain ⟨x, xs, hx⟩ : ∃ x xs, encode i ++ encodeList is = x :: xs := by
      cases h : encode i with
      | nil => simp [h] at hpos
      | cons x xs => exact ⟨x, xs ++ encodeList is, by simp⟩
    simp only [encodeList]
    rw [hx]
    simp only [decodeSeq]
    -- After the item rewrite, the outer `match` sits on an `.ok`, and
    -- `simp only` reduces it before the payload rewrite.
    rw [← hx, decodeItemEncode i hvi m (encodeList is) (by omega)]
    simp only [decodeSeqEncode is hvl m (by omega)]
end

/-- What a successful header read consumed. -/
theorem decodeHeadInv {l rest : List Nat} {h : Head} (hd : decodeHead l = .ok (h, rest)) :
    match h with
    | .single b => l = b :: rest ∧ b < 0x80
    | .str len => l = header 0x80 len ++ rest
    | .list len => l = header 0xc0 len ++ rest := by
  match l with
  | [] => simp [decodeHead] at hd
  | b :: t =>
    simp only [decodeHead] at hd
    -- The long form: the length bytes are canonical, so `beBytes`
    -- rebuilds them from their value.
    have hlong : ∀ (off k n r : Nat) (rr : List Nat), longLength k t = .ok (n, rr) →
        off + 55 + k = b → 0 < k → n = r → header off r ++ rr = b :: t := by
      intro off k n r rr hl hb _ hnr
      subst hnr
      unfold longLength at hl
      split at hl
      · cases hl
      · next hk =>
        simp only at hl
        split at hl
        · cases hl
        · next hz =>
          split at hl
          · cases hl
          · next hall =>
            split at hl
            · cases hl
            · next h56 =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hl
              obtain ⟨rfl, rfl⟩ := hl
              have hall' : ∀ x ∈ t.take k, x < 256 := by
                simpa using hall
              have hbe := beBytesBeNat (t.take k) hall' hz
              have hlenk : (t.take k).length = k := by simp; omega
              unfold header
              simp only [show ¬beNat (List.take k t) < 56 by omega, ↓reduceIte, hbe,
                List.cons_append, List.cons.injEq, hlenk, List.take_append_drop, and_true]
              omega
    split at hd
    · cases hd
    · split at hd
      · next h1 =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        exact ⟨rfl, h1⟩
      · split at hd
        · next h1 h2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hd
          obtain ⟨rfl, rfl⟩ := hd
          simp only [header, show b - 0x80 < 56 by omega, ↓reduceIte, List.singleton_append,
            List.cons.injEq, and_true]
          omega
        · split at hd
          · next h1 h2 h3 =>
            split at hd
            · cases hd
            · next n r hl =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hd
              obtain ⟨rfl, rfl⟩ := hd
              exact (hlong 0x80 (b - 0xb7) n n r hl (by omega) (by omega) rfl).symm
          · split at hd
            · next h1 h2 h3 h4 =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hd
              obtain ⟨rfl, rfl⟩ := hd
              simp only [header, show b - 0xc0 < 56 by omega, ↓reduceIte, List.singleton_append,
                List.cons.injEq, and_true]
              omega
            · next h1 h2 h3 h4 h5 =>
              split at hd
              · cases hd
              · next n r hl =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hd
                obtain ⟨rfl, rfl⟩ := hd
                exact (hlong 0xc0 (b - 0xf7) n n r hl (by omega) (by omega) rfl).symm

theorem takePayloadInv {len : Nat} {rest p r : List Nat}
    (h : takePayload len rest = .ok (p, r)) : rest = p ++ r ∧ p.length = len := by
  unfold takePayload at h
  split at h
  · cases h
  · next hl =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, by simp; omega⟩

/-- Every accepted input is an encoding: the decoder reads canonical
forms only. -/
theorem encodeDecodeAux : ∀ (n : Nat),
    (∀ (l : List Nat) (i : Item) (r : List Nat), decodeItem n l = .ok (i, r) →
      encode i ++ r = l) ∧
    (∀ (p : List Nat) (is : List Item), decodeSeq n p = .ok is → encodeList is = p) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun l i r h => by simp [decodeItem] at h, fun p is h => ?_⟩
    match p with
    | [] => simp only [decodeSeq, Except.ok.injEq] at h; subst h; rfl
    | _ :: _ => simp [decodeSeq] at h
  | succ n ih =>
    obtain ⟨ihItem, ihSeq⟩ := ih
    refine ⟨fun l i r h => ?_, fun p is h => ?_⟩
    · simp only [decodeItem] at h
      split at h
      · cases h
      · next b rest hd =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨rfl, hb⟩ := decodeHeadInv hd
        simp [encode, encodeBytes, isSingleLow, hb]
      · next len rest hd =>
        have hl := decodeHeadInv hd
        split at h
        · cases h
        · next p r' hp =>
          obtain ⟨rfl, hplen⟩ := takePayloadInv hp
          split at h
          · cases h
          · next hs =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only at hl
            simp [encode, encodeBytes, hs, hl, hplen]
      · next len rest hd =>
        have hl := decodeHeadInv hd
        split at h
        · cases h
        · next p r' hp =>
          obtain ⟨rfl, hplen⟩ := takePayloadInv hp
          split at h
          · cases h
          · next is hs =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have he := ihSeq p is hs
            simp only at hl
            simp [encode, he, hl, hplen]
    · match p with
      | [] => simp only [decodeSeq, Except.ok.injEq] at h; subst h; rfl
      | x :: xs =>
        simp only [decodeSeq] at h
        split at h
        · cases h
        · next i r hi =>
          split at h
          · cases h
          · next is' hs =>
            simp only [Except.ok.injEq] at h
            subst h
            simp only [encodeList]
            have he := ihItem (x :: xs) i r hi
            rw [ihSeq r is' hs, he]

/-! ## The instances -/

/-- The model codec of RLP values. -/
instance : Codec Value where
  encode v := encode v.item
  decode? := decode?

/-- A value decodes back from its encoding, and nothing is left. -/
theorem decodeEncodeValue (v : Value) : decode? (encode v.item) = .ok (v, []) := by
  unfold decode?
  have h := decodeItemEncode v.item v.isValid (fuel (encode v.item)) []
    (by simp only [fuel]; omega)
  simp only [List.append_nil] at h
  rw [h]
  simp only [v.isValid, ↓reduceDIte]

/-- Both laws hold with no hypothesis: the value type carries the
validity fact, and the decoder accepts canonical forms only. -/
instance : LawfulCodec Value where
  decodeEncode v := decodeEncodeValue v
  encodeDecode bs v rest h := by
    simp only [Codec.decode?, decode?] at h
    split at h
    · cases h
    · next i r hi =>
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact (encodeDecodeAux _).1 bs i r hi
      · cases h

/-! ## Scalars

RLP carries an integer as its minimal big-endian bytes: zero is the
empty string, and a leading zero byte is not canonical. EIP-778 uses
this form for `seq` and the ports. -/

/-- The integer a canonical scalar string carries, or `none` for a
leading zero or a value of more than `maxBytes` bytes. `none` has one
meaning: the bytes are not a canonical scalar of that width. -/
def scalar? (maxBytes : Nat) (bs : List Nat) : Option Nat :=
  if bs.head? = some 0 then none
  else if maxBytes < bs.length then none
  else if !(bs.all (· < 256)) then none
  else some (beNat bs)

/-- The scalar string of `n`. -/
def ofScalar (n : Nat) : List Nat := beBytes n

theorem scalarOfScalar {n k : Nat} (h : n < 256 ^ k) : scalar? k (ofScalar n) = some n := by
  have hz := headBeBytesNe n
  have hk := lengthBeBytesLe k h
  have hall : (beBytes n).all (· < 256) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro x hx; exact ltOfMemBeBytes hx
  simp [scalar?, ofScalar, hz, show ¬k < (beBytes n).length by omega, hall, beNatBeBytes]

/-! ## The `ByteArray` decoder

The production path walks the input by position, and `lim` marks the
end of the enclosing payload. It mirrors the model step for step, so
the errors agree as well as the values. `Tests/Rlp.lean` pins it to the
model with the harness of `base/bytes`. -/

namespace Wire

/-- The byte at `i`, as a model value. Callers check `i < lim ≤ size`. -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat

/-- The bytes `[i, j)` as the model list. -/
def slice (b : ByteArray) (i j : Nat) : List Nat := toNatList (b.extract i j)

end Wire

open Wire in
/-- The long-form length: `k` bytes at `pos`, before `lim`. -/
def longLengthB (b : ByteArray) (k pos lim : Nat) : Except DecodeError (Nat × Nat) :=
  if lim - pos < k then .error .truncated
  else
    let lb := slice b pos (pos + k)
    if lb.head? = some 0 then .error .malformed
    else if beNat lb < 56 then .error .malformed
    else .ok (beNat lb, pos + k)

open Wire in
/-- The header at `pos`, before `lim`, and the position after it. -/
def decodeHeadB (b : ByteArray) (pos lim : Nat) : Except DecodeError (Head × Nat) :=
  if lim ≤ pos then .error .truncated
  else
    let c := byteAt b pos
    if c < 0x80 then .ok (.single c, pos + 1)
    else if c < 0xb8 then .ok (.str (c - 0x80), pos + 1)
    else if c < 0xc0 then
      match longLengthB b (c - 0xb7) (pos + 1) lim with
      | .error e => .error e
      | .ok (n, q) => .ok (.str n, q)
    else if c < 0xf8 then .ok (.list (c - 0xc0), pos + 1)
    else
      match longLengthB b (c - 0xf7) (pos + 1) lim with
      | .error e => .error e
      | .ok (n, q) => .ok (.list n, q)

mutual
/-- One item at `pos`, before `lim`, and the position after it. -/
def decodeItemB (b : ByteArray) : Nat → Nat → Nat → Except DecodeError (Item × Nat)
  | 0, _, _ => .error .malformed
  | n + 1, pos, lim =>
    match decodeHeadB b pos lim with
    | .error e => .error e
    | .ok (.single c, q) => .ok (.bytes [c], q)
    | .ok (.str len, q) =>
      if lim - q < len then .error .truncated
      else
        let p := Wire.slice b q (q + len)
        if isSingleLow p then .error .malformed else .ok (.bytes p, q + len)
    | .ok (.list len, q) =>
      if lim - q < len then .error .truncated
      else
        match decodeSeqB b n q (q + len) with
        | .error _ => .error .malformed
        | .ok is => .ok (.list is, q + len)

/-- Every item from `pos` to exactly `lim`. -/
def decodeSeqB (b : ByteArray) : Nat → Nat → Nat → Except DecodeError (List Item)
  | n, pos, lim =>
    if lim ≤ pos then .ok []
    else match n with
      | 0 => .error .malformed
      | n + 1 =>
        match decodeItemB b n pos lim with
        | .error e => .error e
        | .ok (i, q) =>
          match decodeSeqB b n q lim with
          | .error e => .error e
          | .ok is => .ok (i :: is)
end

/-- One valid item at the front of `b`, and the number of bytes it
took. The fuel is the model's, `fuel (toNatList b)`. -/
def decodeB? (b : ByteArray) : Except DecodeError (Value × Nat) :=
  match decodeItemB b (2 * b.size + 2) 0 b.size with
  | .error e => .error e
  | .ok (i, q) => if h : i.valid = true then .ok (⟨i, h⟩, q) else .error .malformed

/-- The wire bytes of a value. -/
def encodeB (v : Value) : ByteArray := ofNatList (encode v.item)

/-! ## Item helpers -/

/-- The bytes of a string item; `none` for a list. -/
def Item.bytes? : Item → Option (List Nat)
  | .bytes b => some b
  | .list _ => none

/-- The items of a list item; `none` for a string. -/
def Item.list? : Item → Option (List Item)
  | .list is => some is
  | .bytes _ => none

end Libp2p.Identity.Rlp
