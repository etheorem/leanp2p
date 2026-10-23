import LeanP2P.Crypto.Bytes
import LeanP2P.Net.Varint
/-!
# Protobuf wire codec (VECTOR_TEST_PLAN.md, phase 2 step 12)

Pure encoder/decoder for the proto wire format over the `List Nat` byte
model, following the same pattern as `Net/Varint`: a verified core with a
round-trip theorem (`decode_encode`), plus `ByteArray` entry points for the
IO edge.

Supported wire types: 0 (varint), 1 (fixed64 LE), 2 (length-delimited:
bytes / strings / embedded messages), 5 (fixed32 LE). Deprecated groups
(3/4) are rejected. Decoding keeps unknown fields in the field list (so
they round-trip); the message-structure helpers simply look up the fields
they know, which is proto2/proto3 unknown-field tolerance.

libp2p requirement (peer-ids spec): encoders must be deterministic - minimal
varints, fields in tag order. Both hold by construction (`Varint.encode` is
minimal, `encodeFields` concatenates in list order).

The 9-byte varint cap of `Net/Varint` applies (values < 2^63), which covers
every libp2p use: field numbers, uint64 scalars, byte-string lengths, enums.
-/

namespace LeanP2P.Pb

/-! ## Little-endian byte helpers -/

/-- `k` little-endian bytes of `n` (low byte first). -/
def leBytes (n : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => n % 256 :: leBytes (n / 256) k

/-- Value of little-endian bytes (inverse of `leBytes`). -/
def leOf : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * leOf bs

theorem leBytes_length (v : Nat) : ∀ k, (leBytes v k).length = k
  | 0 => rfl
  | k + 1 => by
      show (v % 256 :: leBytes (v / 256) k).length = _
      rw [List.length_cons, leBytes_length]

theorem leOf_leBytes (v : Nat) : ∀ k, v < 256 ^ k → leOf (leBytes v k) = v
  | 0, h => by
      rw [Nat.pow_zero] at h
      simp only [leBytes, leOf]
      omega
  | k + 1, h => by
      rw [Nat.pow_succ] at h
      show v % 256 + 256 * leOf (leBytes (v / 256) k) = v
      rw [leOf_leBytes (v / 256) k (by omega)]
      omega

/-! ## Values and encoding -/

/-- A protobuf field value; the constructor fixes its wire type. -/
inductive Value where
  /-- wire type 0 -/
  | varint (v : Nat)
  /-- wire type 1: 8 bytes little-endian -/
  | fixed64 (v : Nat)
  /-- wire type 2: length-delimited (bytes, strings, embedded messages) -/
  | bytes (bs : List Nat)
  /-- wire type 5: 4 bytes little-endian -/
  | fixed32 (v : Nat)
  deriving Repr, BEq

def Value.wireType : Value → Nat
  | .varint _ => 0
  | .fixed64 _ => 1
  | .bytes _ => 2
  | .fixed32 _ => 5

/-- Well-formed value: encodable under the 9-byte varint / fixed-width
discipline. -/
def Value.wf : Value → Prop
  | .varint v => v < 2 ^ 63
  | .fixed64 v => v < 2 ^ 64
  | .bytes bs => bs.length < 2 ^ 63
  | .fixed32 v => v < 2 ^ 32

/-- A message is an ordered list of `(field number, value)` pairs. -/
abbrev Fields := List (Nat × Value)

def Fields.wf (fs : Fields) : Prop :=
  ∀ m ∈ fs, m.1 < 2 ^ 59 ∧ m.2.wf

def encodeValue : Value → List Nat
  | .varint v => Varint.encode v
  | .fixed64 v => leBytes v 8
  | .bytes bs => Varint.encode bs.length ++ bs
  | .fixed32 v => leBytes v 4

/-- Tag key: field number shifted left 3, low 3 bits the wire type. -/
def keyOf (num : Nat) (v : Value) : Nat := num * 8 + v.wireType

def encodeFields : Fields → List Nat
  | [] => []
  | (num, v) :: fs =>
      Varint.encode (keyOf num v) ++ encodeValue v ++ encodeFields fs

theorem encode_key_nonempty (num : Nat) (v : Value) : Varint.encode (keyOf num v) ≠ [] := by
  by_cases h : keyOf num v < 128
  · rw [Varint.encode_small h]; exact List.cons_ne_nil _ _
  · rw [Varint.encode_big (by omega)]; exact List.cons_ne_nil _ _

theorem encode_ne_nil (n : Nat) : Varint.encode n ≠ [] := by
  by_cases h : n < 128
  · rw [Varint.encode_small h]; exact List.cons_ne_nil _ _
  · rw [Varint.encode_big (by omega)]; exact List.cons_ne_nil _ _

theorem encodeValue_nonempty (v : Value) : encodeValue v ≠ [] := by
  cases v with
  | varint v => exact encode_ne_nil v
  | fixed64 v =>
      intro h
      simp only [encodeValue] at h
      have hl := leBytes_length v 8
      rw [h] at hl
      simp at hl
  | bytes bs =>
      intro h
      simp only [encodeValue] at h
      cases hb : bs with
      | nil => rw [hb] at h; simp [Varint.encode] at h
      | cons x tl => rw [hb] at h; simp at h
  | fixed32 v =>
      intro h
      simp only [encodeValue] at h
      have hl := leBytes_length v 4
      rw [h] at hl
      simp at hl

/-! ## Decoding -/

private def takeN (n : Nat) (bs : List Nat) : Option (List Nat × List Nat) :=
  if bs.length < n then none else some (bs.take n, bs.drop n)

theorem takeN_app {n : Nat} {bs rest : List Nat} (h : bs.length = n) :
    takeN n (bs ++ rest) = some (bs, rest) := by
  show (if (bs ++ rest).length < n then none
        else some ((bs ++ rest).take n, (bs ++ rest).drop n)) = _
  rw [if_neg (by rw [List.length_append, h]; omega),
      show (bs ++ rest).take n = bs from by rw [← h]; simp,
      show (bs ++ rest).drop n = rest from by rw [← h]; simp]

/-- Decode with fuel; each field consumes at least two bytes (tag key +
nonempty payload), so fuel bounds the field count. -/
def decodeFieldsF : Nat → List Nat → Option (Fields × List Nat)
  | 0, _ => none
  | f + 1, bs =>
      if bs = [] then some ([], [])
      else
        match Varint.decodeF 9 bs with
        | none => none
        | some (key, rest) =>
            let num := key / 8
            match key % 8 with
            | 0 => match Varint.decodeF 9 rest with
                   | none => none
                   | some (v, rest') =>
                       (match decodeFieldsF f rest' with
                        | none => none
                        | some (fs, rem) => some ((num, .varint v) :: fs, rem))
            | 1 => match takeN 8 rest with
                   | none => none
                   | some (payload, rest') =>
                       (match decodeFieldsF f rest' with
                        | none => none
                        | some (fs, rem) =>
                            some ((num, .fixed64 (leOf payload)) :: fs, rem))
            | 2 => match Varint.decodeF 9 rest with
                   | none => none
                   | some (len, rest') =>
                       if rest'.length < len then none
                       else
                         (match decodeFieldsF f (rest'.drop len) with
                          | none => none
                          | some (fs, rem) =>
                              some ((num, .bytes (rest'.take len)) :: fs, rem))
            | 5 => match takeN 4 rest with
                   | none => none
                   | some (payload, rest') =>
                       (match decodeFieldsF f rest' with
                        | none => none
                        | some (fs, rem) =>
                            some ((num, .fixed32 (leOf payload)) :: fs, rem))
            | _ => none  -- wire types 3/4 (deprecated groups) and 6/7

/-- Standalone decode: consumes the whole buffer. -/
def decodeFields (bs : List Nat) : Option Fields := do
  let (fs, rest) ← decodeFieldsF (bs.length + 1) bs
  if rest = [] then some fs else none

/-- ByteArray entry point. -/
def decodeFieldsB? (b : ByteArray) : Option Fields :=
  decodeFields (Bytes.toNatList b)

/-- ByteArray entry point. -/
def encodeFieldsB (fs : Fields) : ByteArray :=
  Bytes.ofNatList (encodeFields fs)

/-! ## Round-trip theorem -/

/-- Decoding an encoding yields exactly the fields and consumes everything.
Fuel-generalized so the induction goes through; `decodeFields` instantiates
it at `length + 1`. -/
theorem decode_encode : ∀ fs : Fields, Fields.wf fs → ∀ f : Nat,
    (encodeFields fs).length < f →
    decodeFieldsF f (encodeFields fs) = some (fs, []) := by
  intro fs
  induction fs with
  | nil => intro _ f hf; cases f with
    | zero => exact absurd hf (by omega)
    | succ f => simp [encodeFields, decodeFieldsF]
  | cons hd fs ih =>
    intro hall
    obtain ⟨num, v⟩ := hd
    obtain ⟨hnum, hval⟩ := hall (num, v) (List.mem_cons.2 (Or.inl rfl))
    have hnum' : num < 2 ^ 59 := hnum
    have hallfs : Fields.wf fs := fun m hm => hall m (List.mem_cons.2 (Or.inr hm))
    intro f hf
    -- fuel bookkeeping: key and payload are each at least one byte
    have hkeylen1 : 1 ≤ (Varint.encode (keyOf num v)).length := by
      have hne := encode_key_nonempty num v
      cases h3 : Varint.encode (keyOf num v) with
      | nil => rw [h3] at hne; exact absurd hne (by simp)
      | cons a t => simp
    have hvallen : 1 ≤ (encodeValue v).length := by
      have hne := encodeValue_nonempty v
      cases h3 : encodeValue v with
      | nil => rw [h3] at hne; exact absurd hne (by simp)
      | cons a t => simp
    cases f with
    | zero => exact absurd hf (by omega)
    | succ f =>
      have hsplit : (Varint.encode (keyOf num v)).length + (encodeValue v).length
          + (encodeFields fs).length ≤ f := by
        have := hf
        rw [encodeFields] at this
        simp only [List.length_append] at this
        omega
      have hfuels : (encodeFields fs).length < f := by omega
      -- the encoded buffer is nonempty, so the empty guard does not fire
      -- (right-nested on purpose: append_assoc rewrites the goal to this form)
      have hne : ¬ (Varint.encode (keyOf num v) ++
          (encodeValue v ++ encodeFields fs)) = [] := by
        intro hc
        have hl := congrArg List.length hc
        rw [List.length_append, List.length_append] at hl
        have h0 : ([] : List Nat).length = 0 := rfl
        rw [h0] at hl
        omega
      -- the tag key stays below the 2^63 varint budget
      have hkey63 : keyOf num v < 2 ^ 63 := by
        unfold keyOf
        have h1 : num * 8 ≤ (2 ^ 59 - 1) * 8 := by omega
        have h2 : (2 ^ 59 - 1) * 8 + 7 = 2 ^ 62 - 1 := by decide
        have h3 : 2 ^ 62 - 1 < 2 ^ 63 := by decide
        cases v <;> simp only [Value.wireType] <;> omega
      have hfuelkey9 : (Varint.encode (keyOf num v)).length ≤ 9 :=
        Varint.encode_length_le _ hkey63
      -- unfold, decode the tag key, dispatch on the wire type
      rw [encodeFields]
      simp only [List.append_assoc, decodeFieldsF]
      split
      · rename_i h; exact absurd h hne
      · simp only [Varint.decodeF_encode_app _ _ hkey63 _ hfuelkey9,
          show keyOf num v / 8 = num from by unfold keyOf; cases v <;>
            simp only [Value.wireType] <;> omega,
          show keyOf num v % 8 = v.wireType from by unfold keyOf; cases v <;>
            simp only [Value.wireType] <;> omega]
        cases v with
        | varint v =>
            have hv : v < 2 ^ 63 := by unfold Value.wf at hval; exact hval
            simp only [encodeValue, List.cons_append, Value.wireType,
              Varint.decodeF_encode_app v _ hv 9 (Varint.encode_length_le v hv),
              ih hallfs f hfuels]
        | fixed64 v =>
            have hv : v < 2 ^ 64 := by unfold Value.wf at hval; exact hval
            have hpow : (256 : Nat) ^ 8 = 2 ^ 64 := by rfl
            simp only [encodeValue, List.cons_append, Value.wireType,
              takeN_app (leBytes_length v 8),
              leOf_leBytes v 8 (by rw [hpow]; exact hv),
              ih hallfs f hfuels]
        | bytes bs =>
            have hv : bs.length < 2 ^ 63 := by unfold Value.wf at hval; exact hval
            have hnoflow : ¬ ((bs ++ encodeFields fs).length < bs.length) := by
              rw [List.length_append]
              omega
            simp only [List.append_assoc, encodeValue, List.cons_append,
              Value.wireType,
              Varint.decodeF_encode_app bs.length _ hv 9
                (Varint.encode_length_le _ hv),
              if_neg hnoflow,
              show (bs ++ encodeFields fs).drop bs.length = encodeFields fs
                from by simp,
              show (bs ++ encodeFields fs).take bs.length = bs from by simp,
              ih hallfs f hfuels]
        | fixed32 v =>
            have hv : v < 2 ^ 32 := by unfold Value.wf at hval; exact hval
            have hpow : (256 : Nat) ^ 4 = 2 ^ 32 := by rfl
            simp only [encodeValue, List.cons_append, Value.wireType,
              takeN_app (leBytes_length v 4),
              leOf_leBytes v 4 (by rw [hpow]; exact hv),
              ih hallfs f hfuels]

/-- Corollary through the standalone entry point. -/
theorem decode_encode_fields (fs : Fields) (h : Fields.wf fs) :
    decodeFields (encodeFields fs) = some fs := by
  simp only [decodeFields]
  rw [decode_encode fs h ((encodeFields fs).length + 1) (by omega)]
  simp

/-! ## Message-structure helpers ("derive-style" API)

Look up known fields, skipping everything else - this is the tolerance
libp2p needs when peer messages evolve (proto2 optional fields, proto3
implicit-presence fields arriving out of order or carrying unknown tags). -/

/-- All length-delimited values of a repeated field, in wire order. -/
def getAllBytes (num : Nat) (fs : Fields) : List (List Nat) :=
  fs.filterMap (fun (n, v) => if n = num then
    match v with | .bytes bs => some bs | _ => none else none)

/-- All varint values of a repeated field, in wire order. -/
def getAllVarints (num : Nat) (fs : Fields) : List Nat :=
  fs.filterMap (fun (n, v) => if n = num then
    match v with | .varint v => some v | _ => none else none)

/-- Last varint field with this number. Singular (proto2 optional /
proto3 implicit-presence) fields follow last-value-wins semantics per the
protobuf spec: a repeated occurrence of a singular field overwrites the
previous value, so the last one on the wire is the message's value. -/
def getVarint? (num : Nat) (fs : Fields) : Option Nat :=
  (fs.reverse.lookup num).bind (fun
    | .varint v => some v
    | _ => none)

/-- Last bytes/string/submessage field with this number, as raw payload
(singular-field semantics, see `getVarint?`). -/
def getBytes? (num : Nat) (fs : Fields) : Option (List Nat) :=
  (fs.reverse.lookup num).bind (fun
    | .bytes bs => some bs
    | _ => none)

/-- First embedded submessage with this number. -/
def getSub? (num : Nat) (fs : Fields) : Option Fields :=
  getBytes? num fs |>.bind decodeFields

/-- Is the field present (proto2 `optional`/`required` semantics)? -/
def hasField (num : Nat) (fs : Fields) : Bool := fs.any (fun (n, _) => n = num)

/-- Length-delimited field as UTF-8 string. -/
def getStr? (num : Nat) (fs : Fields) : Option String :=
  getBytes? num fs |>.bind (fun bs => Bytes.toString? (Bytes.ofNatList bs))

/-- All string values of a repeated field. -/
def getAllStrs (num : Nat) (fs : Fields) : List String :=
  getAllBytes num fs |>.map (fun bs => Bytes.toString? (Bytes.ofNatList bs))
    |>.filterMap id

end LeanP2P.Pb
