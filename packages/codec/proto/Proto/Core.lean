import Proto.Wire

/-!
# The protobuf wire core

Lengths and tags go through the bounded varint dependency. Fixed-width
values use little-endian digits. The field decoder consumes a complete
message, preserving its ordered entries and unknown fields.
-/

set_option autoImplicit false

namespace Pb

open Mock

/-- Internal total conversion; valid callers satisfy the bound before encoding. -/
def boundedVarint (n : Nat) : Varint.UVarint :=
  ⟨n % Varint.limit, Nat.mod_lt _ (by decide)⟩

/-- Wrapping an already bounded value does not change it. -/
theorem boundedVarintValue (v : Varint.UVarint) : boundedVarint v.val = v := by
  cases v with
  | mk n h => simp only [boundedVarint, Nat.mod_eq_of_lt h]

/-- Numeric fields share the single varint encoder. -/
def encodeNat (n : Nat) : List Nat := Varint.encode (boundedVarint n)

/-- The low byte comes first. -/
def leBytes (n : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => n % 256 :: leBytes (n / 256) k

/-- Read a little-endian byte list as a natural number. -/
def leOf : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * leOf bs

/-- Fixed-width output always has its requested length. -/
@[simp] theorem leBytesLength (n k : Nat) : (leBytes n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

/-- Every emitted digit fits in one byte. -/
theorem leBytesValid (n k : Nat) : ∀ b ∈ leBytes n k, b < 256 := by
  induction k generalizing n with
  | zero => simp [leBytes]
  | succ k ih =>
      simp only [leBytes, List.mem_cons]
      intro b hb
      rcases hb with rfl | hb
      · exact Nat.mod_lt _ (by decide)
      · exact ih _ _ hb

/-- A bounded number is recovered from its fixed-width digits. -/
theorem leOfLeBytes (n k : Nat) (h : n < 256 ^ k) : leOf (leBytes n k) = n := by
  induction k generalizing n with
  | zero => simp only [Nat.pow_zero] at h; simp [leBytes, leOf, show n = 0 by omega]
  | succ k ih =>
      rw [Nat.pow_succ] at h
      simp only [leBytes, leOf]
      rw [ih (n / 256) (by omega)]
      omega

/-- Valid byte lists are recovered from the number they represent. -/
theorem leBytesLeOf (bs : List Nat) (k : Nat) (hlen : bs.length = k)
    (hbytes : ∀ b ∈ bs, b < 256) : leBytes (leOf bs) k = bs := by
  induction bs generalizing k with
  | nil =>
      have hk : k = 0 := hlen.symm
      subst k
      rfl
  | cons b bs ih =>
      cases k with
      | zero => simp at hlen
      | succ k =>
          have hb := hbytes b (by simp)
          have ht : ∀ x ∈ bs, x < 256 := fun x hx => hbytes x (by simp [hx])
          have hl : bs.length = k := by simpa using hlen
          have hm : (b + 256 * leOf bs) % 256 = b := by omega
          have hd : (b + 256 * leOf bs) / 256 = leOf bs := by omega
          simp only [leOf, leBytes, hm, hd, ih k hl ht]

/-- The wire-type constructor determines the payload format. -/
def encodeValue : Value → List Nat
  | .varint n => encodeNat n
  | .fixed64 n => leBytes n 8
  | .bytes bs => encodeNat bs.length ++ bs
  | .fixed32 n => leBytes n 4

/-- Field tags keep the low three bits for the wire type. -/
def keyOf (e : Entry) : Nat := e.1 * 8 + e.2.wireType

/-- A single entry keeps its tag adjacent to its payload. -/
def encodeEntry (e : Entry) : List Nat := encodeNat (keyOf e) ++ encodeValue e.2

/-- Concatenation preserves the caller's field order. -/
def encodeEntries : List Entry → List Nat
  | [] => []
  | e :: es => encodeEntry e ++ encodeEntries es

/-- Validity facts are carried in Fields, not requested again at this entry point. -/
def encodeFields (fs : Fields) : List Nat := encodeEntries fs.entries

/-- A fixed payload must be complete and contain only model bytes. -/
def takeBytes (n : Nat) (bs : List Nat) : Except Error (List Nat × List Nat) :=
  if ∀ b ∈ bs.take n, b < 256 then
    if bs.length < n then .error (.framing .truncated)
    else .ok (bs.take n, bs.drop n)
  else .error (.framing .malformed)

/-- Fixed-width fields share the length and byte checks. -/
def readFixed (n : Nat) (bs : List Nat) : Except Error (Nat × List Nat) := do
  let (payload, rest) ← takeBytes n bs
  .ok (leOf payload, rest)

/-- Unsupported wire types have one explicit error, including groups. -/
def decodeValue? (wire : Nat) (bs : List Nat) : Except Error (Value × List Nat) := do
  match wire with
  | 0 =>
      let (v, rest) ← (Varint.decode? bs).mapError Error.framing
      .ok (.varint v.val, rest)
  | 1 =>
      let (n, rest) ← readFixed 8 bs
      .ok (.fixed64 n, rest)
  | 2 =>
      let (len, rest) ← (Varint.decode? bs).mapError Error.framing
      let (payload, tail) ← takeBytes len.val rest
      .ok (.bytes payload, tail)
  | 5 =>
      let (n, rest) ← readFixed 4 bs
      .ok (.fixed32 n, rest)
  | _ => .error .badWireType

/-- The decoder constructs the same proof field that table authors supply. -/
def decodeEntry? (bs : List Nat) : Except Error ({e : Entry // e.Valid} × List Nat) := do
  let (tag, rest) ← (Varint.decode? bs).mapError Error.framing
  let num := tag.val / 8
  if 0 < num ∧ num < fieldNumberLimit then
    let (v, tail) ← decodeValue? (tag.val % 8) rest
    if h : Entry.Valid (num, v) then .ok (⟨(num, v), h⟩, tail)
    else .error .badField
  else .error .badField

/-- One fuel step consumes at least a tag byte. Fuel is the input length. -/
def decodeEntries : Nat → List Nat → Except Error Fields
  | fuel, bs => if bs = [] then .ok Fields.empty else match fuel with
    | 0 => .error (.framing .malformed)
    | fuel + 1 => do
      let (entry, rest) ← decodeEntry? bs
      let fs ← decodeEntries fuel rest
      .ok ⟨entry.val :: fs.entries, by
        intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact entry.property
        · exact fs.valid e he⟩

/-- A protobuf message uses its complete externally framed buffer. -/
def decodeFields? (bs : List Nat) : Except Error (Fields × List Nat) := do
  let fs ← decodeEntries bs.length bs
  .ok (fs, [])

/-- An encoded length extracts exactly the payload that follows it. -/
theorem takeBytesAppend (bs rest : List Nat) (h : ∀ b ∈ bs, b < 256) :
    takeBytes bs.length (bs ++ rest) = .ok (bs, rest) := by
  unfold takeBytes
  simp only [List.take_left, List.drop_left]
  split
  · split
    · rename_i hs
      simp only [List.length_append] at hs
      omega
    · rfl
  · rename_i hn
    exact (hn h).elim


/-- Fixed-width output passes the boundary checks and recovers its value. -/
theorem readFixedEncode (n k : Nat) (h : n < 256 ^ k) (rest : List Nat) :
    readFixed k (leBytes n k ++ rest) = .ok (n, rest) := by
  have ht := takeBytesAppend (leBytes n k) rest (leBytesValid n k)
  rw [leBytesLength] at ht
  simp [readFixed, Bind.bind, Except.bind, ht, leOfLeBytes n k h]

/-- Payloads compose with arbitrary suffixes; the message layer chooses its boundary. -/
theorem decodeValueEncode (v : Value) (h : v.Valid) (rest : List Nat) :
    decodeValue? v.wireType (encodeValue v ++ rest) = .ok (v, rest) := by
  cases v with
  | varint n =>
      simp only [Value.Valid] at h
      simp [Bind.bind, Except.bind, Except.mapError, decodeValue?, Value.wireType, encodeValue, encodeNat,
        Varint.decodeEncodeSuffix, boundedVarint, Nat.mod_eq_of_lt h]
  | fixed64 n =>
      simp [Bind.bind, Except.bind, decodeValue?, Value.wireType, encodeValue,
        readFixedEncode n 8 h rest]
  | fixed32 n =>
      simp [Bind.bind, Except.bind, decodeValue?, Value.wireType, encodeValue,
        readFixedEncode n 4 h rest]
  | bytes bs =>
      rcases h with ⟨hlen, hbytes⟩
      simp [Bind.bind, Except.bind, Except.mapError, decodeValue?, Value.wireType, encodeValue, encodeNat, List.append_assoc,
        Varint.decodeEncodeSuffix, boundedVarint, Nat.mod_eq_of_lt hlen,
        takeBytesAppend bs rest hbytes]

/-- A valid tag fits inside the shared varint range. -/
theorem keyBound (e : Entry) (h : e.Valid) : keyOf e < Varint.limit := by
  obtain ⟨n, v⟩ := e
  have hn := h.2.1
  change n < 2 ^ 29 at hn
  cases v <;> simp only [keyOf, Value.wireType, Varint.limit] <;> omega

/-- Taking the tag's high bits recovers the field number. -/
theorem keyNumber (e : Entry) : keyOf e / 8 = e.1 := by
  obtain ⟨n, v⟩ := e
  cases v <;> simp only [keyOf, Value.wireType] <;> omega

/-- The low bits retain the constructor's wire type. -/
theorem keyWire (e : Entry) : keyOf e % 8 = e.2.wireType := by
  obtain ⟨n, v⟩ := e
  cases v <;> simp only [keyOf, Value.wireType] <;> omega

/-- A complete field round-trips without consuming the next field. -/
theorem decodeEntryEncode (e : Entry) (h : e.Valid) (rest : List Nat) :
    decodeEntry? (encodeEntry e ++ rest) = .ok (⟨e, h⟩, rest) := by
  have hb := keyBound e h
  have hn : 0 < e.1 ∧ e.1 < fieldNumberLimit := ⟨h.1, h.2.1⟩
  simp [Bind.bind, Except.bind, Except.mapError, decodeEntry?, encodeEntry, encodeNat, List.append_assoc,
    Varint.decodeEncodeSuffix, boundedVarint, Nat.mod_eq_of_lt hb,
    keyNumber, keyWire, hn, decodeValueEncode e.2 h.2.2 rest, h]

/-- Every encoded entry consumes at least its tag byte. -/
theorem encodeEntryNonempty (e : Entry) : encodeEntry e ≠ [] := by
  intro h
  have hn := Varint.encodeNonempty (boundedVarint (keyOf e))
  have hl := congrArg List.length h
  have hp : 0 < (Varint.encode (boundedVarint (keyOf e))).length :=
    List.length_pos_iff.mpr hn
  simp only [encodeEntry, encodeNat, List.length_append, List.length_nil] at hl
  omega

/-- Each recursive field consumes fuel; the input length supplies enough. -/
theorem decodeEntriesEncode (es : List Entry) (hv : ∀ e ∈ es, e.Valid)
    (fuel : Nat) (hf : (encodeEntries es).length ≤ fuel) :
    decodeEntries fuel (encodeEntries es) = .ok ⟨es, hv⟩ := by
  induction es generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons e es ih =>
      have he : e.Valid := hv e (by simp)
      have ht : ∀ x ∈ es, x.Valid := fun x hx => hv x (by simp [hx])
      have hp : 0 < (encodeEntry e).length := List.length_pos_iff.mpr (encodeEntryNonempty e)
      have hn : encodeEntry e ++ encodeEntries es ≠ [] := by
        intro hz
        have hl := congrArg List.length hz
        simp only [List.length_append, List.length_nil] at hl
        omega
      simp only [encodeEntries, List.length_append] at hf
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hr : (encodeEntries es).length ≤ fuel := by omega
          rw [encodeEntries, decodeEntries]
          simp only [hn, ite_false, decodeEntryEncode e he (encodeEntries es),
            Bind.bind, Except.bind, ih ht fuel hr]

/-- The public roundtrip is unconditional because Fields owns the bounds. -/
theorem decodeEncode (fs : Fields) : decodeFields? (encodeFields fs) = .ok (fs, []) := by
  have h := decodeEntriesEncode fs.entries fs.valid (encodeFields fs).length (Nat.le_refl _)
  change decodeEntries (encodeFields fs).length (encodeFields fs) = .ok fs at h
  simp only [decodeFields?, h, Bind.bind, Except.bind]


/-- A successful fixed-length read accounts for every consumed byte. -/
theorem takeBytesOk (n : Nat) (bs payload rest : List Nat)
    (h : takeBytes n bs = .ok (payload, rest)) :
    payload.length = n ∧ (∀ b ∈ payload, b < 256) ∧ bs = payload ++ rest := by
  unfold takeBytes at h
  split at h
  · rename_i hbytes
    split at h
    · cases h
    · rename_i hlen
      have hp := Prod.mk.inj (Except.ok.inj h)
      rcases hp with ⟨rfl, rfl⟩
      refine ⟨?_, hbytes, ?_⟩
      · simp only [List.length_take]
        omega
      · exact (List.take_append_drop n bs).symm
  · cases h

/-- The fixed-width inverse uses byte validity, not arithmetic modulo a width. -/
theorem readFixedOk (n value : Nat) (bs rest : List Nat)
    (h : readFixed n bs = .ok (value, rest)) : bs = leBytes value n ++ rest := by
  cases ht : takeBytes n bs with
  | error err => simp [readFixed, ht, Bind.bind, Except.bind] at h
  | ok pair =>
      obtain ⟨payload, tail⟩ := pair
      simp only [readFixed, ht, Bind.bind, Except.bind] at h
      have hp := Prod.mk.inj (Except.ok.inj h)
      rcases hp with ⟨rfl, rfl⟩
      obtain ⟨hlen, hbytes, hsplit⟩ := takeBytesOk n bs payload tail ht
      rw [leBytesLeOf payload n hlen hbytes]
      exact hsplit

/-- Successful payload parsing reconstructs the exact consumed prefix. -/
theorem decodeValueOk (wire : Nat) (bs : List Nat) (v : Value) (rest : List Nat)
    (h : decodeValue? wire bs = .ok (v, rest)) :
    bs = encodeValue v ++ rest ∧ v.wireType = wire := by
  unfold decodeValue? at h
  split at h
  · cases hd : Varint.decode? bs with
    | error err => simp [hd, Except.mapError, Bind.bind, Except.bind] at h
    | ok pair =>
        obtain ⟨n, tail⟩ := pair
        simp only [hd, Except.mapError, Bind.bind, Except.bind] at h
        have hp := Prod.mk.inj (Except.ok.inj h)
        rcases hp with ⟨rfl, rfl⟩
        refine ⟨?_, by simp_all [Value.wireType]⟩
        simpa only [encodeValue, encodeNat, boundedVarintValue] using
          Varint.encodeDecode bs n tail hd
  · cases hd : readFixed 8 bs with
    | error err => simp [hd, Bind.bind, Except.bind] at h
    | ok pair =>
        obtain ⟨n, tail⟩ := pair
        simp only [hd, Bind.bind, Except.bind] at h
        have hp := Prod.mk.inj (Except.ok.inj h)
        rcases hp with ⟨rfl, rfl⟩
        exact ⟨readFixedOk 8 n bs tail hd, by simp_all [Value.wireType]⟩
  · cases hd : Varint.decode? bs with
    | error err => simp [hd, Except.mapError, Bind.bind, Except.bind] at h
    | ok pair =>
        obtain ⟨n, tail⟩ := pair
        simp only [hd, Except.mapError, Bind.bind, Except.bind] at h
        cases ht : takeBytes n.val tail with
        | error err => simp [ht] at h
        | ok pair =>
            obtain ⟨payload, after⟩ := pair
            simp only [ht] at h
            have hp := Prod.mk.inj (Except.ok.inj h)
            rcases hp with ⟨rfl, rfl⟩
            obtain ⟨hlen, _, hsplit⟩ := takeBytesOk n.val tail payload after ht
            have hi := Varint.encodeDecode bs n tail hd
            refine ⟨?_, by simp_all [Value.wireType]⟩
            simpa only [encodeValue, hlen, encodeNat, boundedVarintValue,
              List.append_assoc] using hi.trans (congrArg (Varint.encode n ++ ·) hsplit)
  · cases hd : readFixed 4 bs with
    | error err => simp [hd, Bind.bind, Except.bind] at h
    | ok pair =>
        obtain ⟨n, tail⟩ := pair
        simp only [hd, Bind.bind, Except.bind] at h
        have hp := Prod.mk.inj (Except.ok.inj h)
        rcases hp with ⟨rfl, rfl⟩
        exact ⟨readFixedOk 4 n bs tail hd, by simp_all [Value.wireType]⟩
  · cases h

/-- A successful field parse preserves the tag and every payload byte. -/
theorem decodeEntryOk (bs : List Nat) (entry : {e : Entry // e.Valid}) (rest : List Nat)
    (h : decodeEntry? bs = .ok (entry, rest)) : bs = encodeEntry entry.val ++ rest := by
  cases hd : Varint.decode? bs with
  | error err => simp [decodeEntry?, hd, Except.mapError, Bind.bind, Except.bind] at h
  | ok pair =>
      obtain ⟨tag, tail⟩ := pair
      simp only [decodeEntry?, hd, Except.mapError, Bind.bind, Except.bind] at h
      split at h
      · cases hv : decodeValue? (tag.val % 8) tail with
        | error err => simp [hv] at h
        | ok pair =>
            obtain ⟨v, after⟩ := pair
            simp only [hv] at h
            split at h
            · have hp := Prod.mk.inj (Except.ok.inj h)
              rcases hp with ⟨rfl, rfl⟩
              obtain ⟨hvalue, hwire⟩ := decodeValueOk (tag.val % 8) tail v after hv
              have hkey : keyOf (tag.val / 8, v) = tag.val := by
                simp only [keyOf, hwire]
                omega
              have hin := Varint.encodeDecode bs tag tail hd
              simpa only [encodeEntry, hkey, encodeNat, boundedVarintValue,
                List.append_assoc] using
                hin.trans (congrArg (Varint.encode tag ++ ·) hvalue)
            · cases h
      · cases h

/-- Every successful message parse re-encodes to the complete input. -/
theorem decodeEntriesOk (fuel : Nat) (bs : List Nat) (fs : Fields)
    (h : decodeEntries fuel bs = .ok fs) : bs = encodeFields fs := by
  induction fuel generalizing bs fs with
  | zero =>
      simp only [decodeEntries] at h
      split at h
      · rename_i hz
        subst bs
        cases h
        rfl
      · cases h
  | succ fuel ih =>
      rw [decodeEntries] at h
      split at h
      · rename_i hz
        subst bs
        cases h
        rfl
      · cases he : decodeEntry? bs with
        | error err => simp [he, Bind.bind, Except.bind] at h
        | ok pair =>
            obtain ⟨entry, rest⟩ := pair
            simp only [he, Bind.bind, Except.bind] at h
            cases ht : decodeEntries fuel rest with
            | error err => simp [ht] at h
            | ok tail =>
                simp only [ht] at h
                cases h
                have hr := ih rest tail ht
                have hp := decodeEntryOk bs entry rest he
                simpa only [encodeFields, encodeEntries] using
                  hp.trans (congrArg (encodeEntry entry.val ++ ·) hr)

/-- Accepted input has exactly the encoding returned by the decoder. -/
theorem encodeDecode (bs : List Nat) (fs : Fields) (rest : List Nat)
    (h : decodeFields? bs = .ok (fs, rest)) : bs = encodeFields fs ++ rest := by
  cases hd : decodeEntries bs.length bs with
  | error err => simp [decodeFields?, hd, Bind.bind, Except.bind] at h
  | ok value =>
      simp only [decodeFields?, hd, Bind.bind, Except.bind] at h
      have hp := Prod.mk.inj (Except.ok.inj h)
      rcases hp with ⟨rfl, rfl⟩
      simpa only [List.append_nil] using decodeEntriesOk bs.length bs value hd

/-- The generic codec boundary maps the detailed wire error once. -/
instance : Mock.Bytes.Codec Fields where
  encode := encodeFields
  decode? bs := (decodeFields? bs).mapError Error.toDecodeError

/-- Both codec laws follow from the protobuf proofs, not extra mock axioms. -/
instance : Mock.Bytes.LawfulCodec Fields where
  decodeEncode fs := by
    change (decodeFields? (encodeFields fs)).mapError Error.toDecodeError = _
    rw [decodeEncode]
    rfl
  encodeDecode bs fs rest h := by
    change (decodeFields? bs).mapError Error.toDecodeError = .ok (fs, rest) at h
    cases hd : decodeFields? bs with
    | error err => simp [hd, Except.mapError] at h
    | ok pair =>
        simp only [hd, Except.mapError, Except.ok.injEq] at h
        cases h
        exact encodeDecode bs fs rest hd

/-- Equal encodings imply equal ordered Fields values. -/
theorem encodeInjective {a b : Fields} (h : encodeFields a = encodeFields b) : a = b := by
  have ha := decodeEncode a
  rw [h, decodeEncode b] at ha
  exact (Prod.mk.inj (Except.ok.inj ha)).1.symm

/-- Every valid payload produces byte-valued model entries. -/
theorem encodeValueBytes (v : Value) (h : v.Valid) :
    ∀ b ∈ encodeValue v, b < 256 := by
  cases v with
  | varint n => exact Varint.encodeBytes (boundedVarint n)
  | fixed64 n => exact leBytesValid n 8
  | fixed32 n => exact leBytesValid n 4
  | bytes bs =>
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact Varint.encodeBytes (boundedVarint bs.length) b hb
      · exact h.2 b hb

/-- Tags and payloads both preserve the byte invariant. -/
theorem encodeEntryBytes (e : Entry) (h : e.Valid) :
    ∀ b ∈ encodeEntry e, b < 256 := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact Varint.encodeBytes (boundedVarint (keyOf e)) b hb
  · exact encodeValueBytes e.2 h.2.2 b hb

/-- A valid Fields encoding is lossless at the model-to-ByteArray boundary. -/
theorem encodeFieldsBytes (fs : Fields) : ∀ b ∈ encodeFields fs, b < 256 := by
  obtain ⟨entries, valid⟩ := fs
  change ∀ b ∈ encodeEntries entries, b < 256
  induction entries with
  | nil => simp [encodeEntries]
  | cons e entries ih =>
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact encodeEntryBytes e (valid e (by simp)) b hb
      · exact ih (fun x hx => valid x (by simp [hx])) b hb

end Pb
