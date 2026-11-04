import Multiformats.Multihash
import Multiformats.Multibase

/-!
# Content identifiers

CIDv0 is exactly a sha2-256 multihash with a 32-byte digest. CIDv1
adds version one and a registered content-code value. The prefix parser
is composable, and the standalone parser rejects trailing bytes.
-/

set_option autoImplicit false

namespace Multiformats

/-- Each constructor carries the invariants needed for its own wire form. -/
inductive Cid where
  | v0 (hash : Multihash) (valid : hash.code = .«sha2-256» ∧ hash.digest.length = 32)
  | v1 (codec : ContentCodec) (hash : Multihash)
  deriving DecidableEq, Repr

namespace Cid


/-- CIDv0 cannot be constructed around another hash shape. -/
def v0? (hash : Multihash) : Except Error Cid :=
  if h : hash.code = .«sha2-256» ∧ hash.digest.length = 32 then .ok (.v0 hash h)
  else .error .badCid

/-- Version zero has no explicit version or content-code prefix. -/
def encode : Cid → List Nat
  | .v0 hash _ => Multihash.encode hash
  | .v1 codec hash => Wire.encodeNat 1 ++ Wire.encodeNat codec.toCode ++ Multihash.encode hash

/-- The first decoded integer distinguishes the two allowed forms. -/
def decodeAt? (input : List Nat) : Except Error (Cid × List Nat) := do
  let (version, tail) ← (Varint.decode? input).mapError Error.framing
  if version.val = 18 then
    let (hash, rest) ← Multihash.decodeAt? input
    if h : hash.code = .«sha2-256» ∧ hash.digest.length = 32 then .ok (.v0 hash h, rest)
    else .error .badCid
  else if version.val = 1 then
    let (rawCodec, tail) ← (Varint.decode? tail).mapError Error.framing
    let codec ← match ContentCodec.ofCode? rawCodec.val with
      | none => .error .badCid
      | some codec => .ok codec
    if codec.toCode = rawCodec.val then
      let (hash, rest) ← Multihash.decodeAt? tail
      .ok (.v1 codec hash, rest)
    else .error .badCid
  else .error .badCid

/-- Exactly one CID occupies a standalone buffer. -/
def decode? (input : List Nat) : Except Error (Cid × List Nat) := do
  let (value, rest) ← decodeAt? input
  if rest = [] then .ok (value, []) else .error .badCid

/-- Both versions compose with an arbitrary byte suffix. -/
theorem decodeAtEncode (value : Cid) (rest : List Nat) :
    decodeAt? (encode value ++ rest) = .ok (value, rest) := by
  cases value with
  | v0 hash valid =>
      have codeValue : hash.code.toCode = 18 := by rw [valid.1]; rfl
      have codeRead : (Wire.toVarint hash.code.toCode).val = 18 := by
        change hash.code.toCode % Varint.limit = 18
        rw [codeValue]
        decide
      have head : Varint.decode? (Multihash.encode hash ++ rest) =
          .ok (Wire.toVarint hash.code.toCode,
            Wire.encodeNat hash.digest.length ++ hash.digest ++ rest) := by
        simp [Multihash.encode, Wire.encodeNat, List.append_assoc, Varint.decodeEncodeSuffix]
      have hh := Multihash.decodeAtEncode hash rest
      simp only [encode, decodeAt?, head, Except.mapError, Bind.bind, Except.bind,
        codeRead, ite_true, hh, dite_eq_left valid]
  | v1 codec hash =>
      have hc : codec.toCode < Varint.limit := ContentCodec.codeLt codec
      have hOne : (Wire.toVarint 1).val = 1 := by decide
      have hCodec : (Wire.toVarint codec.toCode).val = codec.toCode :=
        Nat.mod_eq_of_lt hc
      have hh := Multihash.decodeAtEncode hash rest
      simp [encode, decodeAt?, Wire.encodeNat, List.append_assoc,
        Varint.decodeEncodeSuffix, hOne, hCodec,
        ContentCodec.ofCodeToCode, hh, Bind.bind, Except.bind, Except.mapError]

/-- The complete value is recovered with an empty suffix. -/
theorem decodeEncode (value : Cid) : decode? (encode value) = .ok (value, []) := by
  have h := decodeAtEncode value []
  simp only [List.append_nil] at h
  simp [decode?, h, Bind.bind, Except.bind]

/-- A successful prefix parser reconstructs the exact consumed spelling. -/
theorem decodeAtOk (input : List Nat) (value : Cid) (rest : List Nat)
    (h : decodeAt? input = .ok (value, rest)) : input = encode value ++ rest := by
  cases hv : Varint.decode? input with
  | error error => simp [decodeAt?, hv, Except.mapError, Bind.bind, Except.bind] at h
  | ok pair =>
      obtain ⟨version, tail⟩ := pair
      simp only [decodeAt?, hv, Except.mapError, Bind.bind, Except.bind] at h
      split at h
      · cases hm : Multihash.decodeAt? input with
        | error error => simp [hm] at h
        | ok pair =>
            obtain ⟨hashValue, after⟩ := pair
            simp only [hm] at h
            split at h
            · have he := Prod.mk.inj (Except.ok.inj h)
              rcases he with ⟨rfl, rfl⟩
              exact Multihash.decodeAtOk input hashValue after hm
            · cases h
      · split at h
        · rename_i versionEq
          cases hc : Varint.decode? tail with
          | error error => simp [hc] at h
          | ok pair =>
              obtain ⟨rawCodec, afterCodec⟩ := pair
              simp only [hc] at h
              cases ht : ContentCodec.ofCode? rawCodec.val with
              | none => simp [ht] at h
              | some codec =>
                  simp only [ht] at h
                  split at h
                  · rename_i codeEq
                    cases hm : Multihash.decodeAt? afterCodec with
                    | error error => simp [hm] at h
                    | ok pair =>
                        obtain ⟨hashValue, after⟩ := pair
                        simp only [hm] at h
                        have he := Prod.mk.inj (Except.ok.inj h)
                        rcases he with ⟨rfl, rfl⟩
                        have header := Varint.encodeDecode hv
                        have content := Varint.encodeDecode hc
                        have digest := Multihash.decodeAtOk afterCodec hashValue after hm
                        have hall := header.trans (congrArg (Varint.encode version ++ ·)
                          (content.trans (congrArg (Varint.encode rawCodec ++ ·) digest)))
                        have vOne : Wire.toVarint 1 = version := by
                          rw [← versionEq]
                          exact Wire.toVarintVal version
                        simpa only [encode, Wire.encodeNat, codeEq, Wire.toVarintVal,
                          vOne, List.append_assoc] using hall
                  · cases h
        · cases h

/-- Standalone accepted inputs have no trailing spelling. -/
theorem encodeDecode (input : List Nat) (value : Cid) (rest : List Nat)
    (h : decode? input = .ok (value, rest)) : input = encode value ++ rest := by
  cases hd : decodeAt? input with
  | error error => simp [decode?, hd, Bind.bind, Except.bind] at h
  | ok pair =>
      obtain ⟨parsed, tail⟩ := pair
      simp only [decode?, hd, Bind.bind, Except.bind] at h
      split at h
      · rename_i empty
        subst tail
        have he := Prod.mk.inj (Except.ok.inj h)
        rcases he with ⟨rfl, rfl⟩
        exact decodeAtOk input parsed [] hd
      · cases h

/-- The CID codec shares the common decoder-error vocabulary. -/
instance : Bytes.Codec Cid where
  encode := encode
  decode? input := (decode? input).mapError Error.toDecodeError

/-- Both laws use the CID proofs, including the version-zero shape invariant. -/
instance : Bytes.LawfulCodec Cid where
  decodeEncode value := by
    change (decode? (encode value)).mapError Error.toDecodeError = _
    rw [decodeEncode]
    rfl
  encodeDecode input value rest h := by
    change (decode? input).mapError Error.toDecodeError = .ok (value, rest) at h
    cases hd : decode? input with
    | error error => simp [hd, Except.mapError] at h
    | ok pair =>
        simp only [hd, Except.mapError, Except.ok.injEq] at h
        cases h
        exact (encodeDecode input value rest hd).symm

/-- Two different valid CID values cannot share one binary encoding. -/
theorem encodeInjective {a b : Cid} (h : encode a = encode b) : a = b := by
  have left := decodeEncode a
  rw [h, decodeEncode b] at left
  exact (Prod.mk.inj (Except.ok.inj left)).1.symm

/-- Every version emits byte-valued model entries. -/
theorem encodeBytes (value : Cid) : ∀ b ∈ encode value, b < 256 := by
  cases value with
  | v0 hash valid => exact Multihash.encodeBytes hash
  | v1 codec hash =>
      intro b hb
      simp only [encode, List.mem_append] at hb
      rcases hb with (hb | hb) | hb
      · exact Varint.encodeBytes (Wire.toVarint 1) b hb
      · exact Varint.encodeBytes (Wire.toVarint codec.toCode) b hb
      · exact Multihash.encodeBytes hash b hb

/-- The byte path independently follows version, content code, and digest boundaries. -/
def decodeAtB? (input : ByteArray) (position : Nat := 0) : Except Error (Cid × Nat) := do
  let (version, next) ← Wire.readVarintAt input position
  if version.val = 18 then
    let (hash, after) ← Multihash.decodeAtB? input position
    let value ← v0? hash
    .ok (value, after)
  else if version.val = 1 then
    let (rawCodec, next) ← Wire.readVarintAt input next
    let codec ← match ContentCodec.ofCode? rawCodec.val with
      | none => .error .badCid
      | some codec => .ok codec
    let (hash, after) ← Multihash.decodeAtB? input next
    .ok (.v1 codec hash, after)
  else .error .badCid

/-- The standalone byte boundary also checks exact consumption. -/
def ofByteArray? (input : ByteArray) : Except Error Cid := do
  let (value, used) ← decodeAtB? input
  if used = input.size then .ok value else .error .badCid

/-- The production encoder composes byte builders rather than encoded model lists. -/
def toByteArray (value : Cid) : ByteArray :=
  match value with
  | .v0 hash _ => hash.toByteArray
  | .v1 codec hash =>
      hash.appendB (Wire.writeNatB codec.toCode (Wire.writeNatB 1 ByteArray.empty))

/-- Either version owns exactly one multihash. -/
def hash : Cid → Multihash
  | .v0 hash _ | .v1 _ hash => hash

/-- Version zero uses bare base58; version one uses registered base32. -/
def toString (value : Cid) : String :=
  match value with
  | .v0 hash _ => Base58.encode hash.toByteArray
  | .v1 _ _ => Multibase.encodeBase32 value.toByteArray

/-- Text parsing accepts a bare version-zero string or a multibase form. -/
def ofString? (text : String) : Except Error Cid := do
  if text.startsWith "Qm" then ofByteArray? (← Base58.decode? text)
  else
    let (_, bytes) ← Multibase.decode? text
    ofByteArray? bytes

end Cid

end Multiformats
