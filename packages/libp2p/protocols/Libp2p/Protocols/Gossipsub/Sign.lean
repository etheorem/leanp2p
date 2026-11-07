import Libp2p.Protocols.Gossipsub.Types
import Libp2p.Identity
import Bytes

/-!
# Gossipsub signing policy

This module holds the signing policy check, the bytes a signature
covers, and the default message id of gossipsub v1.1. The vendored
spec is `vendor/specs/pubsub/README.md`, sections Message Signing,
Signature Policy Options, and Message Identification.

## Policy decision

The router uses `strictNoSign` by default. The project targets the
Ethereum consensus layer, and that layer requires the StrictNoSign
policy for gossipsub v1.1 messages:
<https://github.com/ethereum/consensus-specs/blob/dev/specs/phase0/p2p-interface.md>.
The libp2p pubsub spec defines the policy options:
<https://github.com/libp2p/specs/blob/master/pubsub/README.md#signature-policy-options>.
Under `strictNoSign` the four signed fields are absent, so the default
message id is empty. The consensus layer supplies a content-addressed
id function through `MsgIdFn`. The hash itself is outside this module.

The two lax options stay out. The spec marks them legacy, and the
project does not target them.

## The signature input

The bytes that a signature covers are the UTF-8 bytes of the string
`libp2p-pubsub:` followed by the encoded message with the `signature`
and `key` fields absent. The vendored spec excludes the signature
field (Message Signing). The go reference implementation also clears
the key field before it signs, so this module clears both fields.
The encoder is a parameter. The rpc module supplies the protobuf
encoder at integration.

## Check order

Under `strictSign` the check order is: `from`, `seqno`, `signature`,
key resolution, key match, verify. The key match applies when the
`key` field is present. An absent field produces its own error. Under
`strictNoSign` the check order is: `from`, `seqno`, `signature`,
`key`. The first present field decides the error. Both orders are
fixed here, so the error of a message with several faults is well
defined.

The key resolution takes a key from the `key` field when that field is
present, and from the peer id otherwise. A `key` field that does not
parse never falls back to the peer id. This rule matches the go
reference.

## The message id

The default id is the concatenation of `from` and `seqno`. An absent
field adds no bytes. The spec calls this strategy origin stamping
(Message Identification). `MsgIdFn` is the type of a caller-supplied
id function.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Sign

open Libp2p.Identity

/-- The two deterministic signature policies of the spec. The spec
names no numeric codes for the policies, so this is a plain inductive
with no code pair. -/
inductive SignPolicy where
  /-- Require `from`, `seqno`, and `signature`, resolve the key, and
  verify the signature. -/
  | strictSign
  /-- Require the four signed fields to be absent. -/
  | strictNoSign
  deriving DecidableEq, BEq, Repr

/-- The rejection reasons of `validate`. Each arm names one reason.
The first six arms belong to `strictSign`, the last four to
`strictNoSign`. -/
inductive SignError where
  /-- `strictSign`: the `from` field is absent. -/
  | missingFrom
  /-- `strictSign`: the `seqno` field is absent. -/
  | missingSeqno
  /-- `strictSign`: the `signature` field is absent. -/
  | missingSignature
  /-- `strictSign`: the `key` field does not parse, or the `from`
  field inlines no key. -/
  | keyUnresolved
  /-- `strictSign`: the key of the `key` field derives another peer
  id than `from`. -/
  | keyMismatch
  /-- `strictSign`: the verifier rejects the signature. -/
  | badSignature
  /-- `strictNoSign`: the `from` field is present. -/
  | hasFrom
  /-- `strictNoSign`: the `seqno` field is present. -/
  | hasSeqno
  /-- `strictNoSign`: the `signature` field is present. -/
  | hasSignature
  /-- `strictNoSign`: the `key` field is present. -/
  | hasKey
  deriving DecidableEq, BEq, Repr

/-- The signing prefix of the spec and of the go reference
implementation. -/
def signPrefix : String := "libp2p-pubsub:"

/-- The prefix as UTF-8 bytes. -/
def signPrefixBytes : List Nat := Bytes.toNatList (Bytes.ofString signPrefix)

/-- The functions that the router wires to the real packages at
integration.

`unmarshalKey` parses the `key` field. `inlineKey` extracts a key that
the peer id inlines. `idOfKey` derives the peer id bytes of a key.
`verify` checks a signature over the signed bytes. All four functions
are total, and the caller supplies them. -/
structure Prims where
  /-- Parse the `key` field. -/
  unmarshalKey : List Nat → Option PubKey
  /-- Extract the key that a peer id inlines. -/
  inlineKey : List Nat → Option PubKey
  /-- Derive the peer id bytes of a key. -/
  idOfKey : PubKey → List Nat
  /-- Check a signature over the signed bytes. -/
  verify : PubKey → List Nat → List Nat → Bool

/-- The identity functions at the router boundary. A failed derivation
gives empty bytes, which cannot encode a peer id. The inline path reads
only an identity multihash and checks its public key protobuf. -/
def Prims.identity : Prims where
  unmarshalKey bs := (PubKey.unmarshal? (Bytes.ofNatList bs)).toOption
  inlineKey bs := do
    let peer ← (PeerId.ofBytes? (Bytes.ofNatList bs)).toOption
    if peer.hash.code != .«identity» then none
    else (PubKey.unmarshal? (Bytes.ofNatList peer.hash.digest)).toOption
  idOfKey k := ((PeerId.ofPubKey k).toOption.map
    (fun peer => Bytes.toNatList peer.toBytes)).getD []
  verify k msg sig := k.verify (Bytes.ofNatList msg) (Bytes.ofNatList sig)

/-- The bytes a signature covers: the prefix, then the encoded message
with the `signature` and `key` fields absent. -/
def signInput (encode : Message → List Nat) (m : Message) : List Nat :=
  signPrefixBytes ++ encode { m with signature := none, key := none }

/-- Check a message against a signature policy.

Under `strictNoSign`, the first present field of `from`, `seqno`,
`signature`, and `key` produces its error arm.

Under `strictSign`, the checks run in this order: `from`, `seqno`,
`signature`, key resolution, key match, verify. A `key` field that is
present must parse, and the derived peer id must equal `from`. An
absent `key` field resolves through the peer id. -/
def validate (p : Prims) (encode : Message → List Nat) (policy : SignPolicy)
    (m : Message) : Except SignError Unit :=
  match policy, m with
  | .strictNoSign, m =>
      if m.from.isSome then .error .hasFrom
      else if m.seqno.isSome then .error .hasSeqno
      else if m.signature.isSome then .error .hasSignature
      else if m.key.isSome then .error .hasKey
      else .ok ()
  | .strictSign, m =>
      match m.from with
      | none => .error .missingFrom
      | some fr =>
        match m.seqno with
        | none => .error .missingSeqno
        | some _ =>
          match m.signature with
          | none => .error .missingSignature
          | some sig =>
            match m.key with
            | some kb =>
              match p.unmarshalKey kb with
              | none => .error .keyUnresolved
              | some k =>
                if p.idOfKey k = fr then
                  if p.verify k (signInput encode m) sig then .ok ()
                  else .error .badSignature
                else .error .keyMismatch
            | none =>
              match p.inlineKey fr with
              | none => .error .keyUnresolved
              | some k =>
                if p.verify k (signInput encode m) sig then .ok ()
                else .error .badSignature

/-- A caller-supplied message id function. The consensus layer supplies
a content-addressed function. -/
abbrev MsgIdFn := Message → MessageId

/-- The default message id: `from` followed by `seqno`. An absent field
adds no bytes. -/
def defaultMsgId (m : Message) : MessageId :=
  ⟨m.from.getD [] ++ m.seqno.getD []⟩

/-! ## Theorems -/

/-- The UTF-8 bytes of the prefix are the expected 14 bytes. -/
theorem signPrefixBytes_eq :
    signPrefixBytes =
      [108, 105, 98, 112, 50, 112, 45, 112, 117, 98, 115, 117, 98, 58] := rfl

/-- `strictNoSign` accepts a message exactly when the four signed fields
are absent. -/
theorem validate_strictNoSign_iff (p : Prims) (encode : Message → List Nat)
    (m : Message) :
    validate p encode .strictNoSign m = .ok () ↔
      m.from = none ∧ m.seqno = none ∧ m.signature = none ∧ m.key = none := by
  rcases m with ⟨fr, d, sq, t, sig, key⟩
  cases fr <;> cases sq <;> cases sig <;> cases key <;> simp [validate]

/-- `strictSign` acceptance implies that `from`, `seqno`, and
`signature` are present, and that the verifier accepted the signature
over the signed bytes. -/
theorem validate_strictSign_sound (p : Prims) (encode : Message → List Nat)
    (m : Message) :
    validate p encode .strictSign m = .ok () →
      m.from.isSome ∧ m.seqno.isSome ∧
      ∃ k sig, m.signature = some sig ∧
        p.verify k (signInput encode m) sig = true := by
  intro h
  rcases m with ⟨fr, d, sq, t, sig, key⟩
  cases fr with
  | none => simp [validate] at h
  | some fr =>
    cases sq with
    | none => simp [validate] at h
    | some sq =>
      cases sig with
      | none => simp [validate] at h
      | some sig =>
        cases key with
        | none =>
          cases hik : p.inlineKey fr with
          | none => simp [validate, hik] at h
          | some k =>
            simp [validate, hik] at h
            exact ⟨rfl, rfl, k, sig, rfl, h⟩
        | some kb =>
          cases huk : p.unmarshalKey kb with
          | none => simp [validate, huk] at h
          | some k =>
            by_cases hm : p.idOfKey k = fr
            · simp [validate, huk, hm] at h
              exact ⟨rfl, rfl, k, sig, rfl, h⟩
            · simp [validate, huk, hm] at h

/-- Under `strictSign`, an accepted message with a `key` field has a
key that parses and derives the peer id in `from`. This theorem pins
the key match check, which the soundness theorem does not name. -/
theorem validate_strictSign_keyField_binding (p : Prims)
    (encode : Message → List Nat) (m : Message) :
    validate p encode .strictSign m = .ok () → m.key.isSome →
      ∃ kb k, m.key = some kb ∧ p.unmarshalKey kb = some k ∧
        m.from = some (p.idOfKey k) := by
  intro h hsome
  rcases m with ⟨fr, d, sq, t, sig, key⟩
  cases fr with
  | none => simp [validate] at h
  | some fr =>
    cases sq with
    | none => simp [validate] at h
    | some sq =>
      cases sig with
      | none => simp [validate] at h
      | some sig =>
        cases key with
        | none => simp at hsome
        | some kb =>
          cases huk : p.unmarshalKey kb with
          | none => simp [validate, huk] at h
          | some k =>
            by_cases hm : p.idOfKey k = fr
            · simp [validate, huk, hm] at h
              exact ⟨kb, k, rfl, huk, by simp [hm]⟩
            · simp [validate, huk, hm] at h

/-- The bytes of the signature input do not depend on the `signature`
and `key` fields. -/
theorem signInput_signature_key_irrelevant (encode : Message → List Nat)
    (m : Message) (s s' k k' : Option (List Nat)) :
    signInput encode { m with signature := s, key := k } =
      signInput encode { m with signature := s', key := k' } := by
  simp [signInput]

/-- The signature input starts with the prefix bytes. -/
theorem signInput_prefix (encode : Message → List Nat) (m : Message) :
    (signInput encode m).take signPrefixBytes.length = signPrefixBytes := by
  simp [signInput]

/-- The default message id ignores the payload and the topic. -/
theorem defaultMsgId_ignores_payload (m : Message) (d' : Option (List Nat))
    (t' : TopicId) :
    defaultMsgId { m with data := d', topic := t' } = defaultMsgId m := rfl

/-- An accepted `strictNoSign` message has the empty default message
id. -/
theorem strictNoSign_ok_defaultMsgId_empty (p : Prims)
    (encode : Message → List Nat) (m : Message) :
    validate p encode .strictNoSign m = .ok () → defaultMsgId m = ⟨[]⟩ := by
  intro h
  have h' := (validate_strictNoSign_iff p encode m).mp h
  simp [defaultMsgId, h'.1, h'.2.1]

/-- The ten rejection arms are pairwise distinct. -/
theorem signError_arms_nodup :
    [SignError.missingFrom, SignError.missingSeqno, SignError.missingSignature,
      SignError.keyUnresolved, SignError.keyMismatch, SignError.badSignature,
      SignError.hasFrom, SignError.hasSeqno, SignError.hasSignature,
      SignError.hasKey].Nodup := by
  decide

end Libp2p.Protocols.Gossipsub.Sign
