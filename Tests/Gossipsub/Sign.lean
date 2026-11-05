import Tests.Support
import Libp2p.Protocols.Gossipsub.Sign

/-!
# Gossipsub suite: Sign

The checks of `Libp2p.Protocols.Gossipsub.Sign` against
`vendor/specs/pubsub/README.md`, sections Message Signing, Signature
Policy Options, and Message Identification.

The verify and encode functions are executable stand-ins. The
signature math belongs to the crypto package, so the stand-in verifier
answers `true` or `false` and the checks pin the policy logic. The
kernel examples at the end show that each rejection arm is reachable.
Each example closes by `rfl`.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Sign

open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Sign
open Libp2p.Protocols.Mock.Identity

/-- An encoder that reads the `from`, `data`, `seqno`, and topic fields.
It reads neither the `signature` nor the `key` field. -/
private def testEncode (m : Message) : List Nat :=
  m.from.getD [] ++ m.data.getD [] ++ m.seqno.getD [] ++
    Bytes.toNatList (Bytes.ofString m.topic.name)

/-- An encoder that reads every field and marks presence. The signature
input check needs this encoder. An input that fails to clear the
`signature` or `key` field still changes under this encoder, so the
check detects that defect. -/
private def tagEncode (m : Message) : List Nat :=
  (match m.from with | none => [0] | some b => 1 :: b) ++
  (match m.data with | none => [0] | some b => 1 :: b) ++
  (match m.seqno with | none => [0] | some b => 1 :: b) ++
  (match m.signature with | none => [0] | some b => 1 :: b) ++
  (match m.key with | none => [0] | some b => 1 :: b) ++
    Bytes.toNatList (Bytes.ofString m.topic.name)

/-- The accepting stand-ins: a nonempty buffer parses as an ed25519
key, the derived peer id carries the key bytes, and the verifier
accepts. -/
private def testPrimsOk : Prims :=
  { unmarshalKey := fun bs => if bs.isEmpty then none else some ⟨.ed25519, bs⟩
    inlineKey := fun bs => if bs.isEmpty then none else some ⟨.ed25519, bs⟩
    idOfKey := fun k => k.data
    verify := fun _ _ _ => true }

/-- The rejecting stand-ins: the verifier rejects. -/
private def testPrimsBad : Prims :=
  { testPrimsOk with verify := fun _ _ _ => false }

/-- A message with the four signed fields set as given. -/
private def testMsg (fr sq sig key : Option (List Nat)) : Message :=
  { «from» := fr, data := some [9], seqno := sq, topic := ⟨"t"⟩,
    signature := sig, key := key }

/-- The UTF-8 bytes of `libp2p-pubsub:`, from
`vendor/specs/pubsub/README.md` Message Signing and the go reference
implementation. -/
private def prefixBytes : List Nat :=
  [108, 105, 98, 112, 50, 112, 45, 112, 117, 98, 115, 117, 98, 58]

/-! ## Reachability of the rejection arms

Each example names one arm and supplies a message that reaches it. -/

example : validate testPrimsOk testEncode .strictSign
    (testMsg none (some [2]) (some [3]) (some [4])) = .error .missingFrom := rfl

example : validate testPrimsOk testEncode .strictSign
    (testMsg (some [1]) none (some [3]) (some [4])) = .error .missingSeqno := rfl

example : validate testPrimsOk testEncode .strictSign
    (testMsg (some [1]) (some [2]) none (some [4])) = .error .missingSignature := rfl

example : validate testPrimsOk testEncode .strictSign
    (testMsg (some [1]) (some [2]) (some [3]) (some [])) = .error .keyUnresolved := rfl

example : validate testPrimsOk testEncode .strictSign
    (testMsg (some []) (some [2]) (some [3]) none) = .error .keyUnresolved := rfl

example : validate testPrimsOk testEncode .strictSign
    (testMsg (some [1]) (some [2]) (some [3]) (some [5])) = .error .keyMismatch := rfl

example : validate testPrimsBad testEncode .strictSign
    (testMsg (some [1]) (some [2]) (some [3]) (some [1])) = .error .badSignature := rfl

example : validate testPrimsOk testEncode .strictNoSign
    (testMsg (some [1]) none none none) = .error .hasFrom := rfl

example : validate testPrimsOk testEncode .strictNoSign
    (testMsg none (some [2]) none none) = .error .hasSeqno := rfl

example : validate testPrimsOk testEncode .strictNoSign
    (testMsg none none (some [3]) none) = .error .hasSignature := rfl

example : validate testPrimsOk testEncode .strictNoSign
    (testMsg none none none (some [4])) = .error .hasKey := rfl

/-! ## Reachability of the acceptance paths -/

example : validate testPrimsOk testEncode .strictSign
    (testMsg (some [1]) (some [2]) (some [3]) (some [1])) = .ok () := rfl

example : validate testPrimsOk testEncode .strictSign
    (testMsg (some [1]) (some [2]) (some [3]) none) = .ok () := rfl

example : validate testPrimsOk testEncode .strictNoSign
    (testMsg none none none none) = .ok () := rfl

/-- Run the checks of this module. -/
def run (r : Runner) : IO Unit := do
  r.section "gossipsub Sign" "vendor/specs/pubsub"

  -- strictNoSign, through the accepting stand-ins
  r.check "strictNoSign accepts a message with all four fields absent"
    (succeedsWith () (validate testPrimsOk testEncode .strictNoSign
      (testMsg none none none none)))
  r.check "strictNoSign rejects a present from"
    (failsWith SignError.hasFrom (validate testPrimsOk testEncode .strictNoSign
      (testMsg (some [1]) none none none)))
  r.check "strictNoSign rejects a present seqno"
    (failsWith SignError.hasSeqno (validate testPrimsOk testEncode .strictNoSign
      (testMsg none (some [2]) none none)))
  r.check "strictNoSign rejects a present signature"
    (failsWith SignError.hasSignature (validate testPrimsOk testEncode .strictNoSign
      (testMsg none none (some [3]) none)))
  r.check "strictNoSign rejects a present key"
    (failsWith SignError.hasKey (validate testPrimsOk testEncode .strictNoSign
      (testMsg none none none (some [4]))))

  -- strictSign, through the accepting stand-ins
  r.check "strictSign accepts a fully signed message"
    (succeedsWith () (validate testPrimsOk testEncode .strictSign
      (testMsg (some [1]) (some [2]) (some [3]) (some [1]))))
  r.check "strictSign accepts a message with the key inlined in from"
    (succeedsWith () (validate testPrimsOk testEncode .strictSign
      (testMsg (some [1]) (some [2]) (some [3]) none)))
  r.check "strictSign rejects a missing from"
    (failsWith SignError.missingFrom (validate testPrimsOk testEncode .strictSign
      (testMsg none (some [2]) (some [3]) none)))
  r.check "strictSign rejects a missing seqno"
    (failsWith SignError.missingSeqno (validate testPrimsOk testEncode .strictSign
      (testMsg (some [1]) none (some [3]) none)))
  r.check "strictSign rejects a missing signature"
    (failsWith SignError.missingSignature (validate testPrimsOk testEncode .strictSign
      (testMsg (some [1]) (some [2]) none none)))
  r.check "strictSign rejects a key field that does not parse"
    (failsWith SignError.keyUnresolved (validate testPrimsOk testEncode .strictSign
      (testMsg (some [1]) (some [2]) (some [3]) (some []))))
  r.check "strictSign rejects a peer id that inlines no key"
    (failsWith SignError.keyUnresolved (validate testPrimsOk testEncode .strictSign
      (testMsg (some []) (some [2]) (some [3]) none)))
  r.check "strictSign rejects a key that derives another peer id"
    (failsWith SignError.keyMismatch (validate testPrimsOk testEncode .strictSign
      (testMsg (some [1]) (some [2]) (some [3]) (some [5]))))
  r.check "strictSign rejects a bad signature"
    (failsWith SignError.badSignature (validate testPrimsBad testEncode .strictSign
      (testMsg (some [1]) (some [2]) (some [3]) (some [1]))))

  -- message id
  r.check "default msg id is from followed by seqno"
    (defaultMsgId (testMsg (some [1, 2]) (some [3, 4, 5]) none none) ==
      ⟨[1, 2, 3, 4, 5]⟩)
  r.check "default msg id is empty when the fields are absent"
    (defaultMsgId (testMsg none none none none) == ⟨[]⟩)

  -- signature input
  r.check "sign input starts with the libp2p-pubsub prefix"
    ((signInput testEncode (testMsg (some [1]) (some [2]) (some [3]) none)).take 14 ==
      prefixBytes)
  r.check "sign input drops the signature and key fields"
    (signInput tagEncode (testMsg (some [1]) (some [2]) (some [3]) (some [4])) ==
      signInput tagEncode (testMsg (some [1]) (some [2]) (some [7]) (some [8])) &&
     signInput tagEncode (testMsg (some [1]) (some [2]) (some [3]) none) ==
      signInput tagEncode (testMsg (some [1]) (some [2]) (some [7]) (some [8])))
  r.check "sign input covers the data field"
    (signInput tagEncode (testMsg (some [1]) (some [2]) (some [3]) none) !=
      signInput tagEncode
        ({ testMsg (some [1]) (some [2]) (some [3]) none with data := some [10] }))

end Tests.Gossipsub.Sign
