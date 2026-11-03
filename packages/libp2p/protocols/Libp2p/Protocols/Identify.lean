import Proto
import Bytes
import Libp2p.Protocols.Mock.Identity
import Libp2p.Protocols.Mock.Multiaddr
import Libp2p.Protocols.Constants

/-!
# Identify message and validate

The pure half of `/ipfs/id/1.0.0` (sub-unit 1a): the `Identify`
message with its `ProtoMessage` instance, the strict field table, the
validate, and the table theorems. The client and the handler values
are sub-unit 1b.

The wire shape comes from go-libp2p v0.50.0 `identify.pb.go`: fields
1, 2, 3, 4, 5, 6, and 8. Field 8 is the signed peer record. The emit
order is ascending field number, the order of the captured wire.

The table is strict on singular fields: a present field with the
wrong wire type, or a present string field with invalid UTF-8, is
`Pb.Error.badField`, gated by `Pb.hasField`. Repeated fields stay
permissive: entries of another wire type are skipped, and invalid
UTF-8 entries are dropped, as the Proto accessors already do.

The strings read back through the real `Bytes.toString?`, never
through `Pb.getStr?`. The latter runs the opaque mock of
`Pb.Mock.Bytes`, which no theorem can relate to `Bytes.ofString`.
-/

set_option autoImplicit false

namespace Libp2p.Protocols

open Mock

/-- One identify answer. The field numbers are the ones of the
go-libp2p v0.50.0 identify protobuf. -/
structure Identify where
  publicKey : Option (List Nat)        -- field 1, the serialized PublicKey protobuf
  listenAddrs : List (List Nat)        -- field 2, binary multiaddrs, repeated
  protocols : List String              -- field 3, repeated
  observedAddr : Option (List Nat)     -- field 4
  protocolVersion : Option String      -- field 5
  agentVersion : Option String         -- field 6
  signedPeerRecord : Option (List Nat) -- field 8, opaque bytes
  deriving Repr, BEq, DecidableEq

namespace Identify

open Mock.Identity Mock.Multiaddr

/-- The identify protocol id. -/
def protocolId : Mock.Core.ProtocolId := Constants.identifyId

/-- The identify push protocol id. -/
def pushId : Mock.Core.ProtocolId := Constants.identifyPushId

/-- The wire image: one entry per present field, in the ascending
order 1, 2, 3, 4, 5, 6, 8. Strings go to bytes with the real
`Bytes` package. -/
def entries (m : Identify) : List Pb.Entry :=
  m.publicKey.toList.map (fun b => (1, Pb.Value.bytes b))
  ++ m.listenAddrs.map (fun b => (2, Pb.Value.bytes b))
  ++ m.protocols.map (fun s => (3, Pb.Value.bytes (Bytes.toNatList (Bytes.ofString s))))
  ++ m.observedAddr.toList.map (fun b => (4, Pb.Value.bytes b))
  ++ m.protocolVersion.toList.map (fun s => (5, Pb.Value.bytes (Bytes.toNatList (Bytes.ofString s))))
  ++ m.agentVersion.toList.map (fun s => (6, Pb.Value.bytes (Bytes.toNatList (Bytes.ofString s))))
  ++ m.signedPeerRecord.toList.map (fun b => (8, Pb.Value.bytes b))

/-- Fail closed. A message whose entries do not fit the wire model
emits no entry; every theorem about the encode takes the validity as
a premise. A payload of `List Nat` and a `String` carry no bound, so
the gate cannot be dropped. -/
def toFields (m : Identify) : Pb.Fields :=
  if h : ∀ e ∈ m.entries, e.Valid then ⟨m.entries, h⟩ else Pb.Fields.empty

/-- A present singular payload must be length-delimited. A miss means
absent. -/
private def bytesField? (num : Nat) (fs : Pb.Fields) : Except Pb.Error (Option (List Nat)) :=
  if Pb.hasField num fs then
    match Pb.getBytes? num fs with
    | some bs => .ok (some bs)
    | none => .error .badField
  else .ok none

/-- A present singular string must be length-delimited and valid
UTF-8. A miss means absent. -/
private def strField? (num : Nat) (fs : Pb.Fields) : Except Pb.Error (Option String) :=
  if Pb.hasField num fs then
    match (Pb.getBytes? num fs).bind (fun bs => Bytes.toString? (Bytes.ofNatList bs)) with
    | some s => .ok (some s)
    | none => .error .badField
  else .ok none

/-- The field table: strict singular fields, permissive repeated
fields. Unknown fields stay untouched in the wire view. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error Identify := do
  let publicKey ← bytesField? 1 fs
  let observedAddr ← bytesField? 4 fs
  let protocolVersion ← strField? 5 fs
  let agentVersion ← strField? 6 fs
  let signedPeerRecord ← bytesField? 8 fs
  .ok { publicKey,
        listenAddrs := Pb.getAllBytes 2 fs,
        protocols := (Pb.getAllBytes 3 fs).filterMap
          (fun bs => Bytes.toString? (Bytes.ofNatList bs)),
        observedAddr, protocolVersion, agentVersion, signedPeerRecord }

instance : Pb.ProtoMessage Identify where
  toFields := toFields
  ofFields? := ofFields?

/-! ## The table theorems

I1, the table law, carries the wire-validity premise. The two
round-trip theorems compose it with the Proto laws. -/

/-- A miss lookup through a segment that maps payloads to another
field number. -/
private theorem lookupMissMap {α : Type} (k n : Nat) (h : k ≠ n) (g : α → Pb.Value)
    (l : List α) :
    List.lookup k (l.map fun x => (n, g x)).reverse = none := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      have hb : (k == n) = false := by simpa using h
      simp [List.lookup_append, ih, List.lookup, hb]

/-- A filterMap of constant `none` drops every entry. -/
private theorem filterMapNone {α β : Type} (l : List α) :
    l.filterMap (fun _ => (none : Option β)) = [] :=
  List.filterMap_eq_nil_iff.mpr fun _ _ => rfl

/-- I1: the table law. Every valid message round-trips through its
own table. -/
theorem ofFieldsToFields (m : Identify) (h : ∀ e ∈ m.entries, e.Valid) :
    Pb.ProtoMessage.ofFields? (α := Identify) (Pb.ProtoMessage.toFields m) = .ok m := by
  change ofFields? (toFields m) = .ok m
  rw [toFields, dite_eq_left h]
  obtain ⟨pk, la, ps, oa, pv, av, spr⟩ := m
  simp only [ofFields?, bytesField?, strField?, Pb.hasField, Pb.getBytes?, Pb.getAllBytes,
    Pb.lookupLast]
  cases pk <;> cases oa <;> cases pv <;> cases av <;> cases spr <;>
    simp [entries, List.lookup_append, List.reverse_append, List.filterMap_append,
      List.any_append, Bind.bind, Except.bind, Bytes.ofNatListToNatList,
      Bytes.toString?OfString, Function.comp_def, List.lookup_cons, filterMapNone,
      lookupMissMap]

/-- I2: an encode decodes back to the message. -/
theorem decodeEncode (m : Identify) (h : ∀ e ∈ m.entries, e.Valid) :
    Pb.decodeMessage? (Pb.encodeMessage m) = .ok (m, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields m h,
    Bind.bind, Except.bind]

/-- I3: equal encodings imply equal messages. Without the premise
the statement is false: a message with an out-of-range byte and the
empty message both encode to `[]`. -/
theorem encodeInjective (a b : Identify) (ha : ∀ e ∈ a.entries, e.Valid)
    (hb : ∀ e ∈ b.entries, e.Valid)
    (h : Pb.encodeMessage a = Pb.encodeMessage b) : a = b := by
  have hf : toFields a = toFields b := Pb.encodeInjective h
  have h3 : Pb.ProtoMessage.ofFields? (α := Identify) (Pb.ProtoMessage.toFields a) =
      Pb.ProtoMessage.ofFields? (α := Identify) (Pb.ProtoMessage.toFields b) :=
    congrArg (fun fs => Pb.ProtoMessage.ofFields? (α := Identify) fs) hf
  rw [ofFieldsToFields a ha, ofFieldsToFields b hb] at h3
  exact Except.ok.inj h3

/-- I4: the repeated fields survive the round trip in order. -/
theorem roundTripRepeated (m : Identify) (h : ∀ e ∈ m.entries, e.Valid) :
    ∃ m' : Identify, Pb.decodeMessage? (Pb.encodeMessage m) = .ok (m', []) ∧
      m'.protocols = m.protocols ∧ m'.listenAddrs = m.listenAddrs :=
  ⟨m, decodeEncode m h, rfl, rfl⟩

/-! ## Validate

The checks run in this order: cap, decode, key presence, key parse,
expected id, addresses. The cap check runs before any decode. -/

/-- The validate failures. The zero-length rule of the read path is
sub-unit 1b, so the pure validate sees an empty payload as an empty
message, which then fails with `missingKey`. -/
inductive Error where
  | overCap
  | badMessage (e : Pb.Error)
  | missingKey
  | badKey
  | keyMismatch
  | badAddress
  deriving DecidableEq, BEq, Repr

/-- The address checks: every listening address and the observed
address, when present, must be valid bytes. -/
private def checkAddrs (m : Identify) (k : Mock.Identity.PubKey) :
    Except Error (Identify × Mock.Identity.PeerId) :=
  if ∀ a ∈ m.listenAddrs, validBytes a then
    if ∀ a ∈ m.observedAddr.toList, validBytes a then
      .ok (m, peerIdOfPubKey k)
    else .error .badAddress
  else .error .badAddress

/-- Validate one received response: the derived peer id must match
the expected id, and the size must stay under the cap. -/
def validate (payload : List Nat) (expected : Option Mock.Identity.PeerId) :
    Except Error (Identify × Mock.Identity.PeerId) :=
  if Constants.identifyCap < payload.length then .error .overCap
  else match (Pb.decodeMessage? payload : Except Pb.Error (Identify × List Nat)) with
    | .error e => .error (.badMessage e)
    | .ok (m, _) =>
      match m.publicKey with
      | none => .error .missingKey
      | some kb =>
        match unmarshalPubKey? kb with
        | none => .error .badKey
        | some k =>
          match expected with
          | none => checkAddrs m k
          | some e =>
            if peerIdOfPubKey k = e then checkAddrs m k
            else .error .keyMismatch

/-- The address check accepts exactly the messages whose addresses
are all valid. -/
private theorem checkAddrsSound (m : Identify) (k : Mock.Identity.PubKey)
    (m' : Identify) (pid : Mock.Identity.PeerId)
    (h : checkAddrs m k = .ok (m', pid)) :
    (∀ a ∈ m.listenAddrs, validBytes a) ∧
      (∀ a ∈ m.observedAddr.toList, validBytes a) ∧
      m' = m ∧ pid = peerIdOfPubKey k := by
  unfold checkAddrs at h
  by_cases ha : ∀ a ∈ m.listenAddrs, validBytes a
  · by_cases ho : ∀ a ∈ m.observedAddr.toList, validBytes a
    · rw [ite_eq_left ha, ite_eq_left ho] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ha, ho, rfl, rfl⟩
    · rw [ite_eq_left ha, ite_eq_right ho] at h
      cases h
  · rw [ite_eq_right ha] at h
    cases h

/-- I5: an over-cap payload fails before any decode. -/
theorem validateOverCap (payload : List Nat) (expected : Option Mock.Identity.PeerId)
    (h : Constants.identifyCap < payload.length) :
    validate payload expected = .error .overCap := by
  simp [validate, h]

/-- I6: the empty payload is the empty message, and it has no key. -/
theorem decodeEmpty :
    Pb.decodeMessage? (α := Identify) [] = .ok (⟨none, [], [], none, none, none, none⟩, []) :=
  rfl

theorem validateEmptyNoKey : validate [] none = .error .missingKey := rfl

/-- I7: acceptance, conditional on the opaque mock results. -/
theorem validateAccepts (payload : List Nat) (m : Identify) (kb : List Nat)
    (k : Mock.Identity.PubKey) (expected : Option Mock.Identity.PeerId)
    (hsize : payload.length ≤ Constants.identifyCap)
    (hdec : Pb.decodeMessage? (α := Identify) payload = .ok (m, []))
    (hpub : m.publicKey = some kb)
    (hun : Mock.Identity.unmarshalPubKey? kb = some k)
    (hderive : ∀ e, expected = some e → Mock.Identity.peerIdOfPubKey k = e)
    (haddrs : ∀ a ∈ m.listenAddrs, validBytes a)
    (hobs : ∀ a ∈ m.observedAddr.toList, validBytes a) :
    validate payload expected = .ok (m, peerIdOfPubKey k) := by
  unfold validate
  rw [ite_eq_right (by omega)]
  simp only [hdec, hpub, hun]
  split
  · simp only [checkAddrs]
    rw [ite_eq_left haddrs, ite_eq_left hobs]
  · rename_i e
    have hk : Mock.Identity.peerIdOfPubKey k = e := hderive e rfl
    rw [ite_eq_left hk]
    simp only [checkAddrs]
    rw [ite_eq_left haddrs, ite_eq_left hobs]

/-- I8: a derived id that differs from the expected id is rejected. -/
theorem validateKeyMismatch (payload : List Nat) (m : Identify) (kb : List Nat)
    (k : Mock.Identity.PubKey) (e : Mock.Identity.PeerId)
    (hsize : payload.length ≤ Constants.identifyCap)
    (hdec : Pb.decodeMessage? (α := Identify) payload = .ok (m, []))
    (hpub : m.publicKey = some kb)
    (hun : Mock.Identity.unmarshalPubKey? kb = some k)
    (hne : Mock.Identity.peerIdOfPubKey k ≠ e) :
    validate payload (some e) = .error .keyMismatch := by
  unfold validate
  rw [ite_eq_right (by omega)]
  simp only [hdec, hpub, hun]
  split
  · rename_i hh
    exact absurd hh hne
  · rfl

/-- I9: soundness. A passing validate carries the cap bound, the
key facts, the derivation match, and the address validity. With I7
and I8 this pins the acceptance set exactly. -/
theorem validateSound (payload : List Nat) (expected : Option Mock.Identity.PeerId)
    (m : Identify) (pid : Mock.Identity.PeerId)
    (h : validate payload expected = .ok (m, pid)) :
    payload.length ≤ Constants.identifyCap ∧
      ∃ kb k, m.publicKey = some kb ∧ Mock.Identity.unmarshalPubKey? kb = some k ∧
        pid = Mock.Identity.peerIdOfPubKey k ∧
        (∀ e, expected = some e → Mock.Identity.peerIdOfPubKey k = e) ∧
        (∀ a ∈ m.listenAddrs, validBytes a) ∧
        (∀ a ∈ m.observedAddr.toList, validBytes a) := by
  unfold validate at h
  by_cases hcap : Constants.identifyCap < payload.length
  · rw [ite_eq_left hcap] at h
    cases h
  · rw [ite_eq_right hcap] at h
    cases hd : Pb.decodeMessage? (α := Identify) payload with
    | error e =>
        simp only [hd] at h
        cases h
    | ok pair =>
        obtain ⟨m', _⟩ := pair
        simp only [hd] at h
        cases hm : m'.publicKey with
        | none =>
            simp only [hm] at h
            cases h
        | some kb =>
            simp only [hm] at h
            cases hu : Mock.Identity.unmarshalPubKey? kb with
            | none =>
                simp only [hu] at h
                cases h
            | some k =>
                simp only [hu] at h
                cases he : expected with
                | none =>
                    simp only [he] at h
                    have hs := checkAddrsSound m' k m pid h
                    rcases hs with ⟨ha, ho, rfl, rfl⟩
                    refine ⟨Nat.le_of_not_lt hcap, ?_⟩
                    refine ⟨kb, k, hm, hu, rfl, ?_, ha, ho⟩
                    intro e' he'
                    cases he'
                | some e =>
                    simp only [he] at h
                    by_cases hkey : Mock.Identity.peerIdOfPubKey k = e
                    · rw [ite_eq_left hkey] at h
                      have hs := checkAddrsSound m' k m pid h
                      rcases hs with ⟨ha, ho, rfl, rfl⟩
                      refine ⟨Nat.le_of_not_lt hcap, ?_⟩
                      refine ⟨kb, k, hm, hu, rfl, ?_, ha, ho⟩
                      intro e' he'
                      cases he'
                      exact hkey
                    · rw [ite_eq_right hkey] at h
                      cases h

end Identify

end Libp2p.Protocols
