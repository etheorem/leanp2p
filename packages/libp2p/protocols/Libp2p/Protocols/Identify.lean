import Proto
import Bytes
import Conc
import Streams.Error
import Streams.Framing
import Streams.Stream
import Multiformats.Multiaddr.Binary
import Libp2p.Protocols.Mock.Identity
import Libp2p.Protocols.Mock.Host
import Libp2p.Protocols.Constants

/-!
# Identify

The pure half of `/ipfs/id/1.0.0`: the `Identify` message with its
`ProtoMessage` instance, the strict field table, the validate, the
table theorems, and `clientCore` with its theorems. The IO half: the
responder, the client, and the push handler.

The wire shape comes from go-libp2p v0.50.0 `identify.pb.go`: fields
1, 2, 3, 4, 5, 6, and 8. Field 8 is the signed peer record. The emit
order is ascending field number, the order of the captured wire.

The table is strict on singular fields: a present field with the
wrong wire type, or a present string field with invalid UTF-8, is
`Pb.Error.badField`, gated by `Pb.hasField`. Repeated fields stay
permissive: entries of another wire type are skipped, and invalid
UTF-8 entries are dropped, as the Proto accessors already do.

The strings read back through `Bytes.toString?`.

The private read loop `readFrameFrom` is a `partial def`: a silent
peer never ends the loop, and the deadline of `client` or `push` ends
it. `client` and `push` read one frame per stream and drop the bytes
after it. Go merges chunked identify messages; this client reads one.
The read rejects a zero-length frame, the spike's rule.
-/

set_option autoImplicit false

namespace Libp2p.Protocols

open Mock

/-- One identify response. The field numbers are the ones of the
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

open Mock.Identity

/-- The identify protocol id. -/
def protocolId : Mock.Core.ProtocolId := Constants.identifyId

/-- The identify push protocol id. -/
def pushId : Mock.Core.ProtocolId := Constants.identifyPushId

/-- The wire view: one entry per present singular field and per
element of a repeated field, in the ascending order 1, 2, 3, 4, 5, 6,
8. Strings go to bytes with the real `Bytes` package. -/
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
`toFields` must keep this check. -/
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

`ofFieldsToFields`, the table law, carries the wire-validity premise.
`decodeEncode`, `encodeInjective` and `roundTripRepeated` build on it
with the Proto laws. -/

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

/-- The table law. Every valid message round-trips through its
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

/-- An encode decodes back to the message. -/
theorem decodeEncode (m : Identify) (h : ∀ e ∈ m.entries, e.Valid) :
    Pb.decodeMessage? (Pb.encodeMessage m) = .ok (m, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields m h,
    Bind.bind, Except.bind]

/-- Equal encodings imply equal messages. Without the premise
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

/-- The repeated fields survive the round trip in order. -/
theorem roundTripRepeated (m : Identify) (h : ∀ e ∈ m.entries, e.Valid) :
    ∃ m' : Identify, Pb.decodeMessage? (Pb.encodeMessage m) = .ok (m', []) ∧
      m'.protocols = m.protocols ∧ m'.listenAddrs = m.listenAddrs :=
  ⟨m, decodeEncode m h, rfl, rfl⟩

/-! ## Validate

The checks run in this order: cap, decode, key presence, key parse,
expected id, addresses. The cap check runs before any decode. -/

/-- The validate failures, plus the read-path arms. The zero-length
rule lives on the read path, so the pure validate sees an empty payload
as an empty message, which then fails with `missingKey`. -/
inductive Error where
  | overCap
  | badMessage (e : Pb.Error)
  | missingKey
  | badKey
  | keyMismatch
  | badAddress
  /-- A zero-length frame on the read path, the spike's rule. -/
  | emptyFrame
  /-- The read deadline expired. -/
  | timeout
  /-- The stream returned an error. -/
  | stream (e : Streams.Error)
  deriving DecidableEq, BEq, Repr

/-- A binary address is valid exactly when the real Multiformats codec
decodes it. The decoder accepts the empty address; a truncated or
unknown component fails. -/
def validAddress (bytes : List Nat) : Bool :=
  (Multiformats.Multiaddr.ofBytes? bytes).isOk

/-- The address checks: every listening address and the observed
address, when present, must decode as a multiaddr. -/
private def checkAddrs (m : Identify) (k : Mock.Identity.PubKey) :
    Except Error (Identify × Mock.Identity.PeerId) :=
  if ∀ a ∈ m.listenAddrs, validAddress a then
    if ∀ a ∈ m.observedAddr.toList, validAddress a then
      .ok (m, peerIdOfPubKey k)
    else .error .badAddress
  else .error .badAddress

/-- Validate one received response: the size cap, the decode, the
presence and parse of `publicKey`, the derived id when the caller
supplies one, and every listen and observed address through
`Multiformats.Multiaddr.ofBytes?`. -/
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
    (∀ a ∈ m.listenAddrs, validAddress a) ∧
      (∀ a ∈ m.observedAddr.toList, validAddress a) ∧
      m' = m ∧ pid = peerIdOfPubKey k := by
  unfold checkAddrs at h
  by_cases ha : ∀ a ∈ m.listenAddrs, validAddress a
  · by_cases ho : ∀ a ∈ m.observedAddr.toList, validAddress a
    · rw [ite_eq_left ha, ite_eq_left ho] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ha, ho, rfl, rfl⟩
    · rw [ite_eq_left ha, ite_eq_right ho] at h
      cases h
  · rw [ite_eq_right ha] at h
    cases h

/-- An over-cap payload fails before any decode. -/
theorem validateOverCap (payload : List Nat) (expected : Option Mock.Identity.PeerId)
    (h : Constants.identifyCap < payload.length) :
    validate payload expected = .error .overCap := by
  simp [validate, h]

/-- The empty payload decodes to the empty message. -/
theorem decodeEmpty :
    Pb.decodeMessage? (α := Identify) [] = .ok (⟨none, [], [], none, none, none, none⟩, []) :=
  rfl

/-- The empty message has no key, so `validate` rejects it. -/
theorem validateEmptyNoKey : validate [] none = .error .missingKey := rfl

/-- Acceptance, conditional on the opaque mock results. -/
theorem validateAccepts (payload : List Nat) (m : Identify) (kb : List Nat)
    (k : Mock.Identity.PubKey) (expected : Option Mock.Identity.PeerId)
    (hsize : payload.length ≤ Constants.identifyCap)
    (hdec : Pb.decodeMessage? (α := Identify) payload = .ok (m, []))
    (hpub : m.publicKey = some kb)
    (hun : Mock.Identity.unmarshalPubKey? kb = some k)
    (hderive : ∀ e, expected = some e → Mock.Identity.peerIdOfPubKey k = e)
    (haddrs : ∀ a ∈ m.listenAddrs, validAddress a)
    (hobs : ∀ a ∈ m.observedAddr.toList, validAddress a) :
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

/-- `validate` rejects a derived id that differs from the expected id. -/
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

/-- Soundness. A passing validate carries the cap bound, the key
facts, the derivation match, and the address validity. The statement
does not tie `m` to the decode of `payload`; it omits the conjunct
`∃ rest, Pb.decodeMessage? (α := Identify) payload = .ok (m, rest)`. -/
theorem validateSound (payload : List Nat) (expected : Option Mock.Identity.PeerId)
    (m : Identify) (pid : Mock.Identity.PeerId)
    (h : validate payload expected = .ok (m, pid)) :
    payload.length ≤ Constants.identifyCap ∧
      ∃ kb k, m.publicKey = some kb ∧ Mock.Identity.unmarshalPubKey? kb = some k ∧
        pid = Mock.Identity.peerIdOfPubKey k ∧
        (∀ e, expected = some e → Mock.Identity.peerIdOfPubKey k = e) ∧
        (∀ a ∈ m.listenAddrs, validAddress a) ∧
        (∀ a ∈ m.observedAddr.toList, validAddress a) := by
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

/-! ## The responder

The responder builds one message from the host data, writes one
length-delimited frame, and half-closes. `respond?` fails closed when
the entries do not fit the wire model: such a message would encode to
an empty one and write a zero-length frame. -/

/-- Build one identify response from the host data. -/
def respond (key : Mock.Identity.PubKey) (addrs : List (List Nat))
    (protocols : List String) (observed : Option (List Nat)) (agent : String)
    (spr : Option (List Nat) := none) : Identify :=
  { protocolVersion := some Constants.identifyProtocolVersion,
    agentVersion := some agent,
    publicKey := some (marshalPubKey key),
    listenAddrs := addrs,
    observedAddr := observed,
    protocols := protocols,
    signedPeerRecord := spr }

/-- Build the response, and fail closed when its entries do not fit the
wire model. -/
def respond? (key : Mock.Identity.PubKey) (addrs : List (List Nat))
    (protocols : List String) (observed : Option (List Nat)) (agent : String)
    (spr : Option (List Nat) := none) : Except Error Identify :=
  let m := respond key addrs protocols observed agent spr
  if ∀ e ∈ m.entries, e.Valid then .ok m else .error .badAddress

/-! ## The client and the push handler

One pure frame step, `decodeFrame?`, serves both `clientCore` and the
IO reader, so the theorems on `clientCore` pin the decoder that the IO
path runs. -/

/-- The pure frame step over the accumulated bytes.

* `.ok (some (payload, rest))`: one whole frame with a nonempty
  payload; `rest` holds the bytes after it.
* `.ok none`: the buffer ends inside a frame; more bytes can complete
  it.
* `.error .emptyFrame`: a zero-length frame, the spike's rule.
* `.error (.badMessage (.framing .malformed))`: a bad prefix, a length
  over `Constants.identifyCap`, or a payload value of 256 or more.
  `Frame.decode?` checks the cap before it takes the body.

`clientCore` and `readFrameFrom` both call it. Only `readFrameFrom`
decides the end of the stream, and no theorem covers that decision. -/
private def decodeFrame? (bytes : List Nat) :
    Except Error (Option (List Nat × List Nat)) :=
  match Streams.Framing.Frame.decode? .uvarint Constants.identifyCap bytes with
  | .error .malformed => .error (.badMessage (.framing .malformed))
  | .error .truncated => .ok none
  | .ok (frame, rest) =>
      if frame.payload.isEmpty then .error .emptyFrame
      else .ok (some (frame.payload, rest))

/-- The pure half of the client: decode one frame under the cap, reject
the empty frame, and validate the payload bytes of that frame. The
caller supplies all the bytes at once, so a buffer that ends inside a
frame is the `.truncated` framing error. An empty buffer is also
`.truncated`, and the core never answers `.ok none`, while `client`
answers `.ok none` on a clean end. -/
def clientCore (bytes : List Nat) (expected : Option Mock.Identity.PeerId) :
    Except Error (Option (Identify × Mock.Identity.PeerId)) :=
  match decodeFrame? bytes with
  | .error e => .error e
  | .ok none => .error (.badMessage (.framing .truncated))
  | .ok (some (payload, _)) => some <$> validate payload expected

/-- One length-delimited frame from the stream. The `partial` reason is
in the module doc: a silent peer never ends the loop, and `client` or
`push` ends it through the deadline. -/
private partial def readFrameFrom (s : Streams.Stream) (buf : List Nat) :
    Conc.Async (Except Error (Option (List Nat))) := do
  match decodeFrame? buf with
  | .error e => return .error e
  | .ok (some (payload, _)) => return .ok (some payload)
  | .ok none =>
      match ← s.read with
      | .error e => return .error (.stream e)
      | .ok none =>
          if buf.isEmpty then return .ok none
          else return .error (.badMessage (.framing .truncated))
      | .ok (some chunk) => readFrameFrom s (buf ++ Bytes.toNatList chunk)

/-- One frame from the stream, over the private loop. -/
private def readFrame (s : Streams.Stream) :
    Conc.Async (Except Error (Option (List Nat))) :=
  readFrameFrom s []

/-- `withinDeadline` needs a `BaseIO` expiry. The stream's `close` is
the write half-close, so it does not wake a parked `read`. `reset` stops
both directions, so it wakes the read. The body starts the reset with
`asTask`, as `Conc.Wrap.spawn` does. Nothing joins this task and the
code ignores its result, an exception to §4.1 rule 2. -/
private def resetQuietly (s : Streams.Stream) : BaseIO Unit :=
  discard (s.reset.asTask.toBaseIO)

/-- Read one response under the cap and the deadline, then validate
it. `.ok none` means that the stream ended before any byte arrived. -/
def client (s : Streams.Stream) (clock : Conc.Clock) (timeoutMs : Nat)
    (expected : Option Mock.Identity.PeerId) :
    Conc.Async (Except Error (Option (Identify × Mock.Identity.PeerId))) := do
  match ← Conc.withinDeadline clock timeoutMs (resetQuietly s) (readFrame s) with
  | .error .deadlineExpired => return .error .timeout
  | .error .closed => return .error (.stream .closed)
  | .ok (.error e) => return .error e
  | .ok (.ok none) => return .ok none
  | .ok (.ok (some payload)) => return (some <$> validate payload expected)

/-- The one map from this protocol's error into the coarse core error.
`pushHandler` and `respondTo` call it at the seam. -/
def mapIdentifyError : Error → Mock.Core.Error
  | .stream e => Mock.Core.mapStreamError e
  | .timeout => .timeout "identify: the deadline expired"
  | .emptyFrame => .protocol "identify: a zero-length frame"
  | e => .protocol (toString (repr e))

/-- Handle one pushed message: validate it, then update the peerstore.
An empty read leaves the peerstore unchanged. This is a delta from go,
whose `consumeMessage` runs on the empty message and clears the peer's
protocols. -/
def push (store : Mock.Host.Peerstore) (expected : Mock.Identity.PeerId)
    (clock : Conc.Clock) (timeoutMs : Nat) (s : Streams.Stream) :
    Conc.Async (Except Error Unit) := do
  match ← Conc.withinDeadline clock timeoutMs (resetQuietly s) (readFrame s) with
  | .error .deadlineExpired => return .error .timeout
  | .error .closed => return .error (.stream .closed)
  | .ok (.error e) => return .error e
  | .ok (.ok none) => return .ok ()
  | .ok (.ok (some payload)) =>
      match validate payload (some expected) with
      | .error e => return .error e
      | .ok (m, pid) =>
          store.addAddrs pid m.listenAddrs
          return .ok ()

/-- The push handler value. -/
def pushHandler (store : Mock.Host.Peerstore) (expected : Mock.Identity.PeerId)
    (clock : Conc.Clock) (timeoutMs : Nat) : Mock.Core.StreamHandler :=
  { id := pushId,
    handle := fun s => ExceptT.mk ((Except.mapError mapIdentifyError) <$>
      push store expected clock timeoutMs s) }

/-- Write one length-delimited message and half-close. The
responder and the push sender share this body: both announce the same
record, and only the protocol id of the stream differs. -/
private def writeRecord (key : Mock.Identity.PubKey) (addrs : List (List Nat))
    (protocols : List String) (observed : Option (List Nat)) (agent : String)
    (spr : Option (List Nat)) (s : Streams.Stream) :
    Conc.Async (Except Mock.Core.Error Unit) := do
  match respond? key addrs protocols observed agent spr with
  | .error e => return .error (mapIdentifyError e)
  | .ok msg =>
      match Streams.Framing.encodeB? .uvarint Constants.identifyCap
          (Pb.encodeMessageB msg) with
      | none => return .error (.protocol "the identify response exceeds the cap")
      | some frame =>
          match ← s.write frame with
          | .error e => return .error (Mock.Core.mapStreamError e)
          | .ok () =>
              discard s.close
              return .ok ()

/-- The responder body. Write one length-delimited message and
half-close. -/
def respondTo (key : Mock.Identity.PubKey) (addrs : List (List Nat))
    (protocols : List String) (observed : Option (List Nat)) (agent : String)
    (spr : Option (List Nat) := none) (s : Streams.Stream) :
    Conc.Async (Except Mock.Core.Error Unit) :=
  writeRecord key addrs protocols observed agent spr s

/-- The push sender: announce this peer's record on the stream that the
host opened under `pushId`, then half-close.

The host owns the schedule. Go's identify service subscribes to
`EvtLocalAddressesUpdated` and `EvtLocalProtocolsUpdated` and pushes
one record per event (the spike's `vendor/go-libp2p/p2p/protocol/identify/id.go`,
the `loop` and `sendPushes` functions). This package sends one record
per call and starts no timer, so the host decides when the local record
changed. -/
def pushTo (key : Mock.Identity.PubKey) (addrs : List (List Nat))
    (protocols : List String) (observed : Option (List Nat)) (agent : String)
    (spr : Option (List Nat) := none) (s : Streams.Stream) :
    Conc.Async (Except Mock.Core.Error Unit) :=
  writeRecord key addrs protocols observed agent spr s

/-- The responder handler value. -/
def respondHandler (key : Mock.Identity.PubKey) (addrs : List (List Nat))
    (protocols : List String) (observed : Option (List Nat)) (agent : String)
    (spr : Option (List Nat) := none) : Mock.Core.StreamHandler :=
  { id := protocolId,
    handle := fun s => respondTo key addrs protocols observed agent spr s }

/-! ## The client-core theorems

`clientCoreFrame` pins the frame that `clientCore` validates.
`clientCoreOverCap` pins the cap check before the body.
`clientCoreEmptyFrame` pins the zero-length rule. Each consumes a law of
`Streams.Framing`, which inherits the axiom
`Streams.Mock.Varint.decodeEncodeSuffix`. None takes a result of this
package's mocks as a premise. -/

/-- The frame step reads a whole frame back from its encoding, with
any rest after it. -/
private theorem decodeFrame?Encode
    (f : Streams.Framing.Frame .uvarint Constants.identifyCap)
    (rest : List Nat) (h : 0 < f.payload.length) :
    decodeFrame? (Streams.Framing.Frame.encode f ++ rest) =
      .ok (some (f.payload, rest)) := by
  unfold decodeFrame?
  rw [Streams.Framing.Frame.decode?EncodeAppend f rest]
  have hne : f.payload ≠ [] := by intro hnil; rw [hnil] at h; simp at h
  simp [List.isEmpty_iff, hne]

/-- The client validates the payload bytes of the frame that it read. -/
theorem clientCoreFrame (f : Streams.Framing.Frame .uvarint Constants.identifyCap)
    (rest : List Nat) (expected : Option Mock.Identity.PeerId)
    (h : 0 < f.payload.length) :
    clientCore (Streams.Framing.Frame.encode f ++ rest) expected =
      some <$> validate f.payload expected := by
  unfold clientCore
  rw [decodeFrame?Encode f rest h]

/-- The frame step rejects a length over the cap before it reads the
body. -/
private theorem decodeFrame?OverCap (len : Nat) (rest : List Nat)
    (hlen : len ≤ Streams.Framing.Prefix.maxLen .uvarint)
    (hcap : Constants.identifyCap < len) :
    decodeFrame? (Streams.Framing.encodeLength .uvarint len ++ rest) =
      .error (.badMessage (.framing .malformed)) := by
  unfold decodeFrame?
  rw [Streams.Framing.Frame.decode?OverCap (p := .uvarint)
      (cap := Constants.identifyCap)
      (l := Streams.Framing.encodeLength .uvarint len ++ rest)
      (rest := rest) (len := len)
      (Streams.Framing.decodeLength?EncodeLength .uvarint len rest hlen) hcap]

/-- `clientCore` rejects a length over the cap before it reads the
body. The statement has no premise about the bytes after the prefix. -/
theorem clientCoreOverCap (len : Nat) (rest : List Nat)
    (expected : Option Mock.Identity.PeerId)
    (hlen : len ≤ Streams.Framing.Prefix.maxLen .uvarint)
    (hcap : Constants.identifyCap < len) :
    clientCore (Streams.Framing.encodeLength .uvarint len ++ rest) expected =
      .error (.badMessage (.framing .malformed)) := by
  unfold clientCore
  rw [decodeFrame?OverCap len rest hlen hcap]

/-- The zero-length rule on the frame step. -/
private theorem decodeFrame?EncodeLengthZero :
    decodeFrame? (Streams.Framing.encodeLength .uvarint 0) = .error .emptyFrame := by
  unfold decodeFrame? Streams.Framing.Frame.decode?
  have hd := Streams.Framing.decodeLength?EncodeLength .uvarint 0 [] (by simp)
  simp only [List.append_nil] at hd
  rw [hd]
  simp [Bytes.take?]

/-- The zero-length rule on `clientCore`, the spike's rule. -/
theorem clientCoreEmptyFrame (expected : Option Mock.Identity.PeerId) :
    clientCore (Streams.Framing.encodeLength .uvarint 0) expected =
      .error .emptyFrame := by
  unfold clientCore
  rw [decodeFrame?EncodeLengthZero]

end Identify

end Libp2p.Protocols
