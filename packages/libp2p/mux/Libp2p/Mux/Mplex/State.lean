import Std.Data.HashMap
import Libp2p.Mux.Mplex.Wire

/-!
# The mplex stream table

The pure state of one mplex session: the live streams, keyed by
`(id, initiator)`, and the counter of the local ids. The shell in
`Mplex/Session.lean` holds the table in one `OnceRef` and changes it
only through the transitions below, each one atomic step.

## The identity rule

Both sides number the streams they open from zero (go-mplex,
`nextChanID`). An id alone therefore names no stream. The spec,
"Opening a new stream": "Both parties can open a substream with the
same ID, therefore this distinction is used to identify whether each
message concerns the channel opened locally or remotely." So a `Key`
holds the id and the side that opened the stream. `classify` reads the
flag of an inbound message and names the key it concerns:

* `NewStream` and the `*Initiator` flags come from the side that
  opened the stream, the peer. They concern a key with
  `initiator = false`.
* The `*Receiver` flags come from the receiver of the stream. The
  receiver is the peer, so the local side opened the stream. They
  concern a key with `initiator = true`.

The connection role plays no part here. A dialer and a listener each
number their own streams from zero.

## Half-close

The spec, "Closing a stream": a close "closes it for writing and
closes the remote end for reading but allows writing in the other
direction". `Halves` holds the two directions apart. A local close
ends the local write direction only. A remote close ends the remote
write direction only. The table retires a stream when both directions
have ended, or at once on a reset in either direction.

`σ` is the type of the runtime port of a stream, so the table stays
pure, and a test can use any type.
-/

set_option autoImplicit false

namespace Libp2p.Mux.Mplex.State

open Libp2p.Mux.Mplex.Wire

/-- The live streams one session holds at one time, both sides
together. An inbound open over the cap gets a reset, and a local open
over the cap is refused. go-mplex sets no such cap. -/
def liveStreamCap : Nat := 1024

/-! ## Keys and routing -/

/-- The identity of a stream: its id, and whether the local side
opened it. -/
structure Key where
  /-- The stream id on the wire. -/
  id : Nat
  /-- `true` when the local side opened the stream. -/
  initiator : Bool
  deriving DecidableEq, Hashable, Repr

/-- The key the peer holds for the same stream: the same id, seen from
the other side. -/
def Key.mirror (k : Key) : Key := { k with initiator := !k.initiator }

/-- What an inbound message asks of the session. -/
inductive Inbound where
  /-- The peer opened a stream. -/
  | open (key : Key)
  /-- Data for a stream. -/
  | data (key : Key)
  /-- The peer closed its write direction. -/
  | close (key : Key)
  /-- The peer reset the stream. -/
  | reset (key : Key)
  deriving DecidableEq, Repr

/-- The key and the request of an inbound message (module doc, "The
identity rule"). -/
def classify (flag : Flag) (id : Nat) : Inbound :=
  match flag with
  | .newStream => .open ⟨id, false⟩
  | .messageReceiver => .data ⟨id, true⟩
  | .messageInitiator => .data ⟨id, false⟩
  | .closeReceiver => .close ⟨id, true⟩
  | .closeInitiator => .close ⟨id, false⟩
  | .resetReceiver => .reset ⟨id, true⟩
  | .resetInitiator => .reset ⟨id, false⟩

/-- The flag of outbound data on the stream `k`. -/
def dataFlag (k : Key) : Flag := if k.initiator then .messageInitiator else .messageReceiver

/-- The flag of an outbound close on the stream `k`. -/
def closeFlag (k : Key) : Flag := if k.initiator then .closeInitiator else .closeReceiver

/-- The flag of an outbound reset on the stream `k`. -/
def resetFlag (k : Key) : Flag := if k.initiator then .resetInitiator else .resetReceiver

/-- The peer routes our data on `k` to its own key for the stream, the
mirror of `k`. -/
theorem classifyData (k : Key) : classify (dataFlag k) k.id = .data k.mirror := by
  cases k with
  | mk id initiator => cases initiator <;> rfl

/-- The peer routes our close on `k` to the mirror of `k`. -/
theorem classifyClose (k : Key) : classify (closeFlag k) k.id = .close k.mirror := by
  cases k with
  | mk id initiator => cases initiator <;> rfl

/-- The peer routes our reset on `k` to the mirror of `k`. -/
theorem classifyReset (k : Key) : classify (resetFlag k) k.id = .reset k.mirror := by
  cases k with
  | mk id initiator => cases initiator <;> rfl

/-- The peer files our open of id `n` under the key it holds as the
receiver. -/
theorem classifyOpen (n : Nat) : classify .newStream n = .open (Key.mirror ⟨n, true⟩) := rfl

/-- Two streams with the same id and opposite initiators are two keys:
no message for one reaches the other. -/
theorem mirrorNe (k : Key) : k.mirror ≠ k := by
  cases k with
  | mk id initiator => cases initiator <;> simp [Key.mirror]

/-! ## The two directions -/

/-- The open directions of one live stream. -/
structure Halves where
  /-- The local write direction is open. -/
  localOpen : Bool
  /-- The peer's write direction is open. -/
  remoteOpen : Bool
  deriving DecidableEq, Repr

namespace Halves

/-- A new stream: both directions open. -/
def fresh : Halves := { localOpen := true, remoteOpen := true }

/-- Both directions have ended. The table retires the stream. -/
def done (h : Halves) : Bool := !h.localOpen && !h.remoteOpen

/-- End the local write direction. -/
def closeLocal (h : Halves) : Halves := { h with localOpen := false }

/-- End the peer's write direction. -/
def closeRemote (h : Halves) : Halves := { h with remoteOpen := false }

/-- A local close leaves the peer's direction as it was: the response
after our FIN still arrives. -/
theorem closeLocalRemote (h : Halves) : h.closeLocal.remoteOpen = h.remoteOpen := rfl

/-- A remote close leaves the local direction as it was: we can still
write after the peer's FIN. -/
theorem closeRemoteLocal (h : Halves) : h.closeRemote.localOpen = h.localOpen := rfl

/-- One close leaves a fresh stream live. -/
theorem freshCloseNotDone : fresh.closeLocal.done = false ∧ fresh.closeRemote.done = false :=
  ⟨rfl, rfl⟩

/-- Two closes end a stream, in either order. -/
theorem closeBothDone (h : Halves) :
    h.closeLocal.closeRemote.done = true ∧ h.closeRemote.closeLocal.done = true :=
  ⟨rfl, rfl⟩

end Halves

/-! ## The table -/

/-- One live stream: its port and its open directions. -/
structure Entry (σ : Type) where
  /-- The runtime port of the stream. -/
  port : σ
  /-- The open directions. -/
  halves : Halves

/-- The state of one session. -/
structure Table (σ : Type) where
  /-- The live streams. -/
  entries : Std.HashMap Key (Entry σ)
  /-- The id of the next local open. -/
  nextId : Nat
  /-- The session has ended. No stream opens. -/
  ended : Bool

/-- The answer to an inbound open. -/
inductive OpenAnswer where
  /-- The table took the stream. -/
  | accepted
  /-- The key is live already. go-mplex ends the session on this
  (`ErrInvalidState`), and so does this session. -/
  | duplicate
  /-- The table is full. The session resets the stream. -/
  | full
  /-- The session has ended. -/
  | ended
  deriving DecidableEq, Repr

namespace Table

variable {σ : Type}

/-- An empty table for a new session. -/
def empty : Table σ := { entries := {}, nextId := 0, ended := false }

/-- The live streams. -/
def size (t : Table σ) : Nat := t.entries.size

/-- Open a local stream with `port`. `none` when the session has ended,
the table is full, or the ids have run out. -/
def openLocal (port : σ) (t : Table σ) : Option Key × Table σ :=
  if t.ended || liveStreamCap ≤ t.size || idLimit ≤ t.nextId then (none, t)
  else
    let key : Key := ⟨t.nextId, true⟩
    (some key, { t with
      entries := t.entries.insert key { port, halves := .fresh }
      nextId := t.nextId + 1 })

/-- Take a stream the peer opened with id `id`. -/
def openRemote (id : Nat) (port : σ) (t : Table σ) : OpenAnswer × Table σ :=
  let key : Key := ⟨id, false⟩
  if t.ended then (.ended, t)
  else if t.entries.contains key then (.duplicate, t)
  else if liveStreamCap ≤ t.size then (.full, t)
  else (.accepted, { t with entries := t.entries.insert key { port, halves := .fresh } })

/-- Forget a stream whose open failed to reach the wire. -/
def forget (key : Key) (t : Table σ) : Table σ :=
  { t with entries := t.entries.erase key }

/-- The port that takes inbound data for `key`: a live stream whose
peer direction is open. Data for any other key is dropped, as go-mplex
drops it. -/
def dataPort? (key : Key) (t : Table σ) : Option σ :=
  match t.entries.get? key with
  | some e => if e.halves.remoteOpen then some e.port else none
  | none => none

/-- Set the halves of a live stream, and retire it when both
directions have ended. -/
private def store (key : Key) (e : Entry σ) (h : Halves) (t : Table σ) : Table σ :=
  if h.done then { t with entries := t.entries.erase key }
  else { t with entries := t.entries.insert key { e with halves := h } }

/-- The peer closed its write direction on `key`. The port is returned
once, the first time, so the shell ends its inbox once. -/
def closeRemote (key : Key) (t : Table σ) : Option σ × Table σ :=
  match t.entries.get? key with
  | some e =>
    if e.halves.remoteOpen then (some e.port, store key e e.halves.closeRemote t)
    else (none, t)
  | none => (none, t)

/-- The peer reset `key`. The stream retires at once. -/
def resetRemote (key : Key) (t : Table σ) : Option σ × Table σ :=
  match t.entries.get? key with
  | some e => (some e.port, { t with entries := t.entries.erase key })
  | none => (none, t)

/-- The local write direction of `key` is open. -/
def writable (key : Key) (t : Table σ) : Bool :=
  match t.entries.get? key with
  | some e => e.halves.localOpen
  | none => false

/-- End the local write direction of `key`. `true` when a close
message is due: the stream was live, and its local direction open. -/
def closeLocal (key : Key) (t : Table σ) : Bool × Table σ :=
  match t.entries.get? key with
  | some e =>
    if e.halves.localOpen then (true, store key e e.halves.closeLocal t)
    else (false, t)
  | none => (false, t)

/-- Reset `key` locally. `true` when a reset message is due: the
stream was live. The stream retires at once. -/
def resetLocal (key : Key) (t : Table σ) : Bool × Table σ :=
  if t.entries.contains key then (true, { t with entries := t.entries.erase key })
  else (false, t)

/-- End the session: every live stream leaves the table, with its
halves, and no stream opens after. -/
def endAll (t : Table σ) : List (Key × Entry σ) × Table σ :=
  (t.entries.toList, { t with entries := {}, ended := true })

end Table

end Libp2p.Mux.Mplex.State
