import Std.Data.HashMap
import Libp2p.Identity
import Libp2p.Host.Mock.Core

/-!
# The session and handler registries

The host keeps the shared state that remains after the loops of §3.3
own their sessions (ARCHITECTURE §3.8). This module holds two of the
three registries; the peerstore has its own module. Each registry is a
`Std.HashMap` that the host keeps inside an `OnceRef`, and only a pure
update function, applied under `OnceRef.update` or
`OnceRef.updateGet`, changes it (the package ARCHITECTURE, contract 1;
PRINCIPLES 3.3). The functions here are data in, data out, so a test
runs them with no cell and no task.

## The session table

One entry per peer: the session the host serves that peer through.
The entry records what the dedup rule (`Libp2p.Host.Dedup`) reads, so
the rule runs inside one update with no probe before it (§3.8):

* `role`, our side of the connection, which says who dialed it;
* `bornMs`, the host clock when the entry was committed;
* `live`, the liveness field. The loop of a session clears it on exit,
  through `markDead` (contract 3).

The session handle is a type parameter, `α`. The host stores its
running session there, and a test stores a plain value, so the table
functions need no connection.

Each entry carries a session number, `id`, that the host draws once
per session. `markDead` matches it, so the exit of a session that dedup
already replaced cannot mark its successor dead.

## The handler table

`Std.HashMap ProtocolId StreamHandler`, keyed by the id each handler
carries (§3.10; contract 5). The ids, in their `Ord` order, are what
the host's stream negotiation answers from.
-/

set_option autoImplicit false

namespace Libp2p.Host

open Libp2p.Identity Libp2p.Host.Mock.Core

/-! ## The session table -/

/-- The entry of one peer in the session table. -/
structure Entry (α : Type) where
  /-- The session number. The host draws a fresh one for each session,
  so two sessions of one peer never share it. -/
  id : Nat
  /-- Our side of the connection: `.initiator` when we dialed it. -/
  role : Role
  /-- The host clock, in milliseconds, when the entry was committed. -/
  bornMs : Nat
  /-- False once the loop of the session has exited (contract 3). -/
  live : Bool
  /-- The session handle. -/
  session : α

/-- The session table: the entry of each peer the host holds a session
with. A synonym with no invariant of its own (§3.7). -/
abbrev SessionTable (α : Type) := Std.HashMap PeerId (Entry α)

namespace SessionTable

variable {α : Type}

/-- The live entry of `peer`. `none` when the table holds no entry for
the peer, or holds a dead one. -/
def live? (t : SessionTable α) (peer : PeerId) : Option (Entry α) :=
  (t.get? peer).filter (·.live)

/-- Mark the session `id` of `peer` dead. The loop of the session
calls it on exit, through the cell's update (contract 3). The entry
stays, so the next dedup decision reads it as dead. An entry with
another number belongs to a later session, and the call leaves it
alone. -/
def markDead (peer : PeerId) (id : Nat) (t : SessionTable α) : SessionTable α :=
  match t.get? peer with
  | some e => if e.id = id then t.insert peer { e with live := false } else t
  | none => t

/-- The live entries, for the shutdown sequence: the host closes each
session it still serves (§5.5). -/
def liveEntries (t : SessionTable α) : List (PeerId × Entry α) :=
  t.toList.filter (·.2.live)

end SessionTable

/-! ## The handler table -/

/-- The handler table: the handler of each protocol id (§3.10). -/
abbrev Handlers := Std.HashMap ProtocolId StreamHandler

namespace Handlers

/-- Store `h` under its id. A handler already stored under the id is
replaced. -/
def set (h : StreamHandler) (t : Handlers) : Handlers :=
  t.insert h.id h

/-- The handler of `id`. `none` when no handler serves the id. -/
def find? (t : Handlers) (id : ProtocolId) : Option StreamHandler :=
  t.get? id

/-- The ids the table serves, in `ProtocolId` order. The order is the
text order of the ids (`ProtocolId`'s derived `Ord`), so the stream
negotiation and an `ls` answer do not depend on the hash order. -/
def ids (t : Handlers) : List ProtocolId :=
  (t.toList.map (·.1)).mergeSort (fun a b => compare a b != .gt)

end Handlers

end Libp2p.Host
