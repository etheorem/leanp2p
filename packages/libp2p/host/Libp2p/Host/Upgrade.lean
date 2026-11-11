import Conc
import Streams
import Libp2p.Identity
import Libp2p.Core
import Libp2p.Negotiate
import Libp2p.Host.Error

/-!
# The host's upgrade

The upgrade of one connection, with the peer checkpoints in the place
the core seam fixes: `ConnectionGater.allowSecured` runs after the
handshake and before the muxer stage (`Libp2p/Core/Policy.lean`), as
go-libp2p's upgrader calls `InterceptSecured`
(`vendor/go-libp2p/p2p/net/upgrader/upgrader.go`, line 176).

`Negotiate.upgradeWith` runs the same stages with no checkpoint. The
host composes the stages from the public functions of
`libp2p/negotiate` instead: `negotiate` for the security and the muxer
stages, `checkIdentity`, and `settleUpgrade`. The stage order follows
`Negotiate.upgradeCore`. A change to the order in one module needs the
same change in the other.

The whole upgrade runs under one `Conc.withinDeadline` of
`Streams.unauthDeadlineMs` (root §5, invariant 4). A refusal at a
checkpoint is an answer, and no failure: the caller maps it to
`Host.Error.gated`.
-/

set_option autoImplicit false

namespace Libp2p.Host

open Conc Streams Libp2p.Identity Libp2p.Core

/-- An upgraded connection: the muxer session and the peer the
handshake proved. The session's `join` also waits for the secure
connection under it, so `Upgraded.join` is the join of both. -/
structure Upgraded where
  /-- The muxer session. -/
  session : MuxSession
  /-- The peer the handshake proved. -/
  remotePeer : PeerId

/-- Wait for the session and the secure connection under it. -/
def Upgraded.join (u : Upgraded) : ExceptT Core.Error Async Unit :=
  u.session.join

/-- The answer of an upgrade that ran to its end: a session, or the
checkpoint that refused the proved peer. -/
inductive Admission where
  | upgraded (u : Upgraded)
  | refused (at_ : Checkpoint)

/-- Close a secure connection and wait for its tasks. The function
drops the answer of the join, because the caller already holds the
answer it reports. -/
private def discardSecure (sc : SecureConn) : Async Unit := do
  sc.toConnection.closeQuietly
  discard sc.join.run

/-- The session `s`, with a `join` that also waits for the secure
connection under it. The join waits for the secure connection even
when the session's join throws a fault, so none of its tasks outlives
the join (PRINCIPLES 3.2). The first failure wins. -/
private def ownSecure (s : MuxSession) (sc : SecureConn) : MuxSession :=
  { s with
    join := ExceptT.mk do
      let a : Except IO.Error (Except Core.Error Unit) ←
        try pure (.ok (← s.join.run)) catch e => pure (.error e)
      let b ← sc.join.run
      match a with
      | .error e => throw e
      | .ok a => return a.bind fun () => b }

/-- The stages: negotiate the security protocol, run the handshake,
check the identity, ask `admit` about the proved peer, negotiate the
muxer, open the session on `clock`. A failure or a refusal after the
handshake closes and joins the secure connection. -/
private def stages (clock : Clock) (role : Role) (conn : Connection) (expected : Option PeerId)
    (admit : PeerId → BaseIO (Option Checkpoint))
    (secs : List SecurityProtocol) (muxers : List Muxer) :
    Async (Except Core.Error Admission) := do
  match ← (Negotiate.negotiate role (BufReader.new conn) conn .empty (secs.map (·.id))).run with
  | .error e => return .error e
  | .ok stage =>
    let some sec := secs.find? (fun s => decide (s.id = stage.proto))
      | return .error (.protocol "selected security protocol is not configured")
    match ← (sec.handshake role conn stage.leftover).run with
    | .error e => return .error e
    | .ok sc =>
      if let .error e := Negotiate.checkIdentity expected sc.remotePeer then
        discardSecure sc
        return .error e
      -- The checkpoint: the handshake proved the peer, and no muxer
      -- byte moves before this point.
      if let some c ← admit sc.remotePeer then
        discardSecure sc
        return .ok (.refused c)
      -- The secure `read` delivers the handshake's leftover, so the
      -- muxer stage starts with no bytes.
      let secure := sc.toConnection
      match ← (Negotiate.negotiate role (BufReader.new secure) secure .empty
          (muxers.map (·.id))).run with
      | .error e => discardSecure sc; return .error e
      | .ok stage2 =>
        let some mux := muxers.find? (fun m => decide (m.id = stage2.proto))
          | discardSecure sc
            return .error (.protocol "selected muxer is not configured")
        match ← (mux.«open» role secure stage2.leftover clock).run with
        | .error e => discardSecure sc; return .error e
        | .ok session =>
          return .ok (.upgraded { session := ownSecure session sc, remotePeer := sc.remotePeer })

/-- Close a session that finished after the timer won, and give its
join to `late`, the task set `upgrade` joins. No caller receives that
session. -/
private def releaseLate (late : TaskSet) : Except Core.Error Admission → BaseIO Unit
  | .ok (.upgraded u) => do
    discard u.session.close.toBaseIO
    late.spawn (discard u.join.run)
  | _ => pure ()

/-- The upgrade of `conn` under the deadline, on `clock`. The expiry
closes the connection once, at the boundary. `Negotiate.settleUpgrade`
maps the expiry to the `timeout` arm. On a failure inside the stages,
this function closes the connection. -/
def upgrade (clock : Clock) (role : Role) (conn : Connection) (expected : Option PeerId)
    (admit : PeerId → BaseIO (Option Checkpoint))
    (secs : List SecurityProtocol) (muxers : List Muxer) :
    ExceptT Core.Error Async Admission := do
  let late ← TaskSet.new
  let answer ← withinDeadline clock Streams.unauthDeadlineMs conn.closeQuietly
    (stages clock role conn expected admit secs muxers) (releaseLate late)
  late.joinAll
  match Negotiate.settleUpgrade answer with
  | .ok a => return a
  | .error e =>
    -- An error from the boundary means the expiry hook closed the
    -- connection. A failure inside the work leaves it open.
    if answer matches .ok _ then conn.closeQuietly
    throw e

end Libp2p.Host
