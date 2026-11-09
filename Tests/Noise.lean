import Tests.Support
import Bytes
import Proto
import Streams
import Libp2p.Core
import Libp2p.Security

/-!
# Noise suite (unit W5.3, 1a)

The unit 1a milestones of `packages/libp2p/security/docs/PLAN.md`,
"Test milestones (unit 1a)":

* The four flynn XX cases of `noise-vectors.json` replay through the
  core in both roles, as events in and actions out: three handshake
  messages, then two transport messages under the cipher states of
  `split`.
* The go transcript of `noise-go-transcript.json` replays the
  responder: message 2 is byte-exact, message 3 decrypts and its
  payload verifies to the captured peer id, and the derived cipher
  states round-trip the recorded transport frames.
* The 8 KiB gate refuses a payload one byte over before the decode.
* The static-key check: a signature over another static key, a
  changed signature, and a missing signature fail; a good payload
  gives the peer id of its identity key.

Beyond the milestones: a libp2p handshake between two cores, with
Ed25519 identities on both sides, and the hostile cases (a changed
ciphertext, a short message, a long message, a message out of turn, an
input twice, an event after the completion).

The unit 1b milestones, "Test milestones (unit 1b)", run the seam
values over the in-memory sim:

* The handshake completes in both roles, with and without split writes,
  and each side proves the other's peer id.
* A bit-flipped transport frame is a protocol error: the reader sees the
  end after the teardown, and the join answers `protocol`. A clean close
  reads the end, and the join answers `.ok`.
* A write over `maxPlaintext` goes out as frames at the cap, and the
  peer reads it back whole.
* The fixed-key value gives the same bytes on the wire in two runs.
* The leftover in both directions: message 0 reaches the responder
  through the `ByteArray` argument, and a transport frame that the
  handshake over-read reaches the reader through the `SecureConn`.

Beyond the milestones: a payload signed over another static key fails
the initiator with `authentication` before message 2 goes out, an end
inside the handshake is `closed`, an end inside a transport frame is
`truncatedFrame`, and a cipher state at the reserved nonce fails the
step (owned contract 6).
-/

set_option autoImplicit false

namespace Tests

open Bytes Libp2p.Identity Libp2p.Security

/-- 32 bytes from hex. -/
private def key32 (where_ hex : String) : IO Noise.Bytes32 := do
  match Noise.Bytes32.ofByteArray? (← unhex where_ hex) with
  | some k => pure k
  | none => throw <| IO.userError s!"{where_}: not 32 bytes: {hex}"

/-- A value of an `Except`, or a failed run that names the error. -/
private def expectOk {ε α : Type} [Repr ε] (where_ : String) : Except ε α → IO α
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"{where_}: {repr e}"

/-- The X25519 public key of a private key. -/
private def x25519Pub (where_ : String) (k : Noise.Bytes32) : IO Noise.Bytes32 := do
  let p ← expectOk where_ (Crypto.x25519PublicKey k.key)
  pure ⟨p⟩

/-- A Noise message with its 2-byte length prefix. -/
private def frame (b : ByteArray) : ByteArray :=
  (Streams.Framing.encodeB? .u16be Noise.maxMessage b).getD .empty

/-- The message inside a framed write: the bytes after the 2-byte
prefix, as the shell's framed read hands them to the peer's core. -/
private def body (f : Bytes.Blob) : Bytes.Blob := ⟨f.bytes.extract 2 f.bytes.size⟩

/-- Post the events in order, and gather the actions. -/
private def stepAll (st : Noise.State) (evs : List Noise.Event) :
    Except Noise.Error (Noise.State × List Noise.Action) :=
  evs.foldlM (init := (st, [])) fun (st, acts) ev => do
    let (st, a) ← Noise.step st ev
    return (st, acts ++ a)

/-- The input with the bit 0 of byte `i` flipped. -/
private def flip (b : ByteArray) (i : Nat) : ByteArray :=
  if h : i < b.size then b.set i (b[i] ^^^ 1) h else b

/-- `n` bytes of value `v`. -/
private def fill (n : Nat) (v : UInt8) : ByteArray := ⟨Array.replicate n v⟩

/-! ## The flynn vectors -/

/-- One flynn case: both roles, three handshake messages, then the two
transport messages. flynn's runner sends the first transport message
with the initiator's cipher state and the second with the
responder's (`vendor/flynn-noise/vector_test.go`). -/
private def flynnCase (r : Runner) (c : Lean.Json) : IO Unit := do
  let file := "noise-vectors.json"
  let note ← jStr file c "note"
  let name := s!"flynn {note}"
  let prologue ← unhex file (← jStr file c "prologue")
  let iS ← key32 file (← jStr file c "initStatic")
  let rS ← key32 file (← jStr file c "respStatic")
  let iE ← key32 file (← jStr file c "initEphemeral")
  let rE ← key32 file (← jStr file c "respEphemeral")
  let mut ps : Array ByteArray := #[]
  let mut cts : Array ByteArray := #[]
  for m in ← jArr file c "messages" do
    ps := ps.push (← unhex file (← jStr file m "payload"))
    cts := cts.push (← unhex file (← jStr file m "ciphertext"))
  unless ps.size = 5 do
    r.check s!"{name}: five messages" false
    return
  -- `ps` and `cts` grow together, so both hold five entries, and every
  -- index below is in range.
  let i0 ← expectOk name (Noise.State.init .initiator prologue iS)
  let r0 ← expectOk name (Noise.State.init .responder prologue rS)
  -- Message 0, initiator to responder: `e`. The vector holds the
  -- message; the write action holds it framed.
  let (i1, a) ← expectOk name (stepAll i0 [.entropy iE, .«local» ⟨ps[0]!⟩])
  r.check s!"{name}: the initiator writes message 0" (a == [.write ⟨frame cts[0]!⟩])
  -- Message 1, responder to initiator: `e, ee, s, es`.
  let (r1, a) ← expectOk name
    (stepAll r0 [.entropy rE, .«local» ⟨ps[1]!⟩, .bytes ⟨cts[0]!⟩])
  r.check s!"{name}: the responder reads message 0 and writes message 1"
    (a == [.payload ⟨ps[0]!⟩ none, .write ⟨frame cts[1]!⟩])
  -- Message 2, initiator to responder: `s, se`, then `split`.
  let (_, a) ← expectOk name (stepAll i1 [.«local» ⟨ps[2]!⟩, .bytes ⟨cts[1]!⟩])
  let [.payload q1 k1, .write f2, .complete ci] := a
    | r.check s!"{name}: the initiator reads message 1, writes message 2, and completes" false
  r.check s!"{name}: the initiator reads payload 1" (q1 == ⟨ps[1]!⟩)
  r.check s!"{name}: payload 1 carries the responder's static key, ahead of the write"
    (k1 == some (← x25519Pub name rS))
  r.check s!"{name}: the initiator writes message 2" (f2 == ⟨frame cts[2]!⟩)
  let (_, a) ← expectOk name (stepAll r1 [.bytes ⟨cts[2]!⟩])
  let [.payload q2 k2, .complete cr] := a
    | r.check s!"{name}: the responder reads message 2 and completes" false
  r.check s!"{name}: the responder reads payload 2" (q2 == ⟨ps[2]!⟩)
  r.check s!"{name}: payload 2 carries the initiator's static key"
    (k2 == some (← x25519Pub name iS))
  r.check s!"{name}: the cipher states pair up" (ci.send == cr.recv && ci.recv == cr.send)
  r.check s!"{name}: the initiator learned the responder's static key"
    (ci.remoteStatic == (← x25519Pub name rS))
  r.check s!"{name}: the responder learned the initiator's static key"
    (cr.remoteStatic == (← x25519Pub name iS))
  -- The transport messages carry an empty associated data.
  let (_, ct3) ← expectOk name (ci.send.encryptWithAd .empty ps[3]!)
  r.check s!"{name}: transport message 0 under the initiator's state" (ct3 == cts[3]!)
  let (_, pt3) ← expectOk name (cr.recv.decryptWithAd .empty cts[3]!)
  r.check s!"{name}: the responder opens transport message 0" (pt3 == ps[3]!)
  let (_, ct4) ← expectOk name (cr.send.encryptWithAd .empty ps[4]!)
  r.check s!"{name}: transport message 1 under the responder's state" (ct4 == cts[4]!)
  let (_, pt4) ← expectOk name (ci.recv.decryptWithAd .empty cts[4]!)
  r.check s!"{name}: the initiator opens transport message 1" (pt4 == ps[4]!)

private def flynn (r : Runner) : IO Unit := do
  let file := "noise-vectors.json"
  let j ← loadJson file
  let cases ← jArr file j "cases"
  r.check "flynn: four cases" (cases.length == 4)
  for c in cases do
    try flynnCase r c
    catch e => r.check s!"flynn case: runs ({e})" false

/-! ## The go transcript -/

/-- The responder against go-libp2p v0.50.0 as initiator. -/
private def goTranscriptRun (r : Runner) : IO Unit := do
  let file := "noise-go-transcript.json"
  let name := "go transcript"
  let j ← loadJson file
  let rS ← key32 file (← jStr file j "respStaticNoiseHex")
  let rE ← key32 file (← jStr file j "respEphemeralPrivHex")
  let rPayload ← unhex file (← jStr file j "respPayloadHex")
  let iPayload ← unhex file (← jStr file j "initPayloadHex")
  let mut msgs : Array (String × ByteArray) := #[]
  for m in ← jArr file j "messages" do
    msgs := msgs.push (← jStr file m "dir", ← unhex file (← jStr file m "hex"))
  -- The indexes below read the three handshake messages.
  unless 3 ≤ msgs.size do
    r.check s!"{name}: three handshake messages" false
    return
  r.check s!"{name}: the ephemeral private key gives the captured public key"
    ((← x25519Pub name rE).bytes == (← unhex file (← jStr file j "respEphemeralNoiseHex")))
  -- The captured messages carry their prefix; the core takes them
  -- without it, as the shell's framed read hands them on.
  let st ← expectOk name (Noise.State.init .responder .empty rS)
  let (st, a) ← expectOk name
    (stepAll st [.entropy rE, .«local» ⟨rPayload⟩, .bytes (body ⟨msgs[0]!.2⟩)])
  r.check s!"{name}: message 1 carries an empty payload, and message 2 is byte-exact"
    (a == [.payload ⟨.empty⟩ none, .write ⟨msgs[1]!.2⟩])
  let (_, a) ← expectOk name (stepAll st [.bytes (body ⟨msgs[2]!.2⟩)])
  let [.payload q (some k), .complete c] := a
    | r.check s!"{name}: the responder reads message 3 with the static key, and completes" false
  r.check s!"{name}: message 3 decrypts to the captured payload" (q == ⟨iPayload⟩)
  r.check s!"{name}: the payload's key is the completion's key" (k == c.remoteStatic)
  -- The payload checks, both directions. The shell checks with the key
  -- of the payload action.
  let v ← expectOk name (Noise.verify k iPayload)
  r.check s!"{name}: the initiator payload verifies to the captured peer id"
    (v.peer.toString == (← jStr file j "initPeerId"))
  r.check s!"{name}: the initiator's identity key is the captured key"
    (v.key.data == (← unhex file (← jStr file j "initIdentityPubHex")))
  let vr ← expectOk name (Noise.verify (← x25519Pub name rS) rPayload)
  r.check s!"{name}: the responder payload verifies to the captured peer id"
    (vr.peer.toString == (← jStr file j "respPeerId"))
  r.check s!"{name}: the responder payload keeps its extensions as bytes" vr.extensions.isSome
  -- The transport frames: open each one, then seal the plaintext again
  -- with a copy of the state from before the open. The copy must give
  -- the recorded bytes back.
  let mut recv := c.recv
  let mut send := c.send
  for (dir, wire) in msgs.toList.drop 3 do
    let body := wire.extract 2 wire.size
    let label := s!"{name}: transport frame {dir} {toHex (wire.extract 0 4)}… round-trips"
    match dir with
    | "i2r" =>
      let (next, pt) ← expectOk name (recv.decryptWithAd .empty body)
      let (_, again) ← expectOk name (recv.encryptWithAd .empty pt)
      recv := next
      r.check label (again == body)
    | _ =>
      let (_, pt) ← expectOk name (send.decryptWithAd .empty body)
      let (next, again) ← expectOk name (send.encryptWithAd .empty pt)
      send := next
      r.check label (again == body)

private def goTranscript (r : Runner) : IO Unit := do
  try goTranscriptRun r
  catch e => r.check s!"go transcript: runs ({e})" false

/-! ## The payload check -/

/-- An Ed25519 identity from a fill byte. -/
private def identity (where_ : String) (v : UInt8) : IO PrivKey :=
  expectOk where_ (PrivKey.ofData? .ed25519 (fill 32 v))

/-- The payload of the identity over the static key. -/
private def payloadOf (where_ : String) (k : PrivKey) (staticPub : Noise.Bytes32) :
    IO ByteArray := do
  expectOk where_ (← (Noise.build k staticPub).run)

private def payloadChecksRun (r : Runner) : IO Unit := do
  let name := "payload"
  let k ← identity name 7
  let peer ← expectOk name (do PeerId.ofPubKey (← k.toPublic))
  let sA ← x25519Pub name (← key32 name (toHex (fill 32 1)))
  let sB ← x25519Pub name (← key32 name (toHex (fill 32 2)))
  let p ← payloadOf name k sA
  r.check s!"{name}: a good payload gives the peer id of its key"
    (match Noise.verify sA p with | .ok v => v.peer == peer | .error _ => false)
  r.check s!"{name}: a good payload carries no extensions"
    (match Noise.verify sA p with | .ok v => v.extensions.isNone | .error _ => false)
  r.check s!"{name}: a signature over another static key fails"
    (failsWith .badSignature (Noise.verify sB p))
  -- The signature is the last field, so the last byte is a signature
  -- byte.
  r.check s!"{name}: a changed signature fails"
    (failsWith .badSignature (Noise.verify sA (flip p (p.size - 1))))
  let pub ← expectOk name k.toPublic
  let some kf := Noise.Field.ofByteArray? pub.marshal
    | r.check s!"{name}: the key fits a field" false
  let noSig := Pb.encodeMessageB
    ({ identityKey := some kf, identitySig := none, extensions := none } : Noise.HandshakePayload)
  r.check s!"{name}: a payload with no signature fails"
    (failsWith .missingIdentity (Noise.verify sA noSig))
  r.check s!"{name}: an empty payload fails" (failsWith .missingIdentity (Noise.verify sA .empty))
  -- The gate: one byte over is refused before the decode. At the cap
  -- the decode runs, and the zero tag is a protobuf error.
  let over := Noise.maxPayload + 1
  r.check s!"{name}: {over} bytes are refused before the decode"
    (failsWith (.payloadTooLarge over) (Noise.verify sA (fill over 0)))
  r.check s!"{name}: {Noise.maxPayload} bytes reach the decode"
    (failsWith (.payload .badField) (Noise.verify sA (fill Noise.maxPayload 0)))

private def payloadChecks (r : Runner) : IO Unit := do
  try payloadChecksRun r
  catch e => r.check s!"payload: runs ({e})" false

/-! ## A libp2p handshake between two cores -/

/-- Both roles with Ed25519 identities, each side checking the other's
payload as the shell does, before its next action. -/
private def libp2pRun (r : Runner) : IO Unit := do
  let name := "libp2p handshake"
  let kI ← identity name 3
  let kR ← identity name 4
  let peerI ← expectOk name (do PeerId.ofPubKey (← kI.toPublic))
  let peerR ← expectOk name (do PeerId.ofPubKey (← kR.toPublic))
  let sI ← key32 name (toHex (fill 32 5))
  let sR ← key32 name (toHex (fill 32 6))
  let pI ← payloadOf name kI (← x25519Pub name sI)
  let pR ← payloadOf name kR (← x25519Pub name sR)
  let i0 ← expectOk name (Noise.State.init .initiator .empty sI)
  let r0 ← expectOk name (Noise.State.init .responder .empty sR)
  let (i1, a) ← expectOk name (stepAll i0 [.entropy (← key32 name (toHex (fill 32 8))),
    .«local» ⟨.empty⟩])
  let [.write m0] := a | r.check s!"{name}: message 0" false
  let (r1, a) ← expectOk name (stepAll r0 [.entropy (← key32 name (toHex (fill 32 9))),
    .«local» ⟨pR⟩, .bytes (body m0)])
  let [.payload _ none, .write m1] := a | r.check s!"{name}: message 1" false
  let (_, a) ← expectOk name (stepAll i1 [.«local» ⟨pI⟩, .bytes (body m1)])
  -- The payload comes before the write of message 2, with the key its
  -- check needs, so the shell can refuse before message 2 goes out.
  let [.payload q1 (some k1), .write m2, .complete ci] := a | r.check s!"{name}: message 2" false
  r.check s!"{name}: the initiator proves the responder's peer id"
    (match Noise.verify k1 q1.bytes with | .ok v => v.peer == peerR | .error _ => false)
  let (_, a) ← expectOk name (stepAll r1 [.bytes (body m2)])
  let [.payload q2 (some k2), .complete cr] := a | r.check s!"{name}: completion" false
  r.check s!"{name}: the responder proves the initiator's peer id"
    (match Noise.verify k2 q2.bytes with | .ok v => v.peer == peerI | .error _ => false)
  r.check s!"{name}: the cipher states pair up" (ci.send == cr.recv && ci.recv == cr.send)

private def libp2p (r : Runner) : IO Unit := do
  try libp2pRun r
  catch e => r.check s!"libp2p handshake: runs ({e})" false

/-! ## Hostile input -/

private def hostileRun (r : Runner) : IO Unit := do
  let file := "noise-vectors.json"
  let name := "noise hostile"
  let j ← loadJson file
  let some c := (← jArr file j "cases").head? | r.check s!"{name}: a flynn case" false
  let iS ← key32 file (← jStr file c "initStatic")
  let rS ← key32 file (← jStr file c "respStatic")
  let iE ← key32 file (← jStr file c "initEphemeral")
  let cts ← (← jArr file c "messages").mapM fun m => do unhex file (← jStr file m "ciphertext")
  -- The indexes below read the three handshake messages.
  unless 3 ≤ cts.length do
    r.check s!"{name}: three handshake messages" false
    return
  let m1 := cts[1]!
  -- The initiator before and after message 0.
  let i0 ← expectOk name (Noise.State.init .initiator .empty iS)
  r.check s!"{name}: a message before the initiator's first write is out of turn"
    (failsWith .unexpectedEvent (Noise.step i0 (.bytes ⟨m1⟩)))
  let (i1, _) ← expectOk name (stepAll i0 [.entropy iE, .«local» ⟨.empty⟩])
  r.check s!"{name}: a changed payload tag fails to decrypt"
    (failsWith .decrypt (stepAll i1 [.bytes ⟨flip m1 (m1.size - 1)⟩]))
  r.check s!"{name}: a changed static key fails to decrypt"
    (failsWith .decrypt (stepAll i1 [.bytes ⟨flip m1 32⟩]))
  r.check s!"{name}: a 10-byte message 1 is short"
    (failsWith (.shortMessage 10 32) (stepAll i1 [.bytes ⟨fill 10 0⟩]))
  r.check s!"{name}: message 1 without its payload tag is short"
    (failsWith (.shortMessage 40 80) (stepAll i1 [.bytes ⟨m1.extract 0 40⟩]))
  let long := Noise.maxMessage + 1
  r.check s!"{name}: a {long}-byte message is refused"
    (failsWith (.messageTooLarge long) (stepAll i1 [.bytes ⟨fill long 0⟩]))
  r.check s!"{name}: an entropy the phase does not need is refused"
    (failsWith .unexpectedEvent (stepAll i1 [.entropy iE]))
  r.check s!"{name}: a second waiting payload is refused"
    (failsWith .unexpectedEvent (stepAll i1 [.«local» ⟨.empty⟩, .«local» ⟨.empty⟩]))
  let (i2, a) ← expectOk name (stepAll i1 [.«local» ⟨.empty⟩, .bytes ⟨m1⟩])
  let [_, .write w2, .complete _] := a | r.check s!"{name}: the initiator completes" false
  r.check s!"{name}: message 2 matches the vector" (w2 == ⟨frame cts[2]!⟩)
  r.check s!"{name}: an event after the completion is refused"
    (failsWith .finished (Noise.step i2 (.bytes ⟨.empty⟩)))
  -- The responder after message 1 has no write left.
  let r0 ← expectOk name (Noise.State.init .responder .empty rS)
  let rE ← key32 file (← jStr file c "respEphemeral")
  let (r1, _) ← expectOk name (stepAll r0 [.entropy rE, .«local» ⟨.empty⟩, .bytes ⟨cts[0]!⟩])
  r.check s!"{name}: a payload after the responder's last write is refused"
    (failsWith .unexpectedEvent (Noise.step r1 (.«local» ⟨.empty⟩)))

private def hostile (r : Runner) : IO Unit := do
  try hostileRun r
  catch e => r.check s!"noise hostile: runs ({e})" false

/-! ## The seam values over the sim (unit 1b) -/

section Sim

open Conc (Async OnceRef)
open Streams (Connection)
open Libp2p.Core (SecureConn SecurityProtocol)

/-- An address, or a failed run. -/
private def ma (s : String) : Async Multiformats.Multiaddr := do
  match Multiformats.Multiaddr.parse? s with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"test address {s} does not parse"

/-- A connected pair over a fresh sim net: the dialer's end and the
listener's end. -/
private def pair (split : Bool := false) : Async (Connection × Connection) := do
  let net ← Streams.Sim.Net.new split
  let l ← net.transport.listen (← ma "/memory/7")
  let some c ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
  let some s ← l.accept | throw <| IO.userError "accept failed"
  l.close
  return (c, s)

/-- A Noise configuration from an Ed25519 identity byte and a static key
byte. -/
private def cfgOf (where_ : String) (idByte staticByte : UInt8) : IO Noise.Config := do
  return { identity := ← identity where_ idByte, static := ← key32 where_ (toHex (fill 32 staticByte)) }

/-- The peer id of a configuration's identity. -/
private def peerOf (where_ : String) (cfg : Noise.Config) : IO PeerId :=
  expectOk where_ (do PeerId.ofPubKey (← cfg.identity.toPublic))

/-- The connection with each write passed through `f`, which sees the
number of the write, from 0, and a cell of its own. `f` answers the
bytes to write now. -/
private def mapWrites {σ : Type} (c : Connection) (init : σ)
    (f : Nat → ByteArray → σ → ByteArray × σ) : BaseIO Connection := do
  let cell : OnceRef (Nat × σ) ← OnceRef.new (0, init)
  return { c with
    write := fun b => do
      -- The ascription marks the step `BaseIO`, so the lift into `Async`
      -- applies (see `Conc.TaskSet.joinAll`).
      let out ← (cell.updateGet fun (n, s) =>
        let (out, s') := f n b s
        (out, (n + 1, s')) : BaseIO ByteArray)
      if !out.isEmpty then c.write out }

/-- Run both handshakes: the responder as a task, the initiator here.
The await joins the task (§4.1, rule 2). -/
private def both (pI pR : SecurityProtocol) (c s : Connection) (leftR : ByteArray := .empty) :
    Async (Except Libp2p.Core.Error SecureConn × Except Libp2p.Core.Error SecureConn) := do
  let t ← (Conc.Wrap.spawn (pR.handshake .responder s leftR).run :
    BaseIO (Task (Except IO.Error (Except Libp2p.Core.Error SecureConn))))
  let ri ← (pI.handshake .initiator c .empty).run
  match ← Conc.Wrap.await t with
  | .ok rr => return (ri, rr)
  | .error e => throw e

/-- Read until `n` bytes have arrived, or the end. -/
private def readN (sc : SecureConn) (n : Nat) : Async ByteArray := do
  let mut acc := ByteArray.empty
  while acc.size < n do
    match ← sc.read with
    | some b => acc := acc ++ b
    | none => break
  return acc

/-- The secure connection of a result, or a failed run. -/
private def secured (where_ : String) : Except Libp2p.Core.Error SecureConn → Async SecureConn
  | .ok sc => return sc
  | .error e => throw <| IO.userError s!"{where_}: {e}"

/-- True when the join answers an orderly end. -/
private def joinsOk (sc : SecureConn) : Async Bool := do
  match ← sc.join.run with
  | .ok () => return true
  | .error _ => return false

/-- The handshake end-to-end in both roles, data both ways, and the
orderly close. -/
private def simRoundTrip (r : Runner) (split : Bool) : Async Unit := do
  let name := s!"noise sim{if split then " (split writes)" else ""}"
  let cfgI ← cfgOf name 3 5
  let cfgR ← cfgOf name 4 6
  let (c, s) ← pair split
  let (ri, rr) ← both (Noise.securityProtocol cfgI) (Noise.securityProtocol cfgR) c s
  let ci ← secured name ri
  let cr ← secured name rr
  r.check s!"{name}: the initiator proves the responder's peer id"
    (ci.remotePeer == (← peerOf name cfgR))
  r.check s!"{name}: the responder proves the initiator's peer id"
    (cr.remotePeer == (← peerOf name cfgI))
  r.check s!"{name}: each side names its own peer id"
    (ci.localPeer == (← peerOf name cfgI) && cr.localPeer == (← peerOf name cfgR))
  ci.write "hello".toUTF8
  r.check s!"{name}: the responder reads the initiator's bytes"
    ((← readN cr 5) == "hello".toUTF8)
  cr.write "world!".toUTF8
  r.check s!"{name}: the initiator reads the responder's bytes"
    ((← readN ci 6) == "world!".toUTF8)
  -- The orderly close: the peer reads the end, and both joins answer
  -- `.ok`.
  ci.close
  r.check s!"{name}: after the close the peer reads the end" ((← cr.read).isNone)
  cr.close
  r.check s!"{name}: both joins answer an orderly end" ((← joinsOk ci) && (← joinsOk cr))

/-- A changed transport frame is a protocol error: the responder's read
sees the end after the teardown, its join answers `protocol`, and the
initiator sees the connection go. -/
private def simCorrupt (r : Runner) : Async Unit := do
  let name := "noise sim corrupt frame"
  let cfgI ← cfgOf name 3 5
  let cfgR ← cfgOf name 4 6
  let (c, s) ← pair
  -- Writes 0 and 1 are handshake messages 0 and 2; write 2 is the first
  -- transport frame, and its last byte is a tag byte.
  let c' ← mapWrites c () fun n b _ => (if n == 2 then flip b (b.size - 1) else b, ())
  let (ri, rr) ← both (Noise.securityProtocol cfgI) (Noise.securityProtocol cfgR) c' s
  let ci ← secured name ri
  let cr ← secured name rr
  ci.write "tampered".toUTF8
  r.check s!"{name}: the reader sees the end, not the bytes" ((← cr.read).isNone)
  r.check s!"{name}: the join answers a protocol error"
    (match ← cr.join.run with | .error (.protocol _) => true | _ => false)
  r.check s!"{name}: the teardown closes the connection, so the peer reads the end"
    ((← ci.read).isNone)
  ci.close
  r.check s!"{name}: the initiator's join answers an orderly end" (← joinsOk ci)

/-- A write over `maxPlaintext` goes out in chunks, and the peer reads
it back whole. -/
private def simLargeWrite (r : Runner) : Async Unit := do
  let name := "noise sim large write"
  let cfgI ← cfgOf name 3 5
  let cfgR ← cfgOf name 4 6
  let (c, s) ← pair
  let (ri, rr) ← both (Noise.securityProtocol cfgI) (Noise.securityProtocol cfgR) c s
  let ci ← secured name ri
  let cr ← secured name rr
  let size := 2 * Noise.maxPlaintext + 5
  let big : ByteArray := ⟨(Array.range size).map (·.toUInt8)⟩
  -- The write parks until the writer has sent its frames, and the
  -- writer parks on the sim's pipe, so the read runs beside it.
  let t ← (Conc.Wrap.spawn (ci.write big) : BaseIO (Task (Except IO.Error Unit)))
  r.check s!"{name}: {size} bytes read back whole" ((← readN cr size) == big)
  match ← Conc.Wrap.await t with
  | .ok () => r.check s!"{name}: the write returns" true
  | .error e => r.check s!"{name}: the write returns ({e})" false
  ci.close
  cr.close
  r.check s!"{name}: both joins answer an orderly end" ((← joinsOk ci) && (← joinsOk cr))

/-- The fixed-key value: both roles over the sim, twice, give the same
bytes on the wire. -/
private def simFixedKey (r : Runner) : Async Unit := do
  let name := "noise fixed keys"
  let cfgI ← cfgOf name 3 5
  let cfgR ← cfgOf name 4 6
  let pI := Noise.fixedKeyProtocol cfgI (fill 32 11)
  let pR := Noise.fixedKeyProtocol cfgR (fill 32 12)
  let mut runs : Array (Array ByteArray × Array ByteArray) := #[]
  for _ in [0:2] do
    let (c, s) ← pair
    let logI : OnceRef (Array ByteArray) ← OnceRef.new #[]
    let logR : OnceRef (Array ByteArray) ← OnceRef.new #[]
    let c' := { c with write := fun b => do logI.update (·.push b); c.write b }
    let s' := { s with write := fun b => do logR.update (·.push b); s.write b }
    let (ri, rr) ← both pI pR c' s'
    let ci ← secured name ri
    let cr ← secured name rr
    ci.write "fixed".toUTF8
    r.check s!"{name}: the bytes arrive" ((← readN cr 5) == "fixed".toUTF8)
    ci.close
    cr.close
    discard <| joinsOk ci
    discard <| joinsOk cr
    runs := runs.push ((← (logI.get : BaseIO _)), (← (logR.get : BaseIO _)))
  -- The loop pushed two runs, so indexes 0 and 1 are in range.
  r.check s!"{name}: two runs write the same initiator bytes" (runs[0]!.1 == runs[1]!.1)
  r.check s!"{name}: two runs write the same responder bytes" (runs[0]!.2 == runs[1]!.2)
  r.check s!"{name}: the initiator wrote three messages and one frame" (runs[0]!.1.size == 3)

/-- The leftover in both directions. In: the responder's handshake
takes message 0 as its `ByteArray` argument. Out: message 2 and the
first transport frame arrive in one chunk, and the frame reaches the
reader through the `SecureConn`. -/
private def simLeftover (r : Runner) : Async Unit := do
  let name := "noise leftover"
  let cfgI ← cfgOf name 3 5
  let cfgR ← cfgOf name 4 6
  let (c, s) ← pair
  -- Write 1 is message 2: hold it, and send it with write 2, the first
  -- transport frame, as one chunk.
  let c' ← mapWrites c ByteArray.empty fun n b held =>
    if n == 1 then (.empty, b) else if n == 2 then (held ++ b, .empty) else (b, held)
  let pI := Noise.securityProtocol cfgI
  let pR := Noise.securityProtocol cfgR
  let t ← (Conc.Wrap.spawn (do
      -- The negotiation's stand-in: it reads message 0 and hands it on.
      let some m0 ← s.read | throw <| IO.userError s!"{name}: no message 0"
      (pR.handshake .responder s m0).run) :
    BaseIO (Task (Except IO.Error (Except Libp2p.Core.Error SecureConn))))
  let ci ← secured name (← (pI.handshake .initiator c' .empty).run)
  ci.write "early".toUTF8
  let cr ← match ← Conc.Wrap.await t with
    | .ok rr => secured name rr
    | .error e => throw e
  r.check s!"{name}: the responder's handshake over-read the frame" (!cr.leftover.isEmpty)
  r.check s!"{name}: the frame reaches the reader, decrypted" ((← readN cr 5) == "early".toUTF8)
  ci.close
  cr.close
  r.check s!"{name}: both joins answer an orderly end" ((← joinsOk ci) && (← joinsOk cr))

/-- Start one handshake as a task. The caller awaits it, which joins it
(§4.1, rule 2). -/
private def spawnHandshake (p : SecurityProtocol) (role : Libp2p.Core.Role) (c : Connection)
    (left : ByteArray := .empty) :
    BaseIO (Task (Except IO.Error (Except Libp2p.Core.Error SecureConn))) :=
  Conc.Wrap.spawn (p.handshake role c left).run

/-- The answer of a handshake task, or a failed run. -/
private def awaitHandshake (t : Task (Except IO.Error (Except Libp2p.Core.Error SecureConn))) :
    Async (Except Libp2p.Core.Error SecureConn) := do
  match ← Conc.Wrap.await t with
  | .ok rr => return rr
  | .error e => throw e

/-- A responder whose payload signs another static key: the initiator
fails with `authentication`, and message 2 never reaches the wire. The
responder runs the core directly, since a seam value always signs its
own static key. -/
private def simBadSignature (r : Runner) : Async Unit := do
  let name := "noise sim bad signature"
  let cfgI ← cfgOf name 3 5
  let sR ← key32 name (toHex (fill 32 6))
  let other ← x25519Pub name (← key32 name (toHex (fill 32 9)))
  let bad ← payloadOf name (← identity name 4) other
  let (c, s) ← pair
  let t ← spawnHandshake (Noise.securityProtocol cfgI) .initiator c
  let some m0 ← s.read | throw <| IO.userError s!"{name}: no message 0"
  let st ← expectOk name (Noise.State.init .responder .empty sR)
  let (_, a) ← expectOk name
    (stepAll st [.entropy (← key32 name (toHex (fill 32 8))), .«local» ⟨bad⟩, .bytes (body ⟨m0⟩)])
  let [.payload _ none, .write m1] := a | throw <| IO.userError s!"{name}: message 1"
  s.write m1.bytes
  r.check s!"{name}: the initiator fails with an authentication error"
    (match ← awaitHandshake t with | .error (.authentication _) => true | _ => false)
  r.check s!"{name}: message 2 never reaches the wire, and the connection ends"
    ((← s.read).isNone)

/-- A write after the peer has closed throws, as `Connection.write`
promises, and the join still answers an orderly end. -/
private def simWriteAfterClose (r : Runner) : Async Unit := do
  let name := "noise sim write after close"
  let cfgI ← cfgOf name 3 5
  let cfgR ← cfgOf name 4 6
  let (c, s) ← pair
  let (ri, rr) ← both (Noise.securityProtocol cfgI) (Noise.securityProtocol cfgR) c s
  let ci ← secured name ri
  let cr ← secured name rr
  cr.close
  r.check s!"{name}: the initiator reads the end" ((← ci.read).isNone)
  let threw ← try ci.write "late".toUTF8; pure false catch _ => pure true
  r.check s!"{name}: the write throws" threw
  r.check s!"{name}: both joins answer an orderly end" ((← joinsOk ci) && (← joinsOk cr))

/-- A fault of a connection read after the handshake: the reader sees
the end, and the join throws the fault (§3.5). The initiator's read 0
is message 1; every read after it throws. -/
private def simReadFault (r : Runner) : Async Unit := do
  let name := "noise sim read fault"
  let cfgI ← cfgOf name 3 5
  let cfgR ← cfgOf name 4 6
  let (c, s) ← pair
  let reads : OnceRef Nat ← OnceRef.new 0
  let c' : Connection := { c with
    read := do
      let n ← (reads.updateGet fun n => (n, n + 1) : BaseIO Nat)
      if n == 0 then c.read else throw <| IO.userError "injected read fault" }
  let (ri, rr) ← both (Noise.securityProtocol cfgI) (Noise.securityProtocol cfgR) c' s
  let ci ← secured name ri
  let cr ← secured name rr
  r.check s!"{name}: the reader sees the end" ((← ci.read).isNone)
  ci.close
  let thrown ← try discard ci.join.run; pure false catch _ => pure true
  r.check s!"{name}: the join throws the fault" thrown
  cr.close
  discard <| joinsOk cr

/-- A write whose frames go out after the loop has ended answers `.ok`.
The initiator's reads end once the test closes `fin`, as after a peer
FIN, while its writes still reach the peer. The write's frames wait at
`gate` until the teardown has run, and then go out. -/
private def simWriteAcrossEnd (r : Runner) : Async Unit := do
  let name := "noise sim write across the end"
  let cfgI ← cfgOf name 3 5
  let cfgR ← cfgOf name 4 6
  let (c, s) ← pair
  let fin : Conc.Chan Unit ← Conc.Chan.new 1
  let gate : Conc.Chan Unit ← Conc.Chan.new 1
  -- One slot per late write: the write says it reached the gate.
  let atGate : Conc.Chan Unit ← Conc.Chan.new 4
  let reads : OnceRef Nat ← OnceRef.new 0
  let writes : OnceRef Nat ← OnceRef.new 0
  let c' : Connection := { c with
    read := do
      let n ← (reads.updateGet fun n => (n, n + 1) : BaseIO Nat)
      -- Read 0 is message 1. After it, park until `fin` closes: the end.
      if n == 0 then c.read else do discard fin.recv; return none
    write := fun b => do
      let n ← (writes.updateGet fun n => (n, n + 1) : BaseIO Nat)
      -- Writes 0 and 1 are handshake messages; later ones wait at the gate.
      if n ≥ 2 then
        discard (atGate.trySend () : BaseIO Bool)
        discard gate.recv
      c.write b }
  let (ri, rr) ← both (Noise.securityProtocol cfgI) (Noise.securityProtocol cfgR) c' s
  let ci ← secured name ri
  let cr ← secured name rr
  let t ← (Conc.Wrap.spawn (ci.write "late".toUTF8) : BaseIO (Task (Except IO.Error Unit)))
  -- The write's frames reach the gate before the reads end, so the
  -- loop took the write before it shut down.
  discard atGate.recv
  -- The end of the reads: the loop shuts down, and the teardown closes
  -- the inbox, so this read answers `none` only after the teardown.
  fin.close
  r.check s!"{name}: the reader sees the end" ((← ci.read).isNone)
  gate.close
  r.check s!"{name}: the write answers .ok, since its frames went out"
    (match ← Conc.Wrap.await t with | .ok () => true | .error _ => false)
  r.check s!"{name}: the peer reads the bytes" ((← readN cr 4) == "late".toUTF8)
  ci.close
  cr.close
  r.check s!"{name}: both joins answer an orderly end" ((← joinsOk ci) && (← joinsOk cr))

/-- The peer ends the connection inside the handshake: the initiator
fails with `closed`. -/
private def simHandshakeEof (r : Runner) : Async Unit := do
  let name := "noise sim handshake eof"
  let cfgI ← cfgOf name 3 5
  let (c, s) ← pair
  let t ← spawnHandshake (Noise.securityProtocol cfgI) .initiator c
  let some _ ← s.read | throw <| IO.userError s!"{name}: no message 0"
  s.close
  r.check s!"{name}: the initiator fails with closed"
    (match ← awaitHandshake t with | .error (.closed _) => true | _ => false)

/-- The transport core at its edges: the end of the connection, a read
that completes no frame, and a cipher state at the reserved nonce
(owned contract 6). -/
private def transportEdges (r : Runner) : IO Unit := do
  let name := "noise transport core"
  let k ← key32 name (toHex (fill 32 1))
  let st : Noise.Transport.State := ⟨.ofKey k, .ofKey k, ⟨.empty⟩⟩
  r.check s!"{name}: an end between frames shuts down"
    (match Noise.Transport.step st .eof with | .ok (_, [.shutdown]) => true | _ => false)
  -- A prefix of 5 and one body byte: no frame is whole yet.
  let short : ByteArray := ⟨#[0, 5, 1]⟩
  let (st', a) ← expectOk name (Noise.Transport.step st (.bytes ⟨short⟩))
  r.check s!"{name}: a read that completes no frame returns its credit" (a == [.credit])
  r.check s!"{name}: an end inside a frame is truncatedFrame"
    (failsWith (.truncatedFrame 3) (Noise.Transport.step st' .eof))
  let spent : Noise.CipherState := ⟨some k, Noise.reservedNonce⟩
  r.check s!"{name}: a seal at the reserved nonce fails"
    (failsWith .nonceExhausted (Noise.Transport.sealFrames spent (fill 3 0)))
  r.check s!"{name}: a write at the reserved nonce fails the step, so the loop tears down"
    (failsWith .nonceExhausted (Noise.Transport.step { st with send := spent } (.write 0 ⟨fill 3 0⟩)))
  -- The seam arms of the payload check and of the end (owned contract 4).
  let authArms := [Noise.Error.badSignature, .missingIdentity, .identity .publicMismatch,
    .payloadTooLarge (Noise.maxPayload + 1), .payload .badField]
  r.check s!"{name}: every failure of the payload check maps to authentication"
    (authArms.all fun e => match e.toCore with | .authentication _ => true | _ => false)
  r.check s!"{name}: an open failure maps to protocol"
    (match Noise.Error.decrypt.toCore with | .protocol _ => true | _ => false)

/-- The pure chunking: three frames, at the cap, at the cap, and the
rest. -/
private def chunking (r : Runner) : IO Unit := do
  let name := "noise chunking"
  let k ← key32 name (toHex (fill 32 1))
  let size := 2 * Noise.maxPlaintext + 5
  let (_, wire) ← expectOk name (Noise.Transport.sealFrames (.ofKey k) (fill size 7))
  let mut lens : Array Nat := #[]
  let mut rest := wire
  while !rest.isEmpty do
    match Streams.Framing.headerB? .u16be Noise.maxMessage rest with
    | .ok (len, hsize) =>
      lens := lens.push len
      rest := rest.extract (hsize + len) rest.size
    | .error _ => break
  r.check s!"{name}: {size} bytes go out as frames of 65535, 65535, and 21 bytes"
    (lens == #[Noise.maxMessage, Noise.maxMessage, 5 + Crypto.aeadTagLen])
  let (_, empty) ← expectOk name (Noise.Transport.sealFrames (.ofKey k) .empty)
  r.check s!"{name}: an empty write takes no frame" empty.isEmpty

private def sim (r : Runner) : IO Unit := do
  chunking r
  transportEdges r
  for (label, act) in [("round trip", simRoundTrip r false), ("split round trip", simRoundTrip r true),
      ("corrupt", simCorrupt r), ("large write", simLargeWrite r), ("fixed keys", simFixedKey r),
      ("leftover", simLeftover r), ("bad signature", simBadSignature r),
      ("handshake eof", simHandshakeEof r), ("write after close", simWriteAfterClose r), ("read fault", simReadFault r),
      ("write across the end", simWriteAcrossEnd r)] do
    try Conc.Async.run act
    catch e => r.check s!"noise sim {label}: runs ({e})" false

end Sim

/-! ## The constants -/

-- The frame cap is the largest length the 2-byte prefix carries, so
-- every frame header a read takes is within the cap before the payload
-- allocates (owned contract 8).
example : Noise.maxMessage = Streams.Framing.Prefix.maxLen .u16be := rfl

-- The protocol name is exactly 32 bytes, so `InitializeSymmetric`
-- takes it as `h` with no padding and no hash.
#guard Noise.protocolName.toUTF8.size = 32
def Noise.run (r : Runner) : IO Unit := do
  r.section "noise" "flynn/noise vectors.txt; go-libp2p p2p/security/noise"
  -- The plaintext cap leaves room for the tag inside the frame cap. The
  -- tag length reads the shim through `@[extern]`, so neither the kernel
  -- nor the build-time interpreter can evaluate it; the test binary,
  -- which links the shim, checks it.
  r.check "the plaintext cap and the tag fill the frame cap"
    (Noise.maxPlaintext + Crypto.aeadTagLen == Noise.maxMessage)
  flynn r
  goTranscript r
  payloadChecks r
  libp2p r
  hostile r
  sim r

end Tests