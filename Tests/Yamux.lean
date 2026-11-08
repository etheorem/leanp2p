import Tests.Support
import Yamux
import Bytes

/-!
# Yamux suite (unit W4.3)

The checks of `packages/net/yamux/docs/PLAN.md`, "Test milestones",
units 1a and 1b. The spike's yamux suite (`spike`, `Tests/Yamux.lean`)
guards the same contracts, and this suite keeps each one. The new
checks derive from the spec (`vendor/specs/yamux/README.md`) and the
package documents:

* **Header (1a).** The fixed 12-byte encodings of the spec field table,
  the round trip with suffix consumption, `truncated` for a short
  prefix, `malformed` for the three header violations, and the generic
  harness of `base/bytes` over the `ByteArray` path.
* **Core transcripts (1b).** Lists of `Event`s through `step`, with the
  `Action`s or the `ProtocolError` they must give: the hostile frames,
  flow control with the hand-off of a grant, half-close, retirement,
  and the backlog. No task, no network, no clock (ARCHITECTURE §6,
  layer 4).
* **Sessions (1b).** Two sessions over the sim transport, plain and
  byte-splitting, and one session against a raw peer that sends
  hostile bytes (§6, layer 5).

No answer depends on how the scheduler orders the tasks. A raw peer
that must know the session has taken its frames sends a ping after them
and waits for the echo: the session takes its bytes in order.
-/

set_option autoImplicit false

namespace Tests

open Conc Streams Yamux

/-! ## Helpers -/

/-- The bytes of a string. -/
private def b (s : String) : ByteArray := s.toUTF8

/-- `n` bytes, each `x`. -/
private def fill (n : Nat) (x : UInt8 := 7) : ByteArray := ⟨Array.replicate n x⟩

/-- The wire bytes of a window-update frame. -/
private def wf (fl : Flags) (id : Nat) (delta : Nat := 0) : ByteArray :=
  (windowFrame fl id delta).bytes

/-- The wire bytes of a data frame. -/
private def df (fl : Flags) (id : Nat) (body : ByteArray) : ByteArray :=
  (frame .data fl id body.size body).bytes

/-- The wire bytes of a ping frame. -/
private def pf (fl : Flags) (value : Nat) : ByteArray := (frame .ping fl 0 value).bytes

/-- The wire bytes of a go-away frame with a raw code. -/
private def gf (code : Nat) : ByteArray := (frame .goAway Flags.none 0 code).bytes

/-- The flags SYN and FIN together. -/
private def synFin : Flags := { synFlags with fin := true }

/-- Run the events through `step` from `s`: the last state and every
action, or the first error. -/
private def feed (s : State) (evs : List Event) : Except ProtocolError (State × List Action) :=
  evs.foldlM (init := (s, [])) fun (s, acc) ev => do
    let (s', a) ← step s ev
    return (s', acc ++ a)

/-- One `bytes` event. -/
private def bytesEvent (x : ByteArray) : Event := .bytes ⟨x⟩

/-- The actions of a transcript, or `none` on an error. -/
private def actionsOf (r : Except ProtocolError (State × List Action)) : Option (List Action) :=
  match r with
  | .ok (_, a) => some a
  | .error _ => none

/-- The live stream ids of a transcript's last state. -/
private def idsOf (r : Except ProtocolError (State × List Action)) : Option (List Nat) :=
  match r with
  | .ok (s, _) => some (s.streams.map (·.id.val))
  | .error _ => none

/-- The delivered bytes of a list of actions, joined. -/
private def delivered (acts : List Action) : ByteArray :=
  acts.foldl (fun acc a => match a with | .deliver _ p => acc ++ p.bytes | _ => acc) .empty

/-- The actions other than deliveries. -/
private def notDelivered (acts : List Action) : List Action :=
  acts.filter fun a => match a with | .deliver _ _ => false | _ => true

/-- The sizes of the data frames among the sends. -/
private def dataSizes (acts : List Action) : List Nat :=
  acts.filterMap fun a => match a with
    | .send f =>
      match Header.decodeB? f.bytes with
      | .ok (h, _) => if h.type == .data then some h.length else none
      | .error _ => none
    | _ => none

/-- True when the result is the error `e`. -/
private def errs (e : ProtocolError) (r : Except ProtocolError (State × List Action)) : Bool :=
  match r with
  | .error e' => e == e'
  | .ok _ => false

/-! ## Header (unit 1a) -/

/-- A header of these fields. -/
private def hd (t : FrameType) (fl : Flags) (id len : Nat) : Header := Header.make t fl id len

/-- The fixed encodings: the unit vectors of the plan, from the spec
field table. -/
private def fixedVectors : List (String × Header × List Nat) := [
  ("a data frame on stream 5 with length 3",
    hd .data Flags.none 5 3, [0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 3]),
  ("a window-update SYN on stream 7 with the 256 KiB window",
    hd .windowUpdate synFlags 7 initialWindow, [0, 1, 0, 1, 0, 0, 0, 7, 0, 4, 0, 0]),
  ("a ping SYN with opaque 42",
    hd .ping synFlags 0 42, [0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 42]),
  ("a go-away with code 0",
    hd .goAway Flags.none 0 0, [0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  ("a data frame with FIN on stream 3",
    hd .data finFlags 3 0, [0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 0]),
  ("every flag, the largest id and length",
    hd .windowUpdate ⟨true, true, true, true, 0⟩ (2 ^ 32 - 1) (2 ^ 32 - 1),
    [0, 1, 0, 15, 255, 255, 255, 255, 255, 255, 255, 255]),
  ("every undefined flag bit, carried through the codec",
    hd .data ⟨false, false, false, false, 4095⟩ 1 0,
    [0, 0, 255, 240, 0, 0, 0, 1, 0, 0, 0, 0])]

/-- The production decoder in the harness's shape: the rest of the input
in the model view (`Bytes.checkModelPins`). -/
private def decodeHeaderB (b : ByteArray) : Except Bytes.DecodeError (Header × List Nat) :=
  (Header.decodeB? b).map fun (h, rest) => (h, Bytes.toNatList rest)

/-- The generic harness over the header (`Bytes.checkRoundTrips`,
`Bytes.checkModelPins`): the round trip on the samples, and the model pin
on every input up to two bytes, on the samples with a suffix, and on
seeded random inputs. -/
private def headerHarness (g : StdGen) : Bool × StdGen :=
  let samples := fixedVectors.map (·.2.1)
  let encoded := samples.map fun h => Bytes.ofNatList (Bytes.Codec.encode h ++ [7, 7])
  -- Random 12- to 14-byte inputs: most break a field, so the pin sees
  -- the malformed path; the rest decode.
  let (random, g) := genBytesList 3000 14 g
  -- Random valid headers, so the pin sees the decode path as often.
  let (valid, g) := Nat.fold 500 (fun _ _ (acc, g) =>
    let (t, g) := randNat g 0 3
    let (fl, g) := randNat g 0 65535
    let (id, g) := randNat g 0 (2 ^ 32 - 1)
    let (len, g) := randNat g 0 (2 ^ 32 - 1)
    let h := hd ((FrameType.ofCode? t).getD .data) ((Flags.ofBits? fl).getD Flags.none) id len
    (Header.encodeB h :: acc, g)) ([], g)
  (Bytes.checkRoundTrips samples &&
    -- Every input up to 2 bytes covers each prefix shape the decoder
    -- can meet before its 12-byte read.
    Bytes.checkModelPins decodeHeaderB (allBytesUpTo 2 ++ encoded ++ random ++ valid), g)

private def headerChecks (r : Runner) : IO Unit := do
  for (name, h, wire) in fixedVectors do
    r.check s!"header: {name} encodes to the spec bytes" (Bytes.Codec.encode h == wire)
    r.check s!"header: {name}, the ByteArray encoder agrees" (Bytes.toNatList h.encodeB == wire)
    r.check s!"header: {name} decodes back"
      (match (Bytes.Codec.decode? wire : Except Bytes.DecodeError (Header × List Nat)) with
        | .ok (h', []) => h' == h
        | _ => false)
    -- Suffix consumption: the header comes off the front, and the rest
    -- comes back untouched.
    r.check s!"header: {name} decodes off a longer buffer"
      (match (Bytes.Codec.decode? (wire ++ [1, 2, 3]) : Except Bytes.DecodeError (Header × List Nat)) with
        | .ok (h', rest) => h' == h && rest == [1, 2, 3]
        | _ => false)
  let wire := [0, 1, 0, 1, 0, 0, 0, 7, 0, 4, 0, 0]
  r.check "header: every prefix shorter than 12 bytes is truncated"
    ((List.range 12).all fun n =>
      failsWith .truncated (Bytes.Codec.decode? (wire.take n) : Except Bytes.DecodeError (Header × List Nat)) &&
      failsWith .truncated (Header.decodeB? (Bytes.ofNatList (wire.take n))))
  let bad : List (String × List Nat) := [
    ("a version other than 0", [1, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 3]),
    ("an unknown type", [0, 4, 0, 0, 0, 0, 0, 5, 0, 0, 0, 3])]
  for (name, w) in bad do
    r.check s!"header: {name} is malformed"
      (failsWith .malformed (Bytes.Codec.decode? w : Except Bytes.DecodeError (Header × List Nat)) &&
        failsWith .malformed (Header.decodeB? (Bytes.ofNatList w)))
  -- A flag bit outside the four passes, as at go-yamux and rust-yamux,
  -- and leaves the four flags as the wire sets them.
  let odd : List (String × List Nat × Flags) := [
    ("a flag bit outside the four", [0, 0, 0, 17, 0, 0, 0, 5, 0, 0, 0, 3], ⟨true, false, false, false, 1⟩),
    ("a flag bit in the high byte", [0, 0, 1, 0, 0, 0, 0, 5, 0, 0, 0, 3], ⟨false, false, false, false, 16⟩)]
  for (name, w, fl) in odd do
    r.check s!"header: {name} decodes, and the four flags read as sent"
      ((match (Bytes.Codec.decode? w : Except Bytes.DecodeError (Header × List Nat)) with
        | .ok (h, []) => h.flags == fl | _ => false) &&
       (match Header.decodeB? (Bytes.ofNatList w) with
        | .ok (h, _) => h.flags == fl | _ => false))
  -- The closed sets: every code past the table answers none.
  r.check "the frame types stop at 3"
    ((List.range 252).all fun n => (FrameType.ofCode? (n + 4)).isNone)
  r.check "the go-away codes stop at 2"
    ((List.range 253).all fun n => (GoAwayCode.ofCode? (n + 3)).isNone)
  let (pinned, _) := headerHarness (mkStdGen 43)
  r.check "the header codec pins to the model" pinned

/-! ## Core transcripts (unit 1b) -/

/-- The server sees the client's streams: odd ids. -/
private def server : State := State.new .server

/-- The client opens odd ids. -/
private def client : State := State.new .client

private def coreSynChecks (r : Runner) : IO Unit := do
  -- A SYN with the peer's parity opens a stream, and the ACK goes out
  -- as a control frame.
  let syn := feed server [bytesEvent (wf synFlags 1)]
  r.check "core: a SYN with the peer's parity creates the stream, with the ACK"
    (actionsOf syn == some [.reply (windowFrame ackFlags 1), .accept ⟨1, 0⟩] && idsOf syn == some [1])
  -- A SYN with our own parity, or on the session id, is a protocol
  -- error, as at go-yamux and rust-yamux; on either role.
  let failsWithId (res : Except ProtocolError (State × List Action)) (id : Nat) : Bool :=
    match res with
    | .error e => e == .invalidStreamId id
    | .ok _ => false
  for (st, ownId) in [(server, 2), (client, 1)] do
    r.check s!"core: a SYN with our own parity is invalidStreamId (id {ownId})"
      (failsWithId (feed st [bytesEvent (wf synFlags ownId)]) ownId)
    r.check s!"core: a data SYN with our own parity is invalidStreamId (id {ownId + 2})"
      (failsWithId (feed st [bytesEvent (df synFlags (ownId + 2) (b "abc"))]) (ownId + 2))
    r.check s!"core: a SYN on id 0 is invalidStreamId (our first id {ownId})"
      (failsWithId (feed st [bytesEvent (wf synFlags 0)]) 0)
  -- A frame for an unknown id creates no state, and its payload passes
  -- by; the next frame still parses.
  let unknown := feed server [bytesEvent (df Flags.none 3 (b "abc") ++ wf Flags.none 5 9 ++ wf synFlags 1)]
  r.check "core: frames for an unknown id create no state"
    (actionsOf unknown == some [.reply (windowFrame ackFlags 1), .accept ⟨1, 0⟩] && idsOf unknown == some [1])
  -- A later open of such an id still works: the peer's frames for our
  -- id 1 come before we open it.
  let later := feed client [bytesEvent (df Flags.none 1 (b "early") ++ wf ackFlags 1 100), .openStream 0]
  r.check "core: a later openStream of an id that saw stray frames still works"
    (actionsOf later == some [.send (windowFrame synFlags 1), .opened 0 ⟨1, 0⟩] && idsOf later == some [1])
  -- Our ids rise by two, with our parity.
  let opens := feed server [.openStream 0, .openStream 1, .openStream 2]
  r.check "core: the server opens 2, 4, 6"
    (idsOf opens == some [6, 4, 2])
  r.check "core: a SYN for a live stream is an error"
    (errs (.duplicateStream 1) (feed server [bytesEvent (wf synFlags 1), bytesEvent (wf synFlags 1)]))

private def coreWindowChecks (r : Runner) : IO Unit := do
  -- The window caps a stream's data: the full window is fine, one byte
  -- more is an error, and nothing past the window is delivered.
  let full := feed server [bytesEvent (wf synFlags 1 ++ df Flags.none 1 (fill initialWindow))]
  r.check "core: data up to the window is delivered"
    (match full with | .ok (_, a) => (delivered a).size == initialWindow | _ => false)
  let over := feed server [bytesEvent (wf synFlags 1 ++ df Flags.none 1 (fill initialWindow)),
    bytesEvent (df Flags.none 1 (b "x"))]
  r.check "core: data beyond the receive window is a protocol error"
    (errs (.windowExceeded 1 1 0) over)
  -- The error comes at the header: a frame whose payload has not
  -- arrived yet still fails.
  let early := feed server [bytesEvent (wf synFlags 1), bytesEvent ((Header.make .data Flags.none 1 (initialWindow + 1)).encodeB)]
  r.check "core: a data frame longer than the window fails at its header"
    (errs (.windowExceeded 1 (initialWindow + 1) initialWindow) early)
  r.check "core: a data frame longer than the window fails for an unknown id too"
    (errs (.windowExceeded 99 (initialWindow + 1) initialWindow)
      (feed server [bytesEvent ((Header.make .data Flags.none 99 (initialWindow + 1)).encodeB)]))
  -- Consumption returns the credit once half the window is free.
  let base := [bytesEvent (wf synFlags 1 ++ df Flags.none 1 (fill initialWindow))]
  let small := feed server (base ++ [.consumed ⟨1, 0⟩ 1000])
  r.check "core: a small consumption sends no window update"
    (match small with | .ok (_, a) => (notDelivered a).length == 2 | _ => false)
  let half := feed server (base ++ [.consumed ⟨1, 0⟩ (initialWindow / 2)])
  r.check "core: consuming half the window sends a window update for it"
    (match half with
      | .ok (_, a) => (notDelivered a).getLast? == some (.send (windowFrame Flags.none 1 (initialWindow / 2)))
      | _ => false)
  -- The receive window never goes negative: after the update, the peer
  -- may send exactly what it got back, and no byte more.
  let refill := feed server (base ++ [.consumed ⟨1, 0⟩ (initialWindow / 2),
    bytesEvent (df Flags.none 1 (fill (initialWindow / 2)))])
  r.check "core: the returned credit admits exactly that much data"
    (match refill with | .ok _ => true | _ => false)
  r.check "core: the returned credit admits no byte more"
    (errs (.windowExceeded 1 1 0) (feed server (base ++ [.consumed ⟨1, 0⟩ (initialWindow / 2),
      bytesEvent (df Flags.none 1 (fill (initialWindow / 2))), bytesEvent (df Flags.none 1 (b "x"))])))

private def coreFlowChecks (r : Runner) : IO Unit := do
  -- A write beyond the credit goes out up to the credit, in frames of
  -- at most `maxDataFrame`, and answers `blocked` with the count it
  -- sent. The core keeps no part of it: the shell parks the writer
  -- (owned contract 4). A second write finds no credit.
  let big := initialWindow + 37856
  let start := [.openStream 0, .write ⟨1, 0⟩ 1 ⟨fill big⟩, .write ⟨1, 0⟩ 2 ⟨fill 10⟩]
  r.check "core: a write sends up to the credit in capped frames, and blocks with the count"
    (match feed client start with
      | .ok (s, a) => dataSizes a == [65536, 65536, 65536, 65536] &&
          a.contains (.blocked 1 1 initialWindow) && a.contains (.blocked 1 2 0) &&
          !a.contains (.done 1) && !a.contains (.done 2) &&
          s.streams.map (·.state.sendCredit) == [0]
      | _ => false)
  -- A window update signals credit, and sends no data by itself.
  let granted := start ++ [bytesEvent (wf Flags.none 1 40000)]
  r.check "core: a window update signals credit, and sends nothing itself"
    (match feed client granted with
      | .ok (_, a) => a.getLast? == some (.credit 1) && (dataSizes a).length == 4
      | _ => false)
  -- The woken writer posts its rest: it completes, and the credit it
  -- left signals again, so the next parked writer wakes.
  let rest1 := granted ++ [.write ⟨1, 0⟩ 1 ⟨fill 37856⟩]
  r.check "core: the rest of a woken write completes, and the credit left goes on"
    (match feed client rest1 with
      | .ok (_, a) => (dataSizes a).drop 4 == [37856] && a.contains (.done 1) &&
          a.getLast? == some (.credit 1)
      | _ => false)
  r.check "core: a partly used grant reaches the next writer"
    (match feed client (rest1 ++ [.write ⟨1, 0⟩ 2 ⟨fill 10⟩]) with
      | .ok (_, a) => (dataSizes a).drop 4 == [37856, 10] && a.contains (.done 2)
      | _ => false)
  -- A grant that stops inside the second write blocks it again, with the
  -- count it covered.
  let short := start ++ [bytesEvent (wf Flags.none 1 37860), .write ⟨1, 0⟩ 1 ⟨fill 37856⟩,
    .write ⟨1, 0⟩ 2 ⟨fill 10⟩]
  r.check "core: a grant too small for the next write sends what it covers"
    (match feed client short with
      | .ok (_, a) => a.contains (.done 1) && !a.contains (.done 2) &&
          (dataSizes a).drop 4 == [37856, 4] && a.getLast? == some (.blocked 1 2 4)
      | _ => false)
  r.check "core: an empty write completes at once"
    (match feed client [.openStream 0, .write ⟨1, 0⟩ 7 ⟨.empty⟩] with
      | .ok (_, a) => a.contains (.done 7) && dataSizes a == []
      | _ => false)
  r.check "core: a write to an unknown stream is refused"
    (actionsOf (feed client [.write ⟨9, 0⟩ 3 ⟨b "x"⟩]) == some [.refused 3 .closed])
  -- Our own ACK backlog: the 257th open waits for an ACK.
  let opens := (List.range (backlogCap + 1)).map Event.openStream
  let waiting := feed client opens
  r.check "core: an open beyond our ACK backlog waits"
    (match waiting with
      | .ok (s, a) => s.streams.length == backlogCap &&
          !a.contains (.opened backlogCap ⟨2 * backlogCap + 1, backlogCap⟩)
      | _ => false)
  r.check "core: an ACK lets the waiting open through"
    (match feed client (opens ++ [bytesEvent (wf ackFlags 1)]) with
      | .ok (_, a) => a.contains (.opened backlogCap ⟨2 * backlogCap + 1, backlogCap⟩)
      | _ => false)

private def coreCloseChecks (r : Runner) : IO Unit := do
  -- Half-close: our FIN ends our direction only, and the response after
  -- it still arrives.
  let half := feed client [.openStream 0, .close ⟨1, 0⟩, bytesEvent (df Flags.none 1 (b "response"))]
  r.check "core: close sends FIN and keeps the stream for the response"
    (match half with
      | .ok (s, a) => a.contains (.send (windowFrame finFlags 1)) &&
          a.contains (.deliver 1 ⟨b "response"⟩) && s.streams.length == 1
      | _ => false)
  r.check "core: a write after our FIN is refused"
    (match feed client [.openStream 0, .close ⟨1, 0⟩, .write ⟨1, 0⟩ 4 ⟨b "late"⟩] with
      | .ok (_, a) => a.contains (.refused 4 .closed)
      | _ => false)
  -- Our FIN ends the write direction: the parked writers wake with
  -- `closed`, since no data may follow the FIN.
  r.check "core: close ends the writes with closed, before the FIN"
    (actionsOf (feed client [.openStream 0, .close ⟨1, 0⟩]) ==
      some [.send (windowFrame synFlags 1), .opened 0 ⟨1, 0⟩, .endWrites 1 .closed,
        .send (windowFrame finFlags 1)])
  -- Retirement: the peer's FIN after ours leaves no entry.
  let both := feed client [.openStream 0, .close ⟨1, 0⟩, bytesEvent (df finFlags 1 (b "bye"))]
  r.check "core: a stream both sides closed leaves the session map"
    (match both with
      | .ok (s, a) => s.streams.isEmpty && a.contains (.eof 1) && a.contains (.deliver 1 ⟨b "bye"⟩)
      | _ => false)
  -- The FIN of a data frame applies after its payload, also when the
  -- payload arrives in pieces.
  let frameBytes := df finFlags 1 (b "bye")
  let pieces := (List.range frameBytes.size).map fun i => bytesEvent (frameBytes.extract i (i + 1))
  let split := feed client ([.openStream 0, .close ⟨1, 0⟩] ++ pieces)
  r.check "core: a FIN on a split data frame applies after the payload"
    (match split with
      | .ok (s, a) => s.streams.isEmpty && (delivered a).toList == (b "bye").toList &&
          notDelivered a == notDelivered (match both with | .ok (_, a) => a | _ => [])
      | _ => false)
  -- The peer numbers its own streams, in any order: go-yamux takes an id
  -- first and sends its SYN later, so concurrent opens arrive out of
  -- order. Any id of the peer's parity that is not live opens, as in
  -- go-yamux and rust-yamux, a retired one included. Each new stream
  -- takes the next epoch.
  let outOfOrder := feed server [bytesEvent (wf synFlags 3), bytesEvent (wf synFlags 1)]
  r.check "core: the peer's SYNs out of id order both open"
    (actionsOf outOfOrder == some [.reply (windowFrame ackFlags 3), .accept ⟨3, 0⟩,
      .reply (windowFrame ackFlags 1), .accept ⟨1, 1⟩])
  -- The first stream on id 1 reads the peer's FIN and closes its side,
  -- so it retires; the peer then opens id 1 again.
  let reuseEvents := [bytesEvent (wf synFlags 1), bytesEvent (df finFlags 1 (b "old")), .close ⟨1, 0⟩,
    bytesEvent (wf synFlags 1)]
  let reuse := feed server reuseEvents
  r.check "core: the peer may open one of its retired ids again, with an ACK and a new key"
    (match reuse with
      | .ok (s, a) => s.streams.map (·.key) == [⟨1, 1⟩] &&
          a.contains (.accept ⟨1, 0⟩) && a.contains (.accept ⟨1, 1⟩) &&
          (a.filter (· == .reply (windowFrame ackFlags 1))).length == 2
      | _ => false)
  -- The handle of the first stream still holds its chunk, and posts
  -- under the old key. Its events reach nothing: the new stream keeps
  -- its state, no frame goes out, and a write is refused.
  let stale := feed server (reuseEvents ++ [.consumed ⟨1, 0⟩ 3, .write ⟨1, 0⟩ 9 ⟨b "x"⟩,
    .close ⟨1, 0⟩, .reset ⟨1, 0⟩])
  r.check "core: a handle of the retired stream cannot reach the new stream on its id"
    (match reuse, stale with
      | .ok (s1, a1), .ok (s2, a2) => s1 == s2 && a2.drop a1.length == [.refused 9 .closed]
      | _, _ => false)
  -- Our own ids never come back: after a stream retires, the next open
  -- takes the next id.
  r.check "core: our retired id is never reused"
    (match feed client [.openStream 0, .reset ⟨1, 0⟩, .openStream 1] with
      | .ok (_, a) => a.contains (.opened 1 ⟨3, 1⟩) &&
          !a.any fun x => match x with | .opened 1 k => k.id == 1 | _ => false
      | _ => false)
  -- The peer's RST: the writes end with a reset, which wakes the parked
  -- writers (owned contract 7), the reads end with a reset, and the
  -- entry leaves.
  let rst := feed client [.openStream 0, .write ⟨1, 0⟩ 1 ⟨fill (initialWindow + 1)⟩, bytesEvent (wf rstFlags 1)]
  r.check "core: the peer's RST ends the stream with a reset"
    (match rst with
      | .ok (s, a) => s.streams.isEmpty && a.contains (.endWrites 1 .reset) && a.contains (.reset 1)
      | _ => false)
  let own := feed client [.openStream 0, .reset ⟨1, 0⟩]
  r.check "core: our reset sends RST and ends the stream"
    (match own with
      | .ok (s, a) => s.streams.isEmpty && a.contains (.endWrites 1 .reset) &&
          a.contains (.send (windowFrame rstFlags 1)) && a.contains (.reset 1)
      | _ => false)
  -- Data after the peer's FIN: no error, charged to the window, as go,
  -- rust, and js do; the reader already has its EOF, so it passes by.
  r.check "core: data after the peer's FIN is no error, and is charged to the window"
    (match feed server [bytesEvent (wf synFin 1), bytesEvent (df Flags.none 1 (b "x"))] with
      | .ok (s, a) => delivered a == .empty &&
          (s.streams.map (·.state.recvWindow)) == [initialWindow - 1]
      | .error _ => false)
  -- While the EOF still waits behind held bytes, late data joins them.
  let tiny := (List.range inboxChunks).map fun _ => bytesEvent (df Flags.none 1 (b "a"))
  r.check "core: data after the FIN joins the held bytes ahead of the EOF"
    (match feed server ([bytesEvent (wf synFlags 1)] ++ tiny ++ [bytesEvent (df finFlags 1 (b "b")),
        bytesEvent (df Flags.none 1 (b "c")), .consumed ⟨1, 0⟩ 1] ) with
      | .ok (_, a) => a.drop (a.length - 2) == [.deliver 1 ⟨b "bc"⟩, .eof 1]
      | .error _ => false)
  -- An RST after the FIN, while the EOF still waits behind held bytes:
  -- the RST ends the write direction only, and a read then hands over
  -- the held bytes and the EOF, as go-yamux and rust-yamux do.
  let held := [bytesEvent (wf synFlags 1)] ++ tiny ++ [bytesEvent (df finFlags 1 (b "b"))]
  r.check "core: an RST after the FIN ends the writes only, while the EOF waits"
    (match feed server (held ++ [bytesEvent (wf rstFlags 1)]) with
      | .ok (s, a) => a.contains (.endWrites 1 .reset) && !a.contains (.reset 1) &&
          s.streams.length == 1
      | .error _ => false)
  r.check "core: after that RST, a read hands over the held bytes and the EOF"
    (match feed server (held ++ [bytesEvent (wf rstFlags 1), .consumed ⟨1, 0⟩ 1]) with
      | .ok (_, a) => a.drop (a.length - 2) == [.deliver 1 ⟨b "b"⟩, .eof 1]
      | .error _ => false)

private def coreSessionChecks (r : Runner) : IO Unit := do
  -- The inbound cap: the peer's live stream past `maxIncomingStreams` is
  -- refused with RST, and the session stays.
  let syns := (List.range (maxIncomingStreams + 1)).map fun i => bytesEvent (wf synFlags (2 * i + 1))
  match feed server syns with
  | .ok (s, a) =>
    r.check "core: the peer's live streams stop at the inbound cap"
      (s.streams.length == maxIncomingStreams &&
        (a.filter fun x => match x with | .accept _ => true | _ => false).length == maxIncomingStreams)
    r.check "core: a SYN beyond the inbound cap is refused with RST"
      (a.getLast? == some (.reply (windowFrame rstFlags (2 * maxIncomingStreams + 1))))
  | .error _ => r.check "core: the peer's live streams stop at the inbound cap" false
  -- Pings: the peer's ping is echoed as a control frame, and ours is
  -- answered by value.
  r.check "core: a ping SYN is echoed with ACK"
    (actionsOf (feed server [bytesEvent (pf synFlags 42)]) == some [.control (frame .ping ackFlags 0 42)])
  r.check "core: our ping is answered by its value"
    (actionsOf (feed server [.ping 5, bytesEvent (pf ackFlags 0)]) ==
      some [.send (frame .ping synFlags 0 0), .wakeAt pingDeadlineMs, .done 5])
  -- Time (module doc of `Yamux/Core.lean`, "Time"). Our ping asks for
  -- a tick at its deadline, and fails with `timeout` at that tick, not
  -- before.
  let pinged := [.tick 1000, .ping 5]
  r.check "core: a ping asks for a tick at its deadline"
    (actionsOf (feed server pinged) ==
      some [.send (frame .ping synFlags 0 0), .wakeAt (1000 + pingDeadlineMs)])
  r.check "core: a ping is not late before its deadline"
    (match feed server (pinged ++ [.tick (1000 + pingDeadlineMs - 1)]) with
      | .ok (_, a) => !a.contains (.refused 5 .timeout)
      | _ => false)
  r.check "core: a ping that no pong answers fails with timeout at its deadline"
    (match feed server (pinged ++ [.tick (1000 + pingDeadlineMs)]) with
      | .ok (s, a) => a.contains (.refused 5 .timeout) && s.pings.isEmpty
      | _ => false)
  -- The keepalive: after the interval with no bytes from the peer, a
  -- ping goes out; with no pong in time, the session ends.
  let kept := State.new .server (keepalive := some keepaliveIntervalMs)
  r.check "core: no keepalive before the interval"
    (match feed kept [.tick 0, .tick (keepaliveIntervalMs - 1)] with
      | .ok (_, a) => a == [.wakeAt keepaliveIntervalMs]
      | _ => false)
  let probe := [.tick 0, .tick keepaliveIntervalMs]
  r.check "core: after the interval a keepalive ping goes out"
    (match feed kept probe with
      | .ok (_, a) => a.contains (.send (frame .ping synFlags 0 0)) &&
          a.getLast? == some (.wakeAt (keepaliveIntervalMs + pingDeadlineMs))
      | _ => false)
  r.check "core: a keepalive with no pong in time ends the session"
    (match feed kept (probe ++ [.tick (keepaliveIntervalMs + pingDeadlineMs)]) with
      | .ok (_, a) => a.contains .expired
      | _ => false)
  r.check "core: a pong in time keeps the session"
    (match feed kept (probe ++ [.tick (keepaliveIntervalMs + 5), bytesEvent (pf ackFlags 0),
        .tick (keepaliveIntervalMs + pingDeadlineMs)]) with
      | .ok (s, a) => !a.contains .expired && s.pings.isEmpty
      | _ => false)
  -- Bytes from the peer restart the interval, as in go-yamux.
  r.check "core: bytes from the peer restart the keepalive interval"
    (match feed kept [.tick 0, .tick 20000, bytesEvent (pf synFlags 7), .tick keepaliveIntervalMs] with
      | .ok (_, a) => !a.contains (.send (frame .ping synFlags 0 0)) &&
          a.contains (.wakeAt (20000 + keepaliveIntervalMs))
      | _ => false)
  -- Go-away, each code.
  r.check "core: a normal go-away shuts the session down"
    (actionsOf (feed server [bytesEvent (gf 0)]) == some [.shutdown])
  r.check "core: a go-away with the protocol-error code ends the session with it"
    (errs (.goAway .protocolError) (feed server [bytesEvent (gf 1)]))
  r.check "core: a go-away with the internal-error code ends the session with it"
    (errs (.goAway .internalError) (feed server [bytesEvent (gf 2)]))
  r.check "core: a go-away with an unknown code is an error"
    (errs (.unknownGoAwayCode 7) (feed server [bytesEvent (gf 7)]))
  r.check "core: a malformed header is an error"
    (errs .malformedHeader (feed server [bytesEvent (Bytes.ofNatList [1, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 3])]))
  -- Our go-away: no stream opens on either side after it.
  match feed server [.openStream 0, .goAway, .openStream 1, bytesEvent (wf synFlags 1)] with
  | .ok (_, a) =>
    r.check "core: after our go-away, opens are refused and SYNs reset"
      (a.contains (.send (goAwayFrame .normal)) && a.contains (.openRefused 1 .closed) &&
        a.contains (.reply (windowFrame rstFlags 1)) &&
        a.all fun x => match x with | .accept _ => false | _ => true)
  | .error _ => r.check "core: after our go-away, opens are refused and SYNs reset" false
  -- Bytes split anywhere give the same session: one byte per event.
  let wire := wf synFlags 1 ++ df Flags.none 1 (b "hello") ++ pf synFlags 9 ++ df finFlags 1 (b "!")
  let whole := feed server [bytesEvent wire]
  let bytewise := feed server ((List.range wire.size).map fun i => bytesEvent (wire.extract i (i + 1)))
  -- The chunk count differs, so the inbox slots differ; the streams,
  -- the other actions, and the bytes do not.
  r.check "core: one byte per event gives the same actions and bytes"
    (match whole, bytewise with
      | .ok (s1, a1), .ok (s2, a2) =>
        s1.streams.map (·.id.val) == s2.streams.map (·.id.val) &&
          notDelivered a1 == notDelivered a2 && (delivered a1).toList == (delivered a2).toList
      | _, _ => false)

/-- The bounded inbox: a reader that stalls holds at most `inboxChunks`
chunks in its inbox, and the rest waits in the core, joined. -/
private def coreInboxChecks (r : Runner) : IO Unit := do
  let tiny := (List.range (inboxChunks + 9)).map fun i => bytesEvent (df Flags.none 1 (fill 1 (UInt8.ofNat i)))
  let deliveries (a : List Action) : Nat :=
    (a.filter fun x => match x with | .deliver _ _ => true | _ => false).length
  match feed server ([bytesEvent (wf synFlags 1)] ++ tiny) with
  | .ok (s, a) =>
    r.check "core: a stalled reader gets at most the inbox's chunks"
      (deliveries a == inboxChunks)
    r.check "core: the bytes past the inbox wait in the core, joined, within the window"
      (match s.streams with
        | [e] => e.state.held.bytes.size == 9 && e.state.slots == inboxChunks &&
            e.state.unread == inboxChunks + 9
        | _ => false)
  | .error _ => r.check "core: a stalled reader gets at most the inbox's chunks" false
  -- One read frees one slot: the held bytes move in as one chunk, in
  -- order.
  match feed server ([bytesEvent (wf synFlags 1)] ++ tiny ++ [.consumed ⟨1, 0⟩ 1]) with
  | .ok (_, a) =>
    r.check "core: a freed slot takes the held bytes as one chunk, in order"
      (match a.getLast? with
        | some (.deliver 1 p) => p.bytes.toList == (List.range 9).map fun i => UInt8.ofNat (inboxChunks + i)
        | _ => false)
  | .error _ => r.check "core: a freed slot takes the held bytes as one chunk, in order" false
  -- A FIN behind held bytes: the EOF waits for them, and the stream stays
  -- in the table until they are handed over.
  match feed server ([bytesEvent (wf synFlags 1)] ++ tiny ++ [bytesEvent (wf finFlags 1), .close ⟨1, 0⟩]) with
  | .ok (s, a) =>
    r.check "core: the EOF waits behind the held bytes"
      (!a.contains (.eof 1) && s.streams.length == 1)
  | .error _ => r.check "core: the EOF waits behind the held bytes" false
  match feed server ([bytesEvent (wf synFlags 1)] ++ tiny ++ [bytesEvent (wf finFlags 1), .close ⟨1, 0⟩,
      .consumed ⟨1, 0⟩ 1]) with
  | .ok (s, a) =>
    r.check "core: the held bytes, then the EOF, and the stream retires"
      ((a.drop (a.length - 2)) == [.deliver 1 ⟨(Bytes.ofNatList ((List.range 9).map (inboxChunks + ·)))⟩, .eof 1] &&
        s.streams.isEmpty)
  | .error _ => r.check "core: the held bytes, then the EOF, and the stream retires" false
  -- A whole window of 1-byte frames to a reader that never reads: every
  -- frame past the inbox joins the held chunk. The join appends in place
  -- while the state has one reference, so this runs in linear time. If a
  -- change ever shares the state, each join copies the held bytes, and
  -- this check runs for hours: the suite hangs here.
  let one := bytesEvent (df Flags.none 1 (fill 1))
  let mut s := server
  let mut ok := true
  for ev in bytesEvent (wf synFlags 1) :: List.replicate initialWindow one do
    match step s ev with
    | .ok (s', _) => s := s'
    | .error _ => ok := false
  r.check "core: a window of 1-byte frames joins into the held chunk"
    (ok && match s.streams with
      | [e] => e.state.held.bytes.size == initialWindow - inboxChunks &&
          e.state.slots == inboxChunks && e.state.unread == initialWindow
      | _ => false)

/-! ## The control queue cap -/

/-- A multiaddr from its text form. -/
private def ma (s : String) : Async Multiformats.Multiaddr := do
  match Multiformats.Multiaddr.parse? s with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"test address {s} does not parse"

/-- A connected pair over a fresh sim net: the dialer's end and the
listener's end. -/
private def pair (split : Bool := false) : Async (Connection × Connection) := do
  let net ← Sim.Net.new split
  let l ← net.transport.listen (← ma "/ip4/127.0.0.1/tcp/4001")
  let some c ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
  let some s ← l.accept | throw <| IO.userError "accept failed"
  l.close
  return (c, s)

/-- The shared parts of a session over `conn`, built as `Session.new`
builds them, for the tests that drive one task by hand. -/
private def shared (conn : Connection) : BaseIO Shared := do
  return {
    conn
    clock := Clock.system
    events := ← Chan.new eventQueueCap
    out := ← Chan.newUnbounded
    controlCount := ← OnceRef.new 0
    room := ← Chan.new 1
    writes := ← Completions.new
    attempts := ← OnceRef.new ({}, false)
    opens := ← Completions.new
    accepts := ← Chan.new backlogCap
    credits := ← Chan.new 1
    alarm := ← Alarm.new
    outcome := ← Outcome.new
    peerGoAway := ← OnceRef.new false
    ownerEnded := ← OnceRef.new false }

/-- A ping flood leaves the control queue at its cap: the shell drops
the control frames beyond it. -/
private def controlCapChecks (r : Runner) : Async Unit := do
  let (conn, peer) ← pair
  let sh ← shared conn
  let echo := Action.control (frame .ping ackFlags 0 1)
  let mut p : Ports := {}
  for _ in [0:3 * controlQueueCap] do
    p ← sh.performOne p echo
  let queued ← sh.out.drain
  r.check "a ping flood leaves the control queue at its cap"
    (queued.length == controlQueueCap && (← sh.controlCount.get) == controlQueueCap)
  -- A frame the core must send is never dropped.
  discard <| sh.performOne p (.send (windowFrame finFlags 1))
  r.check "a frame that must go out passes the full control queue"
    ((← sh.out.drain).length == 1)
  -- The answer to a SYN is never dropped either: past the cap it is
  -- queued and counted, and the count makes the loop wait.
  for _ in [0:5] do
    p ← sh.performOne p (.reply (windowFrame rstFlags 1))
  r.check "SYN answers past the cap are kept, and counted for back-pressure"
    ((← sh.out.drain).length == 5 && (← sh.controlCount.get) == controlQueueCap + 5)
  conn.close
  peer.close

/-- Past the control cap, the loop waits until the writer has sent
enough SYN answers, and only then returns the reader's credit and takes
the next event (owned contract 5). The writes of the connection wait at
`gate` until the test opens it, and the check is that the wait ends:
the credit comes, and so does the answer to an open posted behind the
SYNs. -/
private def synBackPressureChecks (r : Runner) : Async Unit := do
  let (conn, peer) ← pair
  let gate : Chan Unit ← Chan.new 1
  let sh ← shared { conn with write := fun bytes => do discard gate.recv; conn.write bytes }
  let tasks ← TaskSet.new
  -- The peer reads everything, so only the gate holds the writer. Its
  -- read ends when the writer closes the connection.
  tasks.spawn do
    repeat
      if (← peer.read).isNone then break
  tasks.spawn do
    let (ending, p) ← sh.run .server none
    sh.teardown ending p
  tasks.spawn sh.writer
  -- One read of SYNs, two past the cap, then an open behind them.
  let syns := (List.range (controlQueueCap + 2)).foldl
    (fun acc i => acc ++ wf synFlags (2 * i + 1)) ByteArray.empty
  discard <| sh.events.send (.bytes ⟨syns⟩)
  let some (tag, slot) ← sh.opens.register | throw <| IO.userError "register failed"
  discard <| sh.events.send (.openStream tag)
  -- The writer sends the answers, and the wait ends.
  gate.close
  r.check "SYN back-pressure: the reader gets its credit once the writer catches up"
    ((← sh.credits.recv).isSome)
  r.check "SYN back-pressure: the loop takes the next event after the wait"
    (match ← slot.recv with | some (.ok _) => true | _ => false)
  sh.events.close
  tasks.joinAll
  conn.close
  peer.close

/-- The reader reads one read ahead of the loop. It takes a credit
before each read, and the loop returns the credit once it has stepped
the bytes. The test plays the loop. When the `i`-th read arrives, the
reader has made exactly `i` reads, so no read waits in the queue
uncharged to a window. -/
private def readAheadChecks (r : Runner) : Async Unit := do
  let (conn, peer) ← pair
  let chunks := 8
  let reads : OnceRef Nat ← OnceRef.new 0
  -- `chunks` reads of one byte each, then the end of the connection.
  let src : Connection := { conn with
    read := do
      -- The ascription marks the update `BaseIO`, so the lift into
      -- `Async` applies (see `Conc.TaskSet.joinAll`).
      let n ← (reads.updateGet (fun n => (n + 1, n + 1)) : BaseIO Nat)
      return if n ≤ chunks then some (fill 1 0) else none }
  let sh ← shared src
  discard <| sh.credits.trySend ()
  let tasks ← TaskSet.new
  tasks.spawn sh.reader
  -- The next event other than a tick: the reader posts one before the
  -- bytes of each read.
  let nextEvent : Async (Option Event) := do
    repeat
      match ← sh.events.recv with
      | some (.tick _) => pure ()
      | other => return other
    return none
  let mut exact := true
  for i in [1:chunks + 1] do
    match ← nextEvent with
    | some (.bytes _) => exact := exact && (← reads.get) == i
    | _ => exact := false
    discard <| sh.credits.trySend ()
  r.check "the reader reads no further ahead than the read the loop takes" exact
  r.check "the end of the connection follows the last read"
    (match ← nextEvent with | some .eof => true | _ => false)
  tasks.joinAll
  conn.close
  peer.close

/-! ## Sessions over the sim (unit 1b) -/

/-- Every byte of a stream until its end: the bytes, and the error that
ended it, if any. -/
private def readAll (s : Stream) : Async (ByteArray × Option Streams.Error) := do
  let mut acc := ByteArray.empty
  repeat
    match ← s.read with
    | .ok (some c) => acc := acc ++ c
    | .ok none => return (acc, none)
    | .error e => return (acc, some e)
  return (acc, none)

/-- One frame off a raw connection: the header, the payload of a data
frame, and the bytes read past it. `none` at the end. -/
private def readFrame (c : Connection) (pending : ByteArray) :
    Async (Option (Header × ByteArray × ByteArray)) := do
  let some (hb, rest) ← c.readExactly headerSize pending | return none
  match Header.decodeB? hb with
  | .error _ => throw <| IO.userError "test: the session sent a malformed header"
  | .ok (h, _) =>
    if h.type == .data && h.length > 0 then
      let some (body, rest) ← c.readExactly h.length rest | return none
      return some (h, body, rest)
    else return some (h, .empty, rest)

/-- Every frame off a raw connection until its end. -/
private def readFrames (c : Connection) (pending : ByteArray := .empty) : Async (List Header) := do
  let mut out : Array Header := #[]
  let mut pending := pending
  repeat
    match ← readFrame c pending with
    | some (h, _, rest) =>
      out := out.push h
      pending := rest
    | none => break
  return out.toList

/-- Frames off a raw connection up to the echo of our ping of `value`:
the session has then taken every byte we sent before the ping. -/
private def syncPing (c : Connection) (value : Nat) : Async (List Header × ByteArray) := do
  c.write (pf synFlags value)
  let mut seen : Array Header := #[]
  let mut pending := ByteArray.empty
  repeat
    match ← readFrame c pending with
    | some (h, _, rest) =>
      pending := rest
      if h.type == .ping && h.flags.ack && h.length == value then break
      seen := seen.push h
    | none => throw <| IO.userError "test: the session ended before the ping echo"
  return (seen.toList, pending)

private def echoChecks (r : Runner) : Async Unit := do
  for split in [false, true] do
    let tag := if split then " (byte-splitting)" else ""
    let (c, s) ← pair split
    let client ← Session.new .client c
    let server ← Session.new .server s
    let .ok cs ← client.openStream | throw <| IO.userError "open failed"
    discard <| cs.write (b "hello")
    -- Half-close (§5.3): our FIN ends our direction only.
    cs.close
    let some ss ← server.acceptStream | throw <| IO.userError "accept failed"
    let (got, err) ← readAll ss
    r.check s!"session: the request arrives whole, then EOF{tag}"
      (got.toList == (b "hello").toList && err.isNone)
    -- The response after our FIN still arrives.
    let wrote ← ss.write (b "world")
    ss.close
    let (resp, err) ← readAll cs
    r.check s!"session: the response after our FIN still arrives{tag}"
      (resp.toList == (b "world").toList && err.isNone && (match wrote with | .ok () => true | _ => false))
    r.check s!"session: a ping returns{tag}"
      (match ← client.ping with | .ok () => true | _ => false)
    client.close
    -- The peer's go-away ends the server, which reads no more streams.
    r.check s!"session: after the peer closes, accept answers none{tag}"
      ((← server.acceptStream).isNone)
    r.check s!"session: the closing side joins cleanly{tag}"
      (match ← client.join with | .ok () => true | _ => false)
    r.check s!"session: the peer of a closed session joins cleanly{tag}"
      (match ← server.join with | .ok () => true | _ => false)
    r.check s!"session: an open after the end answers closed{tag}"
      (match ← client.openStream with | .error .closed => true | _ => false)

/-- A transfer past the window: the writer parks on credit, and the
reader's consumption returns it. -/
private def transferChecks (r : Runner) : Async Unit := do
  let (c, s) ← pair
  let client ← Session.new .client c
  let server ← Session.new .server s
  let size := 4 * initialWindow + 12345
  let payload : ByteArray := ⟨(Array.range size).map fun i => UInt8.ofNat (i % 251)⟩
  let .ok cs ← client.openStream | throw <| IO.userError "open failed"
  let tasks ← TaskSet.new
  let wrote : OnceRef Bool ← OnceRef.new false
  tasks.spawn do
    if let .ok () ← cs.write payload then wrote.set true
    cs.close
  let some ss ← server.acceptStream | throw <| IO.userError "accept failed"
  let (got, err) ← readAll ss
  tasks.joinAll
  r.check "session: a transfer of four windows arrives whole and in order"
    (got == payload && err.isNone)
  r.check "session: the large write completes" (← wrote.get)
  -- Both directions at once: each side writes a window and a half, and
  -- reads the other's.
  let .ok cs2 ← client.openStream | throw <| IO.userError "open failed"
  let some ss2 ← server.acceptStream | throw <| IO.userError "accept failed"
  let half := fill (initialWindow + initialWindow / 2) 3
  tasks.spawn do discard <| cs2.write half; cs2.close
  tasks.spawn do discard <| ss2.write half; ss2.close
  let (a, _) ← readAll cs2
  let (b', _) ← readAll ss2
  tasks.joinAll
  r.check "session: both directions past the window at once"
    (a.size == half.size && b'.size == half.size)
  client.close
  server.close
  discard client.join
  discard server.join

/-- Read data frames off a raw connection until `n` payload bytes have
arrived: the bytes read past them. -/
private def readData (c : Connection) (n : Nat) : Async ByteArray := do
  let mut got := 0
  let mut pending := ByteArray.empty
  while got < n do
    match ← readFrame c pending with
    | some (h, body, rest) =>
      if h.type == .data then got := got + body.size
      pending := rest
    | none => throw <| IO.userError "test: the session ended before the data"
  return pending

/-- The parked writers (owned contracts 4 and 7). Two writers past the
window both finish: the grants reach each in turn. A writer parked on
credit wakes when the write direction ends: with `reset` on the peer's
RST, and with `closed` on our own close. In the last two, the raw peer
has the whole window before it acts, so the loop has stepped the write
that parked the writer. -/
private def parkedWriterChecks (r : Runner) : Async Unit := do
  -- Two writers on one stream, each a window and a half.
  do
    let (c, s) ← pair
    let client ← Session.new .client c
    let server ← Session.new .server s
    let .ok cs ← client.openStream | throw <| IO.userError "open failed"
    let part := fill (initialWindow + initialWindow / 2) 5
    let tasks ← TaskSet.new
    let done : OnceRef Nat ← OnceRef.new 0
    for _ in [0:2] do
      tasks.spawn do
        if let .ok () ← cs.write part then done.update (· + 1)
    let some ss ← server.acceptStream | throw <| IO.userError "accept failed"
    let mut got := 0
    while got < 2 * part.size do
      match ← ss.read with
      | .ok (some chunk) => got := got + chunk.size
      | _ => break
    tasks.joinAll
    r.check "parked writers: two writers past the window both finish"
      ((← done.get) == 2 && got == 2 * part.size)
    client.close
    server.close
    discard client.join
    discard server.join
  -- A parked writer wakes with `reset` on the peer's RST, and with
  -- `closed` on our close.
  for (byClose, want) in [(false, Streams.Error.reset), (true, .closed)] do
    let (c, raw) ← pair
    let client ← Session.new .client c
    let .ok cs ← client.openStream | throw <| IO.userError "open failed"
    let answer : OnceRef (Option (Except Streams.Error Unit)) ← OnceRef.new none
    let tasks ← TaskSet.new
    tasks.spawn do answer.set (some (← cs.write (fill (initialWindow + 1000))))
    discard <| readData raw initialWindow
    if byClose then cs.close else raw.write (wf rstFlags 1)
    tasks.joinAll
    let how := if byClose then "our close" else "the peer's RST"
    r.check s!"parked writers: a parked writer wakes on {how}"
      (match ← answer.get with | some (.error e) => e == want | _ => false)
    client.close
    discard client.join
    raw.close

/-- The negotiation leftover is the first event of the loop (§4.7). -/
private def leftoverChecks (r : Runner) : Async Unit := do
  let (c, s) ← pair
  -- The peer's SYN and data arrived with the negotiation: the session
  -- takes them as data, before any read.
  let server ← Session.new .server s (wf synFlags 1 ++ df finFlags 1 (b "early"))
  let some ss ← server.acceptStream | throw <| IO.userError "accept failed"
  let (got, err) ← readAll ss
  r.check "session: the leftover opens the stream and delivers its bytes"
    (got.toList == (b "early").toList && err.isNone)
  c.close
  r.check "session: the end of the connection ends the session cleanly"
    (match ← server.join with | .ok () => true | _ => false)

/-- A write whose frame goes out after the loop has ended answers `.ok`.
The client's connection reads park until the test closes `fin`, then
end, as after a peer FIN, while its writes still reach the server. Once
`armed` is set, the writes wait at `gate`, so the write's frame is still
queued when the teardown runs. -/
private def writeAcrossEndChecks (r : Runner) : Async Unit := do
  let (c, s) ← pair
  let fin : Chan Unit ← Chan.new 1
  let gate : Chan Unit ← Chan.new 1
  let armed : OnceRef Bool ← OnceRef.new false
  let c' : Connection := { c with
    read := do discard fin.recv; return none
    write := fun bytes => do
      if ← (armed.get : BaseIO Bool) then discard gate.recv
      c.write bytes }
  let client ← Session.new .client c'
  let server ← Session.new .server s
  let .ok cs ← client.openStream | throw <| IO.userError "open failed"
  armed.set true
  let tasks ← TaskSet.new
  let wrote : OnceRef Bool ← OnceRef.new false
  tasks.spawn do
    if let .ok () ← cs.write (b "late") then wrote.set true
  -- The end of the reads ends the loop; the teardown closes the accept
  -- queue, so this accept answers `none` only after the teardown.
  fin.close
  r.check "session: the reader's end ends the session" ((← client.acceptStream).isNone)
  gate.close
  tasks.joinAll
  r.check "session: a write whose frame went out after the end answers ok" (← wrote.get)
  let some ss ← server.acceptStream | throw <| IO.userError "accept failed"
  let (got, _) ← readAll ss
  r.check "session: the peer reads the bytes of that write" (got.toList == (b "late").toList)
  client.close
  server.close
  discard client.join
  -- The client's session ended at the end of its reads, with no
  -- go-away, and its writer then closed the connection. A frame that the
  -- server still writes after that close fails, and a session that ends
  -- at the end of the connection reports a failed write as a fault
  -- (`Yamux.Shared.recordWriteFault`). So the server's join answers the
  -- fault in some orders of the tasks; the checks above do not read it.
  discard <| (try server.join catch _ => pure (.ok ()))

/-- What the reads see at an RST (`Yamux/Loop.lean`, "The reset"). With
the read direction open, the RST drops the bytes the reader has not
taken, and the next read answers `reset`, as in go-yamux. After the
peer's FIN, the RST leaves the reads alone: they drain to EOF, as in
go-yamux and rust-yamux. Each ping echo shows the session has stepped
the frames before it. -/
private def resetReadChecks (r : Runner) : Async Unit := do
  for afterFin in [false, true] do
    let (raw, s) ← pair
    let server ← Session.new .server s
    let fl := if afterFin then finFlags else Flags.none
    raw.write (wf synFlags 1 ++ df fl 1 (b "a"))
    let _ ← syncPing raw 1
    raw.write (wf rstFlags 1)
    let _ ← syncPing raw 2
    let some ss ← server.acceptStream | throw <| IO.userError "accept failed"
    let (got, err) ← readAll ss
    if afterFin then
      r.check "session: an RST after the peer's FIN leaves the reads to drain to EOF"
        (got.toList == (b "a").toList && err.isNone)
    else
      r.check "session: an RST drops the unread bytes, and the read answers reset"
        (got.isEmpty && err == some .reset)
    server.close
    discard server.join
    raw.close

/-! ## A session against a raw hostile peer -/

private def hostileChecks (r : Runner) : Async Unit := do
  -- Data beyond the window: the session tears down, sends a go-away
  -- with the protocol-error code, and buffers nothing past the window.
  do
    let (raw, s) ← pair
    let server ← Session.new .server s
    -- The stream and its full window first; the ping echo shows the
    -- session has taken them. A step that fails drops the actions of
    -- its whole event, so the stream must exist before the bad frame.
    raw.write (wf synFlags 1 ++ df Flags.none 1 (fill initialWindow))
    let (_, pending) ← syncPing raw 1
    let some ss ← server.acceptStream | throw <| IO.userError "accept failed"
    raw.write (df Flags.none 1 (b "x"))
    r.check "hostile: data beyond the window ends the session with the error"
      (match ← server.join with | .error (.windowExceeded 1 1 0) => true | _ => false)
    let frames ← readFrames raw pending
    r.check "hostile: the session sends a go-away with the protocol-error code"
      (frames.any fun h => h.type == .goAway && h.length == GoAwayCode.protocolError.toCode)
    let (got, err) ← readAll ss
    r.check "hostile: nothing past the window reaches the stream"
      (got.size == initialWindow && err == some .closed)
  -- Many tiny frames to a reader that has not read yet: the bounded
  -- inbox fills, the rest waits in the core, and every byte arrives in
  -- order before the EOF.
  do
    let (raw, s) ← pair
    let server ← Session.new .server s
    let bytes := (List.range 100).map fun i => UInt8.ofNat i
    let frames := bytes.foldl (fun acc x => acc ++ df Flags.none 1 ⟨#[x]⟩) (wf synFlags 1)
    raw.write (frames ++ wf finFlags 1)
    let _ ← syncPing raw 3
    let some ss ← server.acceptStream | throw <| IO.userError "accept failed"
    let (got, err) ← readAll ss
    r.check "hostile: tiny frames past the inbox arrive whole and in order, then EOF"
      (got.toList == bytes && err.isNone)
    server.close
    discard server.join
    raw.close
  -- A SYN with the wrong parity ends the session with a protocol-error
  -- go-away, as at go-yamux and rust-yamux, and opens no stream.
  do
    let (raw, s) ← pair
    let server ← Session.new .server s
    raw.write (wf synFlags 2 ++ df Flags.none 2 (b "bad"))
    r.check "hostile: a SYN with the wrong parity ends the session with the error"
      (match ← server.join with | .error (.invalidStreamId 2) => true | _ => false)
    r.check "hostile: a SYN with the wrong parity opens no stream"
      ((← server.acceptStream).isNone)
    let frames ← readFrames raw
    r.check "hostile: a SYN with the wrong parity draws a protocol-error go-away"
      (frames.any fun h => h.type == .goAway && h.length == GoAwayCode.protocolError.toCode)
    raw.close
  -- Frames for an unknown id create no state, and a later open of that
  -- id works.
  do
    let (c, raw) ← pair
    let client ← Session.new .client c
    raw.write (df Flags.none 1 (b "stray") ++ wf Flags.none 1 99 ++ wf finFlags 3)
    let (before, pending) ← syncPing raw 7
    r.check "hostile: frames for an unknown id draw no answer" before.isEmpty
    let .ok cs ← client.openStream | throw <| IO.userError "open failed"
    let some (h, _, _) ← readFrame raw pending | throw <| IO.userError "no SYN"
    r.check "hostile: a later open of that id sends its SYN"
      (h.type == .windowUpdate && h.flags.syn && h.streamId == 1)
    raw.write (df finFlags 1 (b "fresh"))
    let (got, _) ← readAll cs
    r.check "hostile: the opened stream reads only its own data"
      (got.toList == (b "fresh").toList)
    client.close
    discard client.join
    raw.close
  -- A full accept queue: the peer opens and resets `backlogCap` streams
  -- that the application never takes, so each one still holds its place.
  -- The next stream is reset at the offer, and the wire carries its ACK
  -- first, then the RST: an accept, then a reset.
  do
    let (raw, s) ← pair
    let server ← Session.new .server s
    let held := (List.range backlogCap).foldl
      (fun acc i => acc ++ wf synFlags (2 * i + 1) ++ wf rstFlags (2 * i + 1)) ByteArray.empty
    let last := 2 * backlogCap + 1
    raw.write (held ++ wf synFlags last)
    let (frames, _) ← syncPing raw 11
    r.check "hostile: a stream past the full accept queue gets its ACK, then the RST"
      ((frames.filter (·.streamId == last)).map (fun h => (h.flags.ack, h.flags.rst)) ==
        [(true, false), (false, true)])
    server.close
    discard server.join
    raw.close
  -- A handle of a retired stream, after the peer reopens its id. The old
  -- stream holds two unread chunks when it retires. The new stream on
  -- id 1 takes two chunks, and then the old handle reads its own two,
  -- posting two counts, and resets. If the counts reached the new
  -- stream, the core would count two slots too few, and with
  -- `inboxChunks` more chunks the real inbox would overflow and drop
  -- bytes. The reset would send an RST on id 1.
  do
    let (raw, s) ← pair
    let server ← Session.new .server s
    raw.write (wf synFlags 1 ++ df Flags.none 1 (b "a") ++ df finFlags 1 (b "b"))
    let _ ← syncPing raw 21
    let some old ← server.acceptStream | throw <| IO.userError "accept failed"
    -- Our FIN after the peer's: the stream retires with its chunks unread.
    old.close
    let _ ← syncPing raw 22
    raw.write (wf synFlags 1 ++ df Flags.none 1 (b "n1") ++ df Flags.none 1 (b "n2"))
    let _ ← syncPing raw 23
    let some fresh ← server.acceptStream | throw <| IO.userError "accept failed"
    let (oldBytes, oldErr) ← readAll old
    old.reset
    let (seen, _) ← syncPing raw 24
    r.check "hostile: the old handle reads its own bytes after the id is reused"
      (oldBytes.toList == (b "ab").toList && oldErr.isNone)
    r.check "hostile: the old handle's reset sends nothing on the reused id"
      (seen.all fun h => !(h.streamId == 1 && h.flags.rst))
    let tiny := (List.range inboxChunks).map fun i => UInt8.ofNat (65 + i)
    raw.write (tiny.foldl (fun acc x => acc ++ df Flags.none 1 ⟨#[x]⟩) .empty ++ wf finFlags 1)
    let _ ← syncPing raw 25
    let (got, err) ← readAll fresh
    r.check "hostile: the new stream on the reused id loses no byte to the old handle"
      (got.toList == (b "n1n2").toList ++ tiny && err.isNone)
    server.close
    discard server.join
    raw.close
  -- A peer that sends pings and never reads: the echoes fill the
  -- connection, the writer parks, and the write deadline ends the
  -- session with a fault. Each echo is one write, and the writer arms the
  -- timer of a write only after the write before it has returned. So when
  -- the timer of write `simPipeChunks + 1` is armed, the first
  -- `simPipeChunks` writes filled the sim pipe, and this one is parked.
  -- Only then does the clock move.
  do
    let tc ← TestClock.new
    let (raw, s) ← pair
    -- No keepalive: its ticker would arm timers of its own, and this
    -- check counts the writer's.
    let server ← Session.new .server s (clock := tc.clock) (keepalive := none)
    raw.write ((List.range (2 * simPipeChunks)).foldl (fun acc i => acc ++ pf synFlags i) .empty)
    let answer : OnceRef String ← OnceRef.new ""
    let ts ← TaskSet.new
    ts.spawn do
      let res ← try
          match ← server.join with
          | .ok () => pure "clean"
          | .error e => pure s!"protocol error {repr e}"
        catch
          | .timeExpired .. => pure "expired"
          | e => pure s!"other: {e}"
      answer.set res
      tc.close
    let mut armed := 0
    for _ in [0:simPipeChunks + 1] do
      if ← tc.nextTimer then armed := armed + 1
    r.check "hostile: the writer parks on a peer that stops reading, and the session waits"
      (armed == simPipeChunks + 1 && (← answer.get) == "")
    tc.advance writeDeadlineMs
    ts.joinAll
    r.check "hostile: the parked write ends the session at the write deadline"
      ((← answer.get) == "expired")
    raw.close
  -- A peer that never answers our keepalive: after the interval the
  -- session pings, and when the pong's deadline passes, it ends with a
  -- fault and no go-away. The ticker reads the time, then arms its timer
  -- for the time left, and the test clock counts that from its own now.
  -- An advance between the two steps would push the timer past the
  -- clock, so each advance waits for the timers it must fire
  -- (`TestClock.nextTimer`).
  do
    let tc ← TestClock.new
    let (raw, s) ← pair
    let server ← Session.new .server s (clock := tc.clock)
    -- The first tick asks for the keepalive tick; the ticker arms it.
    discard tc.nextTimer
    tc.advance keepaliveIntervalMs
    let some (h, _, pending) ← readFrame raw .empty | throw <| IO.userError "no keepalive"
    r.check "hostile: after the interval with no bytes, the session pings"
      (h.type == .ping && h.flags.syn)
    -- The ping arms two timers, in either order: the writer's deadline
    -- for its write, and the ticker's for the pong.
    let writeArmed ← tc.nextTimer
    let pongArmed ← tc.nextTimer
    r.check "hostile: the pong deadline is armed before the clock moves"
      (writeArmed && pongArmed)
    tc.advance pingDeadlineMs
    let res ← try
        match ← server.join with
        | .ok () => pure "clean"
        | .error e => pure s!"protocol error {repr e}"
      catch
        | .timeExpired .. => pure "expired"
        | e => pure s!"other: {e}"
    r.check "hostile: a keepalive with no pong ends the session with a fault"
      (res == "expired")
    r.check "hostile: the keepalive end sends no go-away"
      ((← readFrames raw pending).all fun h => h.type != .goAway)
    tc.close
    raw.close
  -- A go-away with each code ends the session.
  for (code, want) in [(0, (none : Option ProtocolError)), (1, some (.goAway .protocolError)),
      (2, some (.goAway .internalError)), (9, some (.unknownGoAwayCode 9))] do
    let (raw, s) ← pair
    let server ← Session.new .server s
    raw.write (gf code)
    let answer ← server.join
    r.check s!"hostile: a go-away with code {code} ends the session"
      (match answer, want with
        | .ok (), none => true
        | .error e, some w => e == w
        | _, _ => false)
    r.check s!"hostile: after a go-away with code {code}, the connection closes"
      ((← readFrames raw).all fun h => h.type != .data)
    raw.close

def Yamux.run (r : Runner) : IO Unit := do
  r.section "yamux" "(packages/net/yamux/docs/PLAN.md, test milestones, units 1a and 1b)"
  headerChecks r
  coreSynChecks r
  coreWindowChecks r
  coreFlowChecks r
  coreCloseChecks r
  coreSessionChecks r
  coreInboxChecks r
  let all : Async Unit := do
    controlCapChecks r
    synBackPressureChecks r
    readAheadChecks r
    echoChecks r
    transferChecks r
    parkedWriterChecks r
    leftoverChecks r
    writeAcrossEndChecks r
    resetReadChecks r
    hostileChecks r
  all.run

end Tests
