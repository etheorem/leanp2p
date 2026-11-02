import Tests.Support
import Yamux

/-!
# yamux header suite

Mirrors `vendor/specs/yamux/README.md` (the hashicorp specification):
the 12-byte big-endian layout, the frame-type and flag code points, and
the closed tables of `Yamux/Sets.lean`.

The spec vectors are the unit vectors of the spike suite
(`Tests/Yamux.lean` on the `spike` branch): a data frame, a window
update that opens a stream, a ping, a `GoAway`, and a data frame with
`FIN`. The rejection cases pin the strictness of the decoder, and the
laws of `Yamux/Header.lean` keep the codec honest by construction.
-/

set_option autoImplicit false

namespace Tests.Yamux

open _root_.Yamux

/-- A 32-bit word, for the test fixtures only. -/
private def w32 (n : Nat) (h : n < 4294967296) : Word32 := ⟨n, h⟩

/-- Build a header from its parts, for the fixtures. -/
private def hdr (t : FrameType) (fl : Flags) (sid len : Nat)
    (hs : sid < 4294967296) (hl : len < 4294967296) : Header :=
  { frameType := t, flags := fl, streamId := w32 sid hs, length := w32 len hl }

/-- The flag word with all four bits set, for the fixtures. -/
private def allFlags : Flags := ⟨true, true, true, true⟩

/-- The decoder's answer, as a comparison against an expected value. -/
private def decodesTo (bs : List Nat) (h : Header) : Bool :=
  match Header.decode? bs with
  | .ok (got, rest) => got == h ∧ rest == []
  | .error _ => false

/-- The decoder rejects an input with the given error. -/
private def rejects (bs : List Nat) (e : Yamux.Mock.Bytes.DecodeError) : Bool :=
  match Header.decode? bs with
  | .error got => got == e
  | .ok _ => false

/-- The model bytes of an encoded header equal the fixture bytes. -/
private def encodes (h : Header) (bs : List Nat) : Bool :=
  Header.encode h == bs

/-- Every header of the generated set. The set covers the four frame
types, the two flag extremes, both id parities, and the width limits. -/
private def samples : List Header :=
  [ hdr .data Flags.empty 0 0 (by decide) (by decide),
    hdr .windowUpdate ⟨true, false, false, false⟩ 7 262144 (by decide) (by decide),
    hdr .ping ⟨true, false, false, false⟩ 0 42 (by decide) (by decide),
    hdr .goAway Flags.empty 0 0 (by decide) (by decide),
    hdr .data ⟨false, false, true, false⟩ 3 1 (by decide) (by decide),
    hdr .data allFlags 4294967295 4294967295 (by decide) (by decide),
    hdr .windowUpdate ⟨false, true, false, false⟩ 4 65535 (by decide) (by decide),
    hdr .ping ⟨false, true, false, false⟩ 0 1 (by decide) (by decide),
    hdr .goAway ⟨false, false, false, true⟩ 0 2 (by decide) (by decide) ]

/-- The first `n` bytes of a header, for the truncation cases. -/
private def take (n : Nat) (bs : List Nat) : List Nat := bs.take n

def run (r : Runner) : IO Unit := do
  r.section "yamux"
    "libp2p/specs yamux README (hashicorp spec): header framing and tables"

  -- The five spec vectors.
  r.check "yamux header data"
    (encodes (hdr .data Flags.empty 5 3 (by decide) (by decide))
      [0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 3])
  r.check "yamux header window update syn"
    (encodes (hdr .windowUpdate ⟨true, false, false, false⟩ 7 262144 (by decide) (by decide))
      [0, 1, 0, 1, 0, 0, 0, 7, 0, 4, 0, 0])
  r.check "yamux header ping syn"
    (encodes (hdr .ping ⟨true, false, false, false⟩ 0 42 (by decide) (by decide))
      [0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 42])
  r.check "yamux header goaway"
    (encodes (hdr .goAway Flags.empty 0 0 (by decide) (by decide))
      [0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
  r.check "yamux header data fin"
    (encodes (hdr .data ⟨false, false, true, false⟩ 3 1 (by decide) (by decide))
      [0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 1])

  -- Every sample round-trips through the wire model.
  for h in samples do
    r.check s!"yamux header roundtrip {repr h}" (decodesTo (Header.encode h) h)

  -- The generic codec harness runs once over the sample set.
  r.check "yamux header lawful codec harness"
    (Yamux.Mock.Bytes.checkRoundTrips samples)

  -- A header is consumed off the front of a longer buffer.
  r.check "yamux header suffix kept"
    (match Header.decode? (Header.encode (hdr .ping ⟨true, true, false, false⟩ 0 1
        (by decide) (by decide)) ++ [9, 9]) with
     | .ok (_, rest) => rest == [9, 9]
     | .error _ => false)

  -- A prefix shorter than twelve bytes is truncated, never malformed.
  let full := Header.encode (hdr .data ⟨true, false, false, false⟩ 1 0 (by decide) (by decide))
  for n in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] do
    r.check s!"yamux header truncated {n}" (rejects (take n full) .truncated)

  -- A version other than zero is a protocol error.
  r.check "yamux header bad version" (rejects [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    .malformed)

  -- An unknown frame type is a protocol error.
  r.check "yamux header bad type" (rejects [0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    .malformed)

  -- A flag byte above the four defined bits is a protocol error.
  r.check "yamux header bad flag high byte" (rejects [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    .malformed)
  r.check "yamux header bad flag low byte" (rejects [0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0]
    .malformed)

  -- The model is wider than the wire: a byte above 255 is a protocol
  -- error, never a silent truncation to eight bits.
  r.check "yamux header byte above 255" (rejects [0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 0, 0]
    .malformed)

  -- The flag codec covers all sixteen values and rejects the rest.
  r.check "yamux flags roundtrip"
    ([Flags.toCode ⟨true, true, true, true⟩, Flags.toCode ⟨false, false, false, false⟩]
      == [15, 0])
  r.check "yamux flags decode all"
    ((List.range 16).all fun n => (Flags.ofCode? n).isSome)
  r.check "yamux flags reject above"
    ((Flags.ofCode? 16).isNone)

  -- The closed tables round-trip on every member.
  r.check "yamux frame type table"
    ([FrameType.data, .windowUpdate, .ping, .goAway].all fun t =>
      FrameType.ofCode? (FrameType.toCode t) == some t)
  r.check "yamux goaway table"
    ([GoAwayCode.normal, .protocolError, .internalError].all fun c =>
      GoAwayCode.ofCode? (GoAwayCode.toCode c) == some c)

/-! ## The core state machine -/

namespace CoreTests

open _root_.Yamux.Core

/-- A client that has opened nothing. -/
private def client : State :=
  { role := .client, streams := [], nextId := 1, retired := [], pending := [],
    closing := false }

/-- A header's bytes, for a frame the core reads. -/
private def hdr (t : FrameType) (fl : Flags) (sid : StreamId) (value : Nat) : List Nat :=
  Header.encode (Header.ofParts t fl sid (Word32.ofNat value))

/-- A data frame's bytes. -/
private def dat (sid : StreamId) (fl : Flags) (payload : List Nat) : List Nat :=
  Header.encode (Header.ofParts .data fl sid (Word32.ofNat payload.length)) ++ payload

/-- The actions carry an `opened` for this tag and id. -/
private def openedWith (tag : Nat) (sid : StreamId) (acts : List Action) : Bool :=
  acts.any fun a =>
    match a with
    | .opened t s => t == tag && s.val == sid.val
    | _ => false

/-- The actions carry an `accept` for this id. -/
private def acceptedWith (sid : StreamId) (acts : List Action) : Bool :=
  acts.any fun a =>
    match a with
    | .accept s => s.val == sid.val
    | _ => false

def run (r : Runner) : IO Unit := do
  r.section "yamux core"
    "packages/net/yamux/docs/ARCHITECTURE.md: the pure session state machine"

  -- Opening a stream hands out this side's first id and reports it.
  match step client (.open 7) with
  | .ok (s1, acts) =>
      r.check "yamux core open advances the id" (s1.nextId == 3)
      r.check "yamux core open reports the stream" (openedWith 7 ⟨1, by decide⟩ acts)
      r.check "yamux core open sends a syn" (acts.length == 2)
  | .error _ => r.check "yamux core open" false

  -- A peer SYN with the peer's parity creates a stream and an accept.
  let synPeer := hdr .windowUpdate ⟨true, false, false, false⟩ ⟨4, by decide⟩ 0
  match step client (.bytes synPeer) with
  | .ok (s1, acts) =>
      r.check "yamux core peer syn creates a stream" (s1.streams.length == 1)
      r.check "yamux core peer syn accepts" (acceptedWith ⟨4, by decide⟩ acts)
  | .error _ => r.check "yamux core peer syn" false

  -- A peer SYN with our own parity is dropped: no stream, no accept.
  let synOurs := hdr .windowUpdate ⟨true, false, false, false⟩ ⟨3, by decide⟩ 0
  match step client (.bytes synOurs) with
  | .ok (s1, acts) =>
      r.check "yamux core own-parity syn is dropped" (s1.streams.length == 0)
      r.check "yamux core own-parity syn accepts nothing"
        (!acceptedWith ⟨3, by decide⟩ acts)
  | .error _ => r.check "yamux core own-parity syn" false

  -- A data frame beyond the granted window is a protocol error.
  let full : Stream := { Stream.fresh ⟨4, by decide⟩ false with buffered := initialWindow }
  let sFull : State := { client with streams := [full] }
  let over := dat ⟨4, by decide⟩ Flags.empty [1]
  match step sFull (.bytes over) with
  | .error e => r.check "yamux core overlong data is rejected" (e == .overlongData)
  | .ok _ => r.check "yamux core overlong data is rejected" false

  -- A data frame inside the window is delivered.
  let roomy : Stream := { Stream.fresh ⟨4, by decide⟩ false with buffered := 0 }
  let sRoomy : State := { client with streams := [roomy] }
  match step sRoomy (.bytes (dat ⟨4, by decide⟩ Flags.empty [1, 2, 3])) with
  | .ok (s1, acts) =>
      r.check "yamux core data is delivered"
        (acts.any fun a => match a with | .deliver _ p => p == [1, 2, 3] | _ => false)
      r.check "yamux core data fills the window"
        ((s1.streams.head?).any fun st => st.buffered == 3)
  | .error _ => r.check "yamux core data is delivered" false

  -- A ping on the session stream is echoed with ACK.
  let ping := hdr .ping ⟨true, false, false, false⟩ ⟨0, by decide⟩ 42
  match step client (.bytes ping) with
  | .ok (_, acts) =>
      r.check "yamux core ping is echoed" (acts.any fun a =>
        match a with
        | .send bs => bs.length == 12 && bs.getD 2 0 == 0 && bs.getD 3 0 == 2
        | _ => false)
  | .error _ => r.check "yamux core ping is echoed" false

  -- A GoAway ends the session.
  let bye := hdr .goAway Flags.empty ⟨0, by decide⟩ 0
  match step client (.bytes bye) with
  | .ok (s1, acts) =>
      r.check "yamux core goaway closes" (s1.closing && acts.contains .close)
  | .error _ => r.check "yamux core goaway closes" false

end CoreTests

end Tests.Yamux
