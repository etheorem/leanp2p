import Crypto
import Bytes
import Proto
import Streams.Framing
import Libp2p.Identity
import Libp2p.Security.Mock.Core
import Libp2p.Security.Constants

/-!
# The Noise XX core

The XX handshake of the Noise spec, as a pure state machine (root
ARCHITECTURE §3.3):

```
step : State → Event → Except Error (State × List Action)
```

```
XX:
  -> e
  <- e, ee, s, es
  -> s, se
```

## Two layers, as the specs split them

The Noise spec defines the handshake over opaque payloads and a
prologue. The noise-libp2p spec puts the libp2p payload inside the
second and third messages, and says: "Upon receiving the handshake
payload, peers MUST decode the public key … The key MUST then be used
to validate the `identity_sig` field." This module is the Noise layer.
It hands each decrypted payload out as `Action.payload`, and
`Libp2p.Security.Payload` checks it. go-libp2p and js-libp2p split the
work the same way (the package ARCHITECTURE, "The core shape"). The
flynn vectors carry raw payloads and a prologue, so they test this
layer alone.

The shell performs the actions in order. On the initiator, the payload
of message 2 comes out before the write of message 3, so the shell
checks it and tears the connection down before message 3 reaches the
wire, as go and js do (the same section).

## The interface follows flynn's

flynn's `HandshakeState` (`vendor/flynn-noise/state.go`) takes the
prologue and the static keypair in `NewHandshakeState`, one payload per
`WriteMessage`, and one whole message per `ReadMessage`. A call out of
turn is an error there. js and nim also set the static key when they
build the handshake state (the package ARCHITECTURE, "The core shape").
So `State.init` takes the role, the prologue
(empty for libp2p), and the static key. The events are:

* `bytes`: one whole Noise message, which the shell read through the
  2-byte length prefix. A message out of turn is `unexpectedEvent`.
* `entropy`: the 32 bytes of the ephemeral private key, from the `Rng`
  seam of the facade (§3.6, §3.3: randomness is an input).
* `local`: the marshaled payload of our next handshake message.

The bytes the shell read past the last message stay in its framed
reader, and the transport reads them next (§4.7). rust-libp2p keeps
them the same way: `map_into_transport` hands the read buffer of the
handshake's `Framed` to the transport
(`vendor/rust-libp2p/transports/noise/src/io/handshake.rs`, line 157).

The actions: `write` a framed message, hand out a decrypted remote
`payload` with the remote static key once it is known, and `complete`
the handshake with the two cipher states of `split` and the remote
static key. The shell learns of the state only from the actions (§3.3),
so the payload carries the key that its check needs.

The core has no tick. The upgrader owns the deadline (owned contract
7).

## The keys by phase

`Phase` names the next step of each role and holds the keys that the
step needs. A DH of the pattern therefore never looks up a key that may
be absent: the type of the phase carries it.
-/

set_option autoImplicit false

namespace Libp2p.Security.Noise

-- `Role` comes from the mock of W5.2 (RULES.md, "Working ahead of the
-- tree").
open Bytes Libp2p.Security.Mock.Core

/-! ## Data types

The core's bytes sit in `Bytes.Blob`, the shared wrapper with a `Repr`
(§3.2). -/

/-- Exactly 32 bytes, for core data: a key, the chaining key, or the
handshake hash. The backend type `Crypto.Key32` has no `Repr`, and the
instance belongs with that type (§3.2), so the core wraps it. -/
structure Bytes32 where
  /-- The bytes, with their size. -/
  key : Crypto.Key32

namespace Bytes32

/-- The bytes. -/
def bytes (k : Bytes32) : ByteArray := k.key.bytes

/-- The bytes as a `Bytes32`. `none` when the size is not 32. -/
def ofByteArray? (b : ByteArray) : Option Bytes32 :=
  (Crypto.Key32.ofByteArray? b).map Bytes32.mk

instance : BEq Bytes32 := ⟨fun a b => a.bytes == b.bytes⟩

/-- The `Repr` that §3.3 asks of core data. It prints the bytes, keys
included. -/
instance : Repr Bytes32 where
  reprPrec k _ := s!"Noise.Bytes32 {toHex k.bytes}"

end Bytes32

/-- How a Noise handshake or payload check fails: the one error
inductive of the package (§3.5). The seam value maps each arm into
`Core.Error` (owned contract 1, contract 4). -/
inductive Error where
  /-- An AEAD open failed: the message was changed, or it was sealed
  under another key. A protocol error, distinct from EOF (owned
  contract 1). -/
  | decrypt
  /-- Another crypto failure: an X25519 peer key of small order
  (`invalidKey`), or a library fault. -/
  | crypto (e : Crypto.CryptoError)
  /-- A handshake message shorter than its tokens need: the size, and
  the size the next token needs. -/
  | shortMessage (size need : Nat)
  /-- A message longer than `maxMessage`. -/
  | messageTooLarge (size : Nat)
  /-- A cipher state reached the reserved nonce `2 ^ 64 - 1`. -/
  | nonceExhausted
  /-- An event the phase does not take: a message out of turn, an
  entropy the phase does not need, or a payload when no write of ours
  is left or one already waits. -/
  | unexpectedEvent
  /-- An event arrived after the handshake completed. -/
  | finished
  /-- The connection ended before the handshake completed. The shell
  reports it; the core never sees the end of the connection. -/
  | closed
  /-- The connection ended inside a transport frame: the bytes of the
  frame that had arrived. go-libp2p reads each frame with `io.ReadFull`,
  which fails with `io.ErrUnexpectedEOF` here
  (`vendor/go-libp2p/p2p/security/noise/rw.go`, lines 130 and 144), so only an end
  between frames is orderly. -/
  | truncatedFrame (size : Nat)
  /-- A handshake payload over `maxPayload`, refused before the decode
  (owned contract 2). -/
  | payloadTooLarge (size : Nat)
  /-- The `NoiseHandshakePayload` protobuf did not decode. -/
  | payload (e : Pb.Error)
  /-- The payload holds no `identity_key` or no `identity_sig`. -/
  | missingIdentity
  /-- The identity key did not unmarshal, or no peer id derives from
  it. -/
  | identity (e : Libp2p.Identity.Error)
  /-- The signature does not verify over the static key of the
  handshake (owned contract 4). -/
  | badSignature
  deriving BEq, Repr

/-! ## The cipher state -/

/-- The Noise `CipherState`: a key, once one is mixed in, and the nonce
of the next message. -/
structure CipherState where
  /-- The key. `none` before the first `MixKey`: then encryption is the
  identity function. -/
  key : Option Bytes32
  /-- The nonce of the next message. -/
  nonce : Nat
  deriving BEq, Repr

namespace CipherState

/-- The cipher state with no key. -/
def empty : CipherState := ⟨none, 0⟩

/-- A fresh cipher state under a key. -/
def ofKey (k : Bytes32) : CipherState := ⟨some k, 0⟩

/-- The ChaChaPoly nonce of the Noise spec: 4 zero bytes, then the
counter as 8 bytes little-endian. `Nat.toUInt8` keeps the low 8 bits,
so each entry is one byte of the counter. The array literal has 12
entries, so `rfl` proves the size. -/
def nonceBytes (n : Nat) : Crypto.Nonce12 :=
  let b (i : Nat) : UInt8 := (n >>> (8 * i)).toUInt8
  ⟨⟨#[0, 0, 0, 0, b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7]⟩, rfl⟩

-- `ByteArray.toList` recurses by well-founded recursion, which the
-- kernel does not unfold, so the check runs through the evaluator.
#guard (nonceBytes 258).bytes.toList = [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0]

/-- `EncryptWithAd`: seal under the key and the nonce, then step the
nonce. With no key, the plaintext passes unchanged. -/
def encryptWithAd (cs : CipherState) (ad pt : ByteArray) : Except Error (CipherState × ByteArray) :=
  match cs.key with
  | none => .ok (cs, pt)
  | some k =>
    if cs.nonce ≥ reservedNonce then .error .nonceExhausted
    else do
      let ct ← (Crypto.chachaSeal k.key (nonceBytes cs.nonce) ad pt).mapError .crypto
      return ({ cs with nonce := cs.nonce + 1 }, ct)

/-- `DecryptWithAd`: open under the key and the nonce, then step the
nonce. A tag that does not verify is `decrypt`. -/
def decryptWithAd (cs : CipherState) (ad ct : ByteArray) : Except Error (CipherState × ByteArray) :=
  match cs.key with
  | none => .ok (cs, ct)
  | some k =>
    if cs.nonce ≥ reservedNonce then .error .nonceExhausted
    else do
      let pt ← (Crypto.chachaOpen k.key (nonceBytes cs.nonce) ad ct).mapError fun
        | .authFailed => .decrypt
        | e => .crypto e
      return ({ cs with nonce := cs.nonce + 1 }, pt)

end CipherState

/-! ## The symmetric state -/

/-- The Noise `SymmetricState`: the cipher state, the chaining key
`ck`, and the handshake hash `h`. -/
structure SymmetricState where
  /-- The cipher state of the handshake messages. -/
  cs : CipherState
  /-- The chaining key. -/
  ck : Bytes32
  /-- The handshake hash. -/
  h : Bytes32
  deriving BEq, Repr

/-- The 32 bytes that a facade call answered. The facade types the
answer as `ByteArray`, so the size is checked once here, where the
bytes cross the FFI (§3.7). A wrong size is a library fault. -/
private def toBytes32 (b : ByteArray) : Except Error Bytes32 :=
  match Bytes32.ofByteArray? b with
  | some k => .ok k
  | none => .error (.crypto .fault)

/-- SHA-256, the `HASH` of the cipher suite. -/
private def hash (b : ByteArray) : Except Error Bytes32 := do
  toBytes32 (← (Crypto.sha256 b).mapError .crypto)

/-- The Noise `HKDF` with two outputs. The Noise spec defines it as
HMAC-SHA-256 steps over the chaining key, and they are RFC 5869 with
`ck` as the salt, an empty info, and 64 bytes of output. -/
private def hkdf2 (ck : Bytes32) (ikm : ByteArray) : Except Error (Bytes32 × Bytes32) := do
  let out ← (Crypto.hkdfSha256 ck.bytes ikm .empty 64).mapError .crypto
  return (← toBytes32 (out.extract 0 32), ← toBytes32 (out.extract 32 64))

/-- The X25519 shared secret of a private and a public key. -/
private def dh (priv pub : Bytes32) : Except Error ByteArray :=
  (Crypto.x25519 priv.key pub.key).map (·.bytes) |>.mapError .crypto

namespace SymmetricState

/-- `InitializeSymmetric`: `h` is the protocol name, zero-padded when
shorter than 32 bytes and hashed when longer, and `ck` is `h`. -/
def init (name : ByteArray) : Except Error SymmetricState := do
  let h ← if name.size ≤ 32 then
      toBytes32 (name ++ ⟨Array.replicate (32 - name.size) 0⟩)
    else hash name
  return ⟨.empty, h, h⟩

/-- `MixHash`: `h` becomes `HASH(h ‖ data)`. -/
def mixHash (ss : SymmetricState) (data : ByteArray) : Except Error SymmetricState := do
  return { ss with h := ← hash (ss.h.bytes ++ data) }

/-- `MixKey`: the KDF of `ck` and the input gives the new `ck` and a
fresh cipher key. -/
def mixKey (ss : SymmetricState) (ikm : ByteArray) : Except Error SymmetricState := do
  let (ck, k) ← hkdf2 ss.ck ikm
  return { ss with ck, cs := .ofKey k }

/-- A DH token (`ee`, `es`, `se`): `MixKey` of the shared secret. -/
def mixDh (ss : SymmetricState) (priv pub : Bytes32) : Except Error SymmetricState := do
  ss.mixKey (← dh priv pub)

/-- `EncryptAndHash`: encrypt with `h` as the associated data, then mix
the ciphertext into `h`. -/
def encryptAndHash (ss : SymmetricState) (pt : ByteArray) :
    Except Error (SymmetricState × ByteArray) := do
  let (cs, ct) ← ss.cs.encryptWithAd ss.h.bytes pt
  let ss ← { ss with cs }.mixHash ct
  return (ss, ct)

/-- `DecryptAndHash`: decrypt with `h` as the associated data, then mix
the ciphertext into `h`. -/
def decryptAndHash (ss : SymmetricState) (ct : ByteArray) :
    Except Error (SymmetricState × ByteArray) := do
  let (cs, pt) ← ss.cs.decryptWithAd ss.h.bytes ct
  let ss ← { ss with cs }.mixHash ct
  return (ss, pt)

/-- `Split`: the KDF of `ck` and an empty input gives the two transport
keys. The first one protects the initiator's messages. -/
def split (ss : SymmetricState) : Except Error (CipherState × CipherState) := do
  let (k1, k2) ← hkdf2 ss.ck .empty
  return (.ofKey k1, .ofKey k2)

end SymmetricState

/-! ## The handshake state -/

/-- The next step of the handshake, by role, with the keys it needs.
The initiator writes messages 0 and 2, and the responder writes
message 1. -/
inductive Phase where
  /-- The initiator writes message 0 (`e`). -/
  | initStart
  /-- The initiator wrote message 0 with its ephemeral key, and reads
  message 1. -/
  | initSentA (e : Bytes32)
  /-- The initiator read message 1: the peer's ephemeral and static
  keys. It writes message 2 (`s, se`). -/
  | initGotB (re rs : Bytes32)
  /-- The responder reads message 0. -/
  | respStart
  /-- The responder read message 0: the peer's ephemeral key. It writes
  message 1 (`e, ee, s, es`). -/
  | respGotA (re : Bytes32)
  /-- The responder wrote message 1 with its ephemeral key, and reads
  message 2. -/
  | respSentB (e : Bytes32)
  /-- The handshake completed. -/
  | done
  deriving BEq, Repr

namespace Phase

/-- The phase still needs the ephemeral private key: before our `e`
token. -/
def needsEntropy : Phase → Bool
  | .initStart | .respStart | .respGotA _ => true
  | _ => false

/-- A write of ours is still ahead, so a payload may wait for it. -/
def writesLeft : Phase → Bool
  | .initStart | .initSentA _ | .initGotB _ _ | .respStart | .respGotA _ => true
  | _ => false

end Phase

/-- The state of one handshake: the phase, the symmetric state, our
static keys, and the inputs that wait to be used. -/
structure State where
  /-- The next step, with the keys it needs. -/
  phase : Phase
  /-- The symmetric state. -/
  sym : SymmetricState
  /-- Our static private key. -/
  s : Bytes32
  /-- Our static public key. -/
  sPub : Bytes32
  /-- Our ephemeral private key, once the entropy arrived and before
  the `e` token used it. -/
  entropy : Option Bytes32
  /-- The payload of our next message, once the shell posted it. -/
  payload : Option Blob
  deriving BEq, Repr

/-- An input of the core. -/
inductive Event where
  /-- One whole Noise message, without its length prefix. -/
  | bytes (msg : Blob)
  /-- The ephemeral private key, 32 bytes from the `Rng` seam. -/
  | entropy (e : Bytes32)
  /-- The marshaled payload of our next handshake message. `local` is a
  Lean keyword, so the name takes guillemets, as `Muxer.«open»`
  does. -/
  | «local» (p : Blob)
  deriving BEq, Repr

/-- The end of a handshake. -/
structure Completion where
  /-- The cipher state of our transport messages. -/
  send : CipherState
  /-- The cipher state of the peer's transport messages. -/
  recv : CipherState
  /-- The peer's static Noise key. The payload check verifies the
  signature over it. -/
  remoteStatic : Bytes32
  deriving BEq, Repr

/-- An output of the core. The shell performs the actions in order. -/
inductive Action where
  /-- Write the framed message to the connection. -/
  | write (frame : Blob)
  /-- The peer's payload of one handshake message, decrypted, with the
  peer's static key once the handshake has learned it. The shell checks
  the payloads of messages 1 and 2 against that key before it performs
  the next action; it learns of the state only from the actions (§3.3),
  so the key travels here. Message 0 arrives before the peer's `s`
  token, so its key is `none`. -/
  | payload (p : Blob) (remoteStatic : Option Bytes32)
  /-- The handshake completed. -/
  | complete (c : Completion)
  deriving BEq, Repr

namespace State

/-- The state before the first message: the protocol name and the
prologue mixed in. libp2p uses an empty prologue; the flynn vectors set
one. -/
def init (role : Role) (prologue : ByteArray) (s : Bytes32) : Except Error State := do
  let sym ← SymmetricState.init protocolName.toUTF8
  let sym ← sym.mixHash prologue
  let sPub ← (Crypto.x25519PublicKey s.key).mapError .crypto
  let phase := match role with
    | .initiator => .initStart
    | .responder => .respStart
  return { phase, sym, s, sPub := ⟨sPub⟩, entropy := none, payload := none }

/-! ### Tokens -/

/-- Write `e`: the public key of the ephemeral private key, in clear,
mixed into `h`. -/
private def writeE (sym : SymmetricState) (e : Bytes32) :
    Except Error (SymmetricState × ByteArray) := do
  let pub ← (Crypto.x25519PublicKey e.key).mapError .crypto
  return (← sym.mixHash pub.bytes, pub.bytes)

/-- Read `e` at `pos`: the peer's ephemeral key, mixed into `h`. -/
private def readE (sym : SymmetricState) (msg : ByteArray) (pos : Nat) :
    Except Error (SymmetricState × Bytes32 × Nat) := do
  let some re := Bytes32.ofByteArray? (msg.extract pos (pos + dhLen))
    | throw (.shortMessage msg.size (pos + dhLen))
  return (← sym.mixHash re.bytes, re, pos + dhLen)

/-- Read `s` at `pos`. In XX, `s` always follows a `MixKey`, so it
arrives encrypted: the key and the tag. -/
private def readS (sym : SymmetricState) (msg : ByteArray) (pos : Nat) :
    Except Error (SymmetricState × Bytes32 × Nat) := do
  let len := dhLen + Crypto.aeadTagLen
  if msg.size < pos + len then throw (.shortMessage msg.size (pos + len))
  let (sym, pt) ← sym.decryptAndHash (msg.extract pos (pos + len))
  return (sym, ← toBytes32 pt, pos + len)

/-- End a message we write: the encrypted payload after the token
bytes, then the 2-byte length prefix. -/
private def finishWrite (sym : SymmetricState) (out payload : ByteArray) :
    Except Error (SymmetricState × Blob) := do
  let (sym, ct) ← sym.encryptAndHash payload
  let msg := out ++ ct
  let some frame := Streams.Framing.encodeB? .u16be maxMessage msg
    | throw (.messageTooLarge msg.size)
  return (sym, ⟨frame⟩)

/-- End a message we read: the payload is the rest after `pos`. -/
private def finishRead (sym : SymmetricState) (msg : ByteArray) (pos : Nat) :
    Except Error (SymmetricState × Blob) := do
  let (sym, pt) ← sym.decryptAndHash (msg.extract pos msg.size)
  return (sym, ⟨pt⟩)

/-- `Split`, and the completion in our role. The initiator sends with
the first cipher state. -/
private def complete (sym : SymmetricState) (initiator : Bool) (rs : Bytes32) :
    Except Error Completion := do
  let (c1, c2) ← sym.split
  let (send, recv) := if initiator then (c1, c2) else (c2, c1)
  return { send, recv, remoteStatic := rs }

/-! ### Messages -/

/-- Write the message the phase writes, when its inputs are present.
No action while one is missing. -/
private def tryWrite (st : State) : Except Error (State × List Action) := do
  match st.phase, st.payload, st.entropy with
  | .initStart, some p, some e =>
    -- Message 0: `e`.
    let (sym, out) ← writeE st.sym e
    let (sym, frame) ← finishWrite sym out p.bytes
    return ({ st with phase := .initSentA e, sym, payload := none, entropy := none },
      [.write frame])
  | .respGotA re, some p, some e =>
    -- Message 1: `e, ee, s, es`. The responder's `es` is DH(s, re).
    let (sym, out) ← writeE st.sym e
    let sym ← sym.mixDh e re
    let (sym, sCt) ← sym.encryptAndHash st.sPub.bytes
    let sym ← sym.mixDh st.s re
    let (sym, frame) ← finishWrite sym (out ++ sCt) p.bytes
    return ({ st with phase := .respSentB e, sym, payload := none, entropy := none },
      [.write frame])
  | .initGotB re rs, some p, _ =>
    -- Message 2: `s, se`. The initiator's `se` is DH(s, re).
    let (sym, sCt) ← st.sym.encryptAndHash st.sPub.bytes
    let sym ← sym.mixDh st.s re
    let (sym, frame) ← finishWrite sym sCt p.bytes
    let c ← complete sym true rs
    return ({ st with phase := .done, sym, payload := none }, [.write frame, .complete c])
  | _, _, _ => return (st, [])

/-- Read the message the phase reads. A message in a phase that writes,
or after the end, is `unexpectedEvent`. -/
private def read (st : State) (msg : ByteArray) : Except Error (State × List Action) := do
  if msg.size > maxMessage then throw (.messageTooLarge msg.size)
  match st.phase with
  | .respStart =>
    -- Message 0: `e`, and a payload in clear.
    let (sym, re, pos) ← readE st.sym msg 0
    let (sym, p) ← finishRead sym msg pos
    return ({ st with phase := .respGotA re, sym }, [.payload p none])
  | .initSentA e =>
    -- Message 1: `e, ee, s, es`. The initiator's `es` is DH(e, rs).
    let (sym, re, pos) ← readE st.sym msg 0
    let sym ← sym.mixDh e re
    let (sym, rs, pos) ← readS sym msg pos
    let sym ← sym.mixDh e rs
    let (sym, p) ← finishRead sym msg pos
    return ({ st with phase := .initGotB re rs, sym }, [.payload p (some rs)])
  | .respSentB e =>
    -- Message 2: `s, se`. The responder's `se` is DH(e, rs).
    let (sym, rs, pos) ← readS st.sym msg 0
    let sym ← sym.mixDh e rs
    let (sym, p) ← finishRead sym msg pos
    let c ← complete sym false rs
    return ({ st with phase := .done, sym }, [.payload p (some rs), .complete c])
  | _ => throw .unexpectedEvent

end State

/-- The transition function. An input is taken when the phase can use
it; then the core writes whatever its inputs allow. An event after the
completion is `finished`: the transport takes over then. -/
def step (st : State) (ev : Event) : Except Error (State × List Action) := do
  if st.phase == .done then throw .finished
  match ev with
  | .bytes m =>
    let (st, acts) ← st.read m.bytes
    let (st, more) ← st.tryWrite
    return (st, acts ++ more)
  | .entropy e =>
    unless st.phase.needsEntropy && st.entropy.isNone do throw .unexpectedEvent
    State.tryWrite { st with entropy := some e }
  | .«local» p =>
    unless st.phase.writesLeft && st.payload.isNone do throw .unexpectedEvent
    State.tryWrite { st with payload := some p }

end Libp2p.Security.Noise
