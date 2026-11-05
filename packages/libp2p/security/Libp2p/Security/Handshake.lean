import Conc
import Bytes
import Crypto
import Libp2p.Security.Constants
import Libp2p.Security.Mock.Core

/-!
# Noise `XX` handshake state machine

The pure core of `noise-libp2p`. Nothing in this file does IO: every step takes
a state and an event and returns the next state plus the actions a driver must
perform (`write` those bytes, or `established` with the two transport keys).
That is what makes the vectors and the captured go transcript replayable
byte-for-byte in the test suite, and it is what makes the handshake reviewable
without a network.

The pattern is `XX`: both sides contribute an ephemeral, both sides send their
static key encrypted, and neither static key is known before the handshake. It
is the libp2p pattern because the peer id is not known until the payload
arrives, so the responder cannot pick a key or a pattern before it has seen the
initiator's first message.

Message shapes, with `enc` being `encryptAndHash`:

- `msg1` initiator → responder: `e`, `enc(payload)`
- `msg2` responder → initiator: `e`, `enc(s)`, `enc(payload)`
- `msg3` initiator → responder: `enc(s)`, `enc(payload)`

`mixHash` hashes into `h`, the running transcript hash that every AEAD call
authenticates as associated data. `mixKey` folds key material into `ck` and
replaces the cipher key. A handshake that ends without the final `h` matching
on both sides cannot produce matching transport keys, which is why the tags are
the only integrity check the pattern needs.

The failure arms matter as much as the success path: a short message, a token
that is not 32 or 48 bytes, a tag that does not open, and a payload over 8 KiB
are all `Core.Error`, and none of them is end-of-stream. A peer that sends a
malformed handshake gets an error, not a clean close.
-/

set_option autoImplicit false

namespace Libp2p.Security

open Libp2p.Core (Role)

/-- The backend arms as log text. -/
def renderCrypto : Crypto.CryptoError → String
  | .authFailed => "authentication failed"
  | .invalidKey => "invalid key"
  | .invalidInput => "invalid input"
  | .invalidCertificate => "invalid certificate"
  | .fault => "backend fault"

/-- The failure `Except` every primitive here returns. A primitive that cannot
produce output is a protocol invariant break at this layer: the backend checks
widths the handshake already fixed. A failed AEAD open is the one place where
the tag, and so the peer, is at fault, and `CipherState.decrypt` reports that
arm itself. -/
def liftCrypto {α : Type} : Except Crypto.CryptoError α → Except Libp2p.Core.Error α
  | .ok v => .ok v
  | .error e => .error (.protocol (renderCrypto e))

/-- `n` as little-endian bytes. Noise numbers its nonces little-endian. -/
def leBytes (n width : Nat) : ByteArray :=
  Bytes.ofNatList ((List.range width).map (fun i => (n / 256 ^ i) % 256))

/-- The 12-byte ChaCha20-Poly1305 nonce: four zero bytes, then the 64-bit
counter little-endian. -/
def nonceBytes (n : Nat) : ByteArray :=
  Bytes.ofNatList [0, 0, 0, 0] ++ leBytes n 8

/-- Split a byte string at `n`, clamping both halves the way `extract`
does. Used to slice a 64-byte HKDF output into two keys and to read a
token of a fixed width off the front of a message. -/
def splitAt (b : ByteArray) (n : Nat) : ByteArray × ByteArray :=
  (b.extract 0 n, b.extract n b.size)

/-- A cipher key and its counter. `none` means no key yet, which is the
state before the first `mixKey`; in that state Noise sends plaintext with
an empty tag, which is why `encrypt` has a `none` arm instead of an
error. -/
structure CipherState where
  /-- The key, once `mixKey` has run at least once. -/
  key : Option Crypto.Key32 := none
  /-- Messages encrypted under `key` so far. -/
  nonce : Nat := 0

/-- The symmetric state: the chaining key, the transcript hash, and the
current cipher state. -/
structure SymmetricState where
  /-- The chaining key, folded by every `mixKey`. -/
  ck : ByteArray
  /-- The transcript hash, folded by every `mixHash`. -/
  h : ByteArray
  /-- The current cipher state. -/
  c : CipherState := {}

/-- Encrypt with associated data. With no key this is the identity and adds
no tag, which is the Noise rule for the pre-`mixKey` part of a handshake. -/
def CipherState.encrypt (cs : CipherState) (ad pt : ByteArray) :
    Except Libp2p.Core.Error (ByteArray × CipherState) :=
  match cs.key with
  | none => .ok (pt, cs)
  | some k =>
    if cs.nonce > maxNonce then .error (.protocol "nonce exhausted")
    else
      match Crypto.Nonce12.ofByteArray? (nonceBytes cs.nonce) with
      | none => .error (.protocol "nonce width")
      | some n =>
        match liftCrypto (Crypto.chachaSeal k n ad pt) with
        | .error e => .error e
        | .ok ct => .ok (ct, { cs with nonce := cs.nonce + 1 })

/-- Decrypt with associated data. A failed open is `authentication`: the tag
did not verify, which is not the same event as the peer closing. -/
def CipherState.decrypt (cs : CipherState) (ad ct : ByteArray) :
    Except Libp2p.Core.Error (ByteArray × CipherState) :=
  match cs.key with
  | none => .ok (ct, cs)
  | some k =>
    if cs.nonce > maxNonce then .error (.protocol "nonce exhausted")
    else
      match Crypto.Nonce12.ofByteArray? (nonceBytes cs.nonce) with
      | none => .error (.protocol "nonce width")
      | some n =>
        match Crypto.chachaOpen k n ad ct with
        | .error _ => .error (.authentication "AEAD tag did not verify")
        | .ok pt => .ok (pt, { cs with nonce := cs.nonce + 1 })

/-- The initial symmetric state: `ck` is the protocol name, `h` is the
protocol name hashed once, and no key is set. The name is exactly 32 bytes,
so it is its own first hash input (Noise §5.2). -/
def initSymmetric : SymmetricState :=
  let name := Bytes.ofString handshakeName
  { ck := name, h := name, c := {} }

/-- `MixHash`: fold bytes into the transcript hash. -/
def SymmetricState.mixHash (ss : SymmetricState) (data : ByteArray) :
    Except Libp2p.Core.Error SymmetricState :=
  match liftCrypto (Crypto.sha256 (ss.h ++ data)) with
  | .ok h' => .ok { ss with h := h' }
  | .error e => .error e

/-- `MixKey`: derive a new chaining key and cipher key from the old chaining
key and `ikm`, and reset the nonce. The two 32-byte halves of the 64-byte
HKDF output are `temp` and `out`. -/
def SymmetricState.mixKey (ss : SymmetricState) (ikm : ByteArray) :
    Except Libp2p.Core.Error SymmetricState :=
  match liftCrypto (Crypto.hkdfSha256 ss.ck ikm (Bytes.ofNatList []) 64) with
  | .error e => .error e
  | .ok out =>
    let (temp, key) := splitAt out 32
    match Crypto.Key32.ofByteArray? key with
    | none => .error (.protocol "hkdf key width")
    | some k => .ok { ss with ck := temp, c := { key := some k, nonce := 0 } }

/-- `EncryptAndHash`: encrypt, then fold the ciphertext into the transcript. -/
def SymmetricState.encryptAndHash (ss : SymmetricState) (pt : ByteArray) :
    Except Libp2p.Core.Error (ByteArray × SymmetricState) :=
  match ss.c.encrypt ss.h pt with
  | .error e => .error e
  | .ok (ct, c') =>
    match (SymmetricState.mixHash { ss with c := c' } ct) with
    | .error e => .error e
    | .ok ss' => .ok (ct, ss')

/-- `DecryptAndHash`: fold the ciphertext into the transcript, then
decrypt. -/
def SymmetricState.decryptAndHash (ss : SymmetricState) (ct : ByteArray) :
    Except Libp2p.Core.Error (ByteArray × SymmetricState) :=
  match ss.mixHash ct with
  | .error e => .error e
  | .ok ss' =>
    match ss'.c.decrypt ss.h ct with
    | .error e => .error e
    | .ok (pt, c') => .ok (pt, { ss' with c := c' })

/-- `Split`: the two transport keys. The first half is the
initiator-to-responder direction and the second half the reverse. -/
def SymmetricState.split (ss : SymmetricState) :
    Except Libp2p.Core.Error (Crypto.Key32 × Crypto.Key32) :=
  match liftCrypto (Crypto.hkdfSha256 ss.ck (Bytes.ofNatList []) (Bytes.ofNatList []) 64) with
  | .error e => .error e
  | .ok out =>
    let (k1b, k2b) := splitAt out 32
    match Crypto.Key32.ofByteArray? k1b, Crypto.Key32.ofByteArray? k2b with
    | some k1, some k2 => .ok (k1, k2)
    | _, _ => .error (.protocol "split key width")

/-- The local state of one handshake. `s` is our static private key, `e` our
ephemeral private key, and `rs`/`re` the peer's public keys once their
messages have carried them. `msg` is the number of the next message we
expect to send or read, which is what tells `step` which function to run. -/
structure State where
  /-- The symmetric state. -/
  ss : SymmetricState
  /-- Which end we are. -/
  role : Role
  /-- Our static private key. -/
  s : ByteArray
  /-- Our ephemeral private key for this handshake. -/
  eph : ByteArray
  /-- The peer's static public key, once known. -/
  rs : Option ByteArray := none
  /-- The peer's ephemeral public key, once known. -/
  re : Option ByteArray := none
  /-- The payload we will send, if it is already known. -/
  payload : ByteArray := ByteArray.empty
  /-- The payload the peer sent, once read. -/
  receivedPayload : Option ByteArray := none
  /-- The number of the next message: 1, 2 or 3. -/
  msg : Nat := 1
  /-- The transport keys, once the handshake completed. -/
  sendKey : Option Crypto.Key32 := none
  /-- The other direction's transport key. -/
  recvKey : Option Crypto.Key32 := none

/-- What the driver hands to `step`. -/
inductive Event where
  /-- Run the next write for this side. -/
  | send
  /-- Feed bytes that arrived from the peer. -/
  | received (bytes : ByteArray)

/-- What the driver must do after a step. -/
inductive Action where
  /-- Put these bytes on the connection. -/
  | write (bytes : ByteArray)
  /-- The handshake is done: these are the transport keys. -/
  | established (send recv : Crypto.Key32)

/-- Start a handshake. `prologue` is libp2p's peer id binding and is mixed
in before the first message, so a transcript captured on one connection
does not replay on another. -/
def init (role : Role) (staticPriv ephemeralPriv prologue : ByteArray) :
    Except Libp2p.Core.Error State :=
  let ss := initSymmetric
  match ss.mixHash prologue with
  | .error e => .error e
  | .ok ss => .ok { ss := ss, role := role, s := staticPriv, eph := ephemeralPriv }

/-- Our ephemeral public key. -/
def ephemeralPublic (st : State) : Except Libp2p.Core.Error ByteArray :=
  match Crypto.Key32.ofByteArray? st.eph with
  | none => .error (.protocol "ephemeral key width")
  | some k => do
    let ep ← liftCrypto (Crypto.x25519PublicKey k)
    .ok ep.bytes

/-- Our static public key. -/
def staticPublic (st : State) : Except Libp2p.Core.Error ByteArray :=
  match Crypto.Key32.ofByteArray? st.s with
  | none => .error (.protocol "static key width")
  | some k => do
    let sp ← liftCrypto (Crypto.x25519PublicKey k)
    .ok sp.bytes

/-- The raw shared secret, with both key widths checked. -/
def dhShared (priv pub : ByteArray) : Except Libp2p.Core.Error ByteArray :=
  match Crypto.Key32.ofByteArray? priv, Crypto.Key32.ofByteArray? pub with
  | some a, some b => do
    let shared ← liftCrypto (Crypto.x25519 a b)
    .ok shared.bytes
  | _, _ => .error (.protocol "dh key width")

/-- One Diffie-Hellman step on 32-byte keys, mixed into `ck` as `mixKey`.
Every `ee`, `es` and `se` in `XX` goes through here. -/
def mixDh (ss : SymmetricState) (priv pub : ByteArray) :
    Except Libp2p.Core.Error SymmetricState := do
  ss.mixKey (← dhShared priv pub)

/-- `e`: write our ephemeral public key, mix it into the transcript, and
fold it into the key. -/
def writeEphemeral (st : State) :
    Except Libp2p.Core.Error (ByteArray × State) := do
  let ep ← ephemeralPublic st
  let ss ← st.ss.mixHash ep
  let ss ← ss.mixKey ep
  .ok (ep, { st with ss := ss })

/-- `e` from the peer: it must be 32 bytes, and it is mixed before use. -/
def readEphemeral (st : State) (msg : ByteArray) :
    Except Libp2p.Core.Error (State × ByteArray) := do
  let (ep, rest) := splitAt msg 32
  if ep.size != 32 then .error (.protocol "ephemeral token length")
  else
    let ss ← st.ss.mixHash ep
    let ss ← ss.mixKey ep
    .ok ({ st with ss := ss, re := some ep }, rest)

/-- The `s` token: encrypt our static public key under the current key, fold
the ciphertext into the transcript, then fold the plaintext into `ck`. That
last `mixKey` is the Noise rule for a static key and the reason `es`/`se`
works on both sides. -/
def writeStatic (st : State) :
    Except Libp2p.Core.Error (ByteArray × State) := do
  let sp ← staticPublic st
  let (ct, ss) ← st.ss.encryptAndHash sp
  let ss ← ss.mixKey sp
  .ok (ct, { st with ss := ss })

/-- The `s` token from the peer. -/
def readStatic (st : State) (msg : ByteArray) :
    Except Libp2p.Core.Error (State × ByteArray) := do
  let (ct, rest) := splitAt msg 48
  if ct.size != 48 then .error (.protocol "static token length")
  else
    let (sp, ss) ← st.ss.decryptAndHash ct
    if sp.size != 32 then .error (.protocol "static key width")
    else
      let ss ← ss.mixKey sp
      .ok ({ st with ss := ss, rs := some sp }, rest)

/-- Encrypt and append the payload, the last field of every `XX` message. -/
def writePayload (st : State) :
    Except Libp2p.Core.Error (ByteArray × State) := do
  if st.payload.size > maxPayload then .error (.protocol "payload over 8 KiB")
  else
    let (ct, ss) ← st.ss.encryptAndHash st.payload
    .ok (ct, { st with ss := ss })

/-- Read the payload field: whatever is left of the message. -/
def readPayload (st : State) (msg : ByteArray) :
    Except Libp2p.Core.Error (State × ByteArray) := do
  if msg.size > maxPayload + tagLen then .error (.protocol "payload over 8 KiB")
  else
    let (pt, ss) ← st.ss.decryptAndHash msg
    if pt.size > maxPayload then .error (.protocol "payload over 8 KiB")
    else .ok ({ st with ss := ss, receivedPayload := some pt }, pt)

/-- Message 1, initiator: `e`, payload. -/
def writeMsg1 (st : State) : Except Libp2p.Core.Error (ByteArray × State) := do
  let (ep, st) ← writeEphemeral st
  let (pl, st) ← writePayload st
  .ok (ep ++ pl, st)

/-- Message 1 as the responder: read `e` and the payload. `ee` waits until
message 2, where our own ephemeral exists. -/
def readMsg1 (st : State) (msg : ByteArray) : Except Libp2p.Core.Error State := do
  let (st, rest) ← readEphemeral st msg
  let (st, _) ← readPayload st rest
  .ok { st with msg := 2 }

/-- Message 2, responder: `e`, `ee`, `s`, `es`, payload. -/
def writeMsg2 (st : State) : Except Libp2p.Core.Error (ByteArray × State) := do
  let (ep, st) ← writeEphemeral st
  let re ← match st.re with
    | some re => .ok re
    | none => .error (.protocol "no peer ephemeral")
  let ss ← mixDh st.ss st.eph re
  let st := { st with ss := ss }
  let (smsg, st) ← writeStatic st
  let rs ← match st.rs with
    | some rs => .ok rs
    | none => .error (.protocol "no peer static")
  let es ← dhShared st.eph rs
  let ss ← st.ss.mixKey es
  let st := { st with ss := ss }
  let (pl, st) ← writePayload st
  .ok (ep ++ smsg ++ pl, st)

/-- Message 2 as the initiator: the mirror of `writeMsg2`, with `ee` on our
ephemeral and `es` on our static key. -/
def readMsg2 (st : State) (msg : ByteArray) : Except Libp2p.Core.Error State := do
  let (st, rest) ← readEphemeral st msg
  let re ← match st.re with
    | some re => .ok re
    | none => .error (.protocol "no peer ephemeral")
  let ss ← mixDh st.ss st.eph re
  let st := { st with ss := ss }
  let (st, rest) ← readStatic st rest
  let rs ← match st.rs with
    | some rs => .ok rs
    | none => .error (.protocol "no peer static")
  let es ← dhShared st.s rs
  let ss ← st.ss.mixKey es
  let st := { st with ss := ss }
  let (st, _) ← readPayload st rest
  .ok { st with msg := 3 }

/-- Message 3, initiator: `s`, `se`, payload. -/
def writeMsg3 (st : State) : Except Libp2p.Core.Error (ByteArray × State) := do
  let (smsg, st) ← writeStatic st
  let rs ← match st.rs with
    | some rs => .ok rs
    | none => .error (.protocol "no peer static")
  let se ← dhShared st.eph rs
  let ss ← st.ss.mixKey se
  let st := { st with ss := ss }
  let (pl, st) ← writePayload st
  .ok (smsg ++ pl, st)

/-- Message 3 as the responder: `s`, `se`, payload, then `split`. Our static
key is known, so `se` is our static against their ephemeral. -/
def readMsg3 (st : State) (msg : ByteArray) : Except Libp2p.Core.Error State := do
  let (st, rest) ← readStatic st msg
  let re ← match st.re with
    | some re => .ok re
    | none => .error (.protocol "no peer ephemeral")
  let se ← dhShared st.s re
  let ss ← st.ss.mixKey se
  let st := { st with ss := ss }
  let (st, _) ← readPayload st rest
  .ok st

/-- Finish: `split`, then orient the keys by role. The initiator sends under
the first half and receives under the second; the responder the reverse. -/
def finish (st : State) : Except Libp2p.Core.Error (State × Action) := do
  let (k1, k2) ← st.ss.split
  let (send, recv) := if st.role == .initiator then (k1, k2) else (k2, k1)
  .ok ({ st with sendKey := some send, recvKey := some recv },
       Action.established send recv)

/-- One step of the machine. Pure: no IO, no randomness, no clock. The driver
supplies the ephemeral at `init` and the peer's bytes as events, so a recorded
transcript replays deterministically.

The guard on `msg` is what keeps a message from being read twice or echoed
back at the wrong point; a step that does not fit the state is `unsupported`
and never silently ignored. -/
def step (st : State) (ev : Event) :
    Except Libp2p.Core.Error (State × List Action) := do
  match ev with
  | .send =>
    match st.role, st.msg with
    | .initiator, 1 =>
      let (bytes, st) ← writeMsg1 st
      .ok ({ st with msg := 2 }, [Action.write bytes])
    | .responder, 2 =>
      let (bytes, st) ← writeMsg2 st
      .ok ({ st with msg := 3 }, [Action.write bytes])
    | .initiator, 3 =>
      let (bytes, st) ← writeMsg3 st
      let (st, act) ← finish st
      .ok (st, [Action.write bytes, act])
    | _, _ => .error (.protocol "no message to send in this state")
  | .received bytes =>
    match st.role, st.msg with
    | .responder, 1 =>
      let st ← readMsg1 st bytes
      .ok (st, [])
    | .initiator, 2 =>
      let st ← readMsg2 st bytes
      .ok (st, [])
    | .responder, 3 =>
      let st ← readMsg3 st bytes
      let (st, act) ← finish st
      .ok (st, [act])
    | _, _ => .error (.protocol "no message to read in this state")

end Libp2p.Security
