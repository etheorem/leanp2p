import LeanP2P.Crypto.Sha256
import LeanP2P.Crypto.Hkdf
import LeanP2P.Crypto.OpenSsl
import LeanP2P.Crypto.Messages
import LeanP2P.Net.Transport
import LeanP2P.Conn.Security
import LeanP2P.Conn.Reader
/-!
# Noise XX (VECTOR_TEST_PLAN.md, phase 3 step 16)

`noise-libp2p`: the `Noise_XX_25519_ChaChaPoly_SHA256` handshake over any
`Connection`, per vendor/specs/noise/README.md.

Layering, mirroring the Noise framework:

- `CipherState` - AEAD (ChaCha20-Poly1305 through the OpenSSL backend, the
  phase 2 decision) with a 64-bit counter nonce serialized as 4 zero bytes
  ++ little-endian counter; `2^64 - 1` nonces per key, never reached here.
- `SymmetricState` - running hash `h` (SHA-256, pure Lean) and chaining key
  `ck` (HKDF-SHA256, pure Lean: Noise's two-output HKDF is exactly RFC 5869
  with `salt = ck`, `info = ""`, `L = 64`).
- `HandshakeState` - the XX pattern `-> e, <- e, ee, s, es, -> s, se`,
  driven through `mixHash` / `mixKey` / `encryptAndHash` / `decryptAndHash`
  and finished with `split` (two transport cipher states).

Wire format: every message is `2-byte big-endian length ++ message`, capped
at 65535 bytes (`maxMessage`). `be16Bytes`/`frameOf?` are the verified pure
codec; the IO shell goes through `readFramed`/`writeFramed`.

The libp2p payload rides in handshake messages 2 and 3: the
`NoiseHandshakePayload` protobuf (`Crypto/Messages`) with the identity key,
the signature of `noise-libp2p-static-key:` ++ static Noise public key, and
the muxer-negotiation extension. Verification follows the spec: an invalid
signature aborts the connection.

The responder's keys are explicit in `HandshakeState` (`s`, and `efix` as an
optional deterministic ephemeral), so the captured go-libp2p transcript
(`Tests/vectors/noise-go-transcript.json`) replays byte-for-byte.
-/

namespace LeanP2P.Noise

def protocolName : String := "Noise_XX_25519_ChaChaPoly_SHA256"

/-- Noise messages must fit in 16 bits (noise spec "Message Format"). -/
def maxMessage : Nat := 65535

/-! ## Message framing: 2-byte big-endian length prefix -/

def be16Bytes (n : Nat) : List Nat := [n / 256 % 256, n % 256]

def be16Of (bs : List Nat) : Nat :=
  match bs with
  | a :: b :: _ => a * 256 + b
  | _ => 0

theorem be16_length (n : Nat) : (be16Bytes n).length = 2 := by simp [be16Bytes]

theorem be16_roundtrip (n : Nat) (h : n < 65536) : be16Of (be16Bytes n) = n := by
  simp only [be16Of, be16Bytes]
  have h1 : n / 256 < 256 := by omega
  omega

def writeFramed (c : Connection) (payload : ByteArray) : IO Unit := do
  let n := payload.size
  if n ≤ maxMessage then
    c.write (Bytes.ofNatList (be16Bytes n) ++ payload)

/-- Read one framed message (`none` on EOF). The length prefix is two bytes,
so the 65535 cap holds by construction. Over-read bytes stay in the reader. -/
def readFramed (r : BufReader) : IO (Option ByteArray) := do
  match ← r.readExactly 2 with
  | none => pure none
  | some lenB =>
    let len := be16Of (Bytes.toNatList lenB)
    r.readExactly len

/-! ## CipherState -/

structure CipherState where
  /-- 32-byte key, absent before the first key is mixed. -/
  k : Option ByteArray
  n : Nat := 0

/-- Noise nonce: 4 zero bytes then the little-endian 64-bit counter. -/
def nonceBytes (n : Nat) : ByteArray :=
  Bytes.ofNatList ([0, 0, 0, 0] ++ Pb.leBytes n 8)

def maxNonce : Nat := 2 ^ 64 - 1

def CipherState.encrypt (cs : CipherState) (ad pt : ByteArray) :
    IO (Option (ByteArray × CipherState)) := do
  if cs.n ≥ maxNonce then pure none
  else match cs.k with
    | none => pure (some (pt, { cs with n := cs.n + 1 }))
    | some k =>
      match ← OpenSsl.chacha20poly1305Seal k (nonceBytes cs.n) ad pt with
      | none => pure none
      | some ct => pure (some (ct, { cs with n := cs.n + 1 }))

def CipherState.decrypt (cs : CipherState) (ad ct : ByteArray) :
    IO (Option (ByteArray × CipherState)) := do
  if cs.n ≥ maxNonce then pure none
  else match cs.k with
    | none => pure (some (ct, { cs with n := cs.n + 1 }))
    | some k =>
      match ← OpenSsl.chacha20poly1305Open k (nonceBytes cs.n) ad ct with
      | none => pure none
      | some pt => pure (some (pt, { cs with n := cs.n + 1 }))

/-! ## SymmetricState -/

structure SymmetricState where
  ck : ByteArray
  h : ByteArray
  c : CipherState

/-- `h = ck = protocol_name` (zero-padded to 32 bytes when shorter, hashed
when longer) - Noise framework §5.2; the prologue is mixed in afterwards.
The noise-libp2p name is exactly 32 bytes, so `h` starts out as the raw
ASCII name. -/
def initState : SymmetricState :=
  let name := Bytes.ofString protocolName
  let h := if name.size ≤ 32 then
    Bytes.ofNatList (Bytes.toNatList name ++ List.replicate (32 - name.size) 0)
  else Sha256.digestB name
  { ck := h, h := h, c := { k := none, n := 0 } }

def SymmetricState.mixHash (ss : SymmetricState) (data : ByteArray) : SymmetricState :=
  { ss with h := Sha256.digestB (ss.h ++ data) }

/-- Noise's two-output HKDF: RFC 5869 with `salt = ck`, empty `info`,
`L = 64`, split in half. -/
def hkdf2 (ck ikm : ByteArray) : ByteArray × ByteArray :=
  let okm := Bytes.ofNatList
    (Hkdf.expand (Hkdf.extract (Bytes.toNatList ck) (Bytes.toNatList ikm)) [] 64)
  (okm.extract 0 32, okm.extract 32 64)

def SymmetricState.mixKey (ss : SymmetricState) (ikm : ByteArray) : SymmetricState :=
  let (ck, k) := hkdf2 ss.ck ikm
  { ck := ck, h := ss.h, c := { k := some k, n := 0 } }

/-- Encrypt (or, keyless, pass through) and mix the ciphertext into `h`. -/
def SymmetricState.encryptAndHash (ss : SymmetricState) (pt : ByteArray) :
    IO (Option (ByteArray × SymmetricState)) := do
  match ← ss.c.encrypt ss.h pt with
  | none => pure none
  | some (ct, c) => pure (some (ct, { ss with c := c }.mixHash ct))

/-- Decrypt (or, keyless, pass through) and mix the ciphertext into `h`. -/
def SymmetricState.decryptAndHash (ss : SymmetricState) (ct : ByteArray) :
    IO (Option (ByteArray × SymmetricState)) := do
  match ← ss.c.decrypt ss.h ct with
  | none => pure none
  | some (pt, c) => pure (some (pt, { ss with c := c }.mixHash ct))

/-- `Split()`: the final key derivation. `k1` encrypts initiator -> responder
traffic, `k2` responder -> initiator. -/
def SymmetricState.split (ss : SymmetricState) : CipherState × CipherState :=
  let (k1, k2) := hkdf2 ss.ck ByteArray.empty
  ({ k := some k1, n := 0 }, { k := some k2, n := 0 })

/-! ## HandshakeState (XX) -/

structure HandshakeState where
  ss : SymmetricState
  initiator : Bool
  /-- Local static Noise private key (32 bytes). -/
  s : ByteArray
  /-- Deterministic local ephemeral, for replay tests; generated randomly
when `none`. -/
  efix : Option ByteArray := none
  /-- Local ephemeral private key (generated in msg1/msg2). -/
  e : Option ByteArray := none
  /-- Remote static Noise public key (learned in msg3). -/
  rs : Option ByteArray := none
  /-- Remote ephemeral public key (learned in msg1/msg2). -/
  re : Option ByteArray := none

def HandshakeState.init (initiator : Bool) (staticPriv : ByteArray)
    (prologue : ByteArray := ByteArray.empty) : IO (Option HandshakeState) := do
  if staticPriv.size != 32 then pure none
  else pure (some
    { ss := initState.mixHash prologue
      initiator := initiator
      s := staticPriv })

def keypair (efix : Option ByteArray) : IO (Option (ByteArray × ByteArray)) := do
  match efix with
  | some e =>
      if e.size != 32 then pure none
      else match ← OpenSsl.x25519Pubkey e with
        | none => pure none
        | some pub => pure (some (e, pub))
  | none =>
      match ← OpenSsl.randomBytes 32 with
      | none => pure none
      | some e => match ← OpenSsl.x25519Pubkey e with
        | none => pure none
        | some pub => pure (some (e, pub))

/-- X25519 (clamping inside OpenSSL). -/
def dh (priv pub : ByteArray) : IO (Option ByteArray) :=
  OpenSsl.x25519Dh priv pub

/-! ### Responder side -/

/-- Responder, message 1 (`-> e`): the 32-byte ephemeral, then the keyless
payload, both mixed into `h`. -/
def HandshakeState.readMsg1 (hs : HandshakeState) (msg1 : ByteArray) :
    IO (Option (ByteArray × HandshakeState)) := do
  if hs.initiator ∨ msg1.size < 32 then pure none
  else do
    let ePub := msg1.extract 0 32
    let rest := msg1.extract 32 msg1.size
    -- <- e: mix the ephemeral, then the keyless payload
    let ss0 := hs.ss.mixHash ePub
    match ← ss0.decryptAndHash rest with
    | none => pure none
    | some (payload, ss') =>
      pure (some (payload, { hs with re := some ePub, ss := ss' }))

/-- Responder, message 2 (`<- e, ee, s, es ++ payload`). -/
def HandshakeState.writeMsg2 (hs : HandshakeState) (payload : ByteArray) :
    IO (Option (ByteArray × HandshakeState)) := do
  if hs.initiator then pure none
  else match ← keypair hs.efix with
    | none => pure none
    | some (e, ePub) =>
      let re? := hs.re
      if re?.isNone then pure none
      else do
        -- e
        let ss0 := hs.ss.mixHash ePub
        -- ee
        let ee? ← dh e re?.get!
        match ee? with
        | none => pure none
        | some ee => do
          let ss1 := ss0.mixKey ee
          -- s (encrypt the static public key with ad = h)
          let sPub? ← OpenSsl.x25519Pubkey hs.s
          match sPub? with
          | none => pure none
          | some sPub => do
            match ← ss1.encryptAndHash sPub with
            | none => pure none
            | some (ctS, ss2) => do
              -- es: responder uses its static key
              let es? ← dh hs.s re?.get!
              match es? with
              | none => pure none
              | some es => do
                let ss3 := ss2.mixKey es
                match ← ss3.encryptAndHash payload with
                | none => pure none
                | some (ctP, ss4) =>
                  pure (some (ePub ++ ctS ++ ctP, { hs with ss := ss4, e := some e }))

/-- Responder, message 3 (`-> s, se ++ payload`): 48 bytes of encrypted
static key, then the encrypted payload. Returns the payload and the final
handshake state. -/
def HandshakeState.readMsg3 (hs : HandshakeState) (msg3 : ByteArray) :
    IO (Option (ByteArray × HandshakeState)) := do
  if hs.initiator ∨ hs.re.isNone ∨ msg3.size < 48 then pure none
  else do
    let ctS := msg3.extract 0 48
    let ctP := msg3.extract 48 msg3.size
    match ← hs.ss.decryptAndHash ctS with
    | none => pure none
    | some (rs, ss1) => do
      -- se: responder uses its ephemeral against the remote static key
      let se? ← dh hs.e.get! rs
      match se? with
      | none => pure none
      | some se => do
        let ss2 := ss1.mixKey se
        match ← ss2.decryptAndHash ctP with
        | none => pure none
        | some (payload, ss3) =>
          pure (some (payload, { hs with ss := ss3, rs := some rs }))

/-! ### Initiator side -/

/-- Initiator, message 1 (`-> e` + keyless payload). -/
def HandshakeState.writeMsg1 (hs : HandshakeState) (payload : ByteArray) :
    IO (Option (ByteArray × HandshakeState)) := do
  if ¬ hs.initiator then pure none
  else match ← keypair hs.efix with
    | none => pure none
    | some (e, ePub) => do
      -- -> e: mix the ephemeral, then the keyless payload
      let ss0 := hs.ss.mixHash ePub
      match ← ss0.encryptAndHash payload with
      | none => pure none
      | some (ct, ss') =>
        pure (some (ePub ++ ct, { hs with ss := ss', e := some e }))

/-- Initiator, message 2 (`<- e, ee, s, es ++ payload`): 48 bytes of
encrypted remote static key, then the encrypted payload. -/
def HandshakeState.readMsg2 (hs : HandshakeState) (msg2 : ByteArray) :
    IO (Option (ByteArray × HandshakeState)) := do
  if ¬ hs.initiator ∨ msg2.size < 48 then pure none
  else do
    let ePub := msg2.extract 0 32
    let ctS := msg2.extract 32 80
    let ctP := msg2.extract 80 msg2.size
    let ss0 := hs.ss.mixHash ePub
    -- ee
    let ee? ← dh hs.e.get! ePub
    match ee? with
    | none => pure none
    | some ee => do
      let ss1 := ss0.mixKey ee
      -- s: decrypt the remote static key (token order: s comes before es)
      match ← ss1.decryptAndHash ctS with
      | none => pure none
      | some (rs, ss2) => do
        -- es: initiator DH(ephemeral, remote static)
        let es? ← dh hs.e.get! rs
        match es? with
        | none => pure none
        | some es => do
          let ss3 := ss2.mixKey es
          match ← ss3.decryptAndHash ctP with
          | none => pure none
          | some (payload, ss4) =>
            pure (some (payload, { hs with ss := ss4, rs := some rs, re := some ePub }))

/-- Initiator, message 3 (`-> s, se ++ payload`). -/
def HandshakeState.writeMsg3 (hs : HandshakeState) (payload : ByteArray) :
    IO (Option (ByteArray × HandshakeState)) := do
  if ¬ hs.initiator ∨ hs.e.isNone then pure none
  else do
    let sPub? ← OpenSsl.x25519Pubkey hs.s
    match sPub? with
    | none => pure none
    | some sPub => do
      match ← hs.ss.encryptAndHash sPub with
      | none => pure none
      | some (ctS, ss1) => do
        -- se: initiator uses its static key against the remote ephemeral
        let se? ← dh hs.s hs.re.get!
        match se? with
        | none => pure none
        | some se => do
          let ss2 := ss1.mixKey se
          match ← ss2.encryptAndHash payload with
          | none => pure none
          | some (ctP, ss3) =>
            pure (some (ctS ++ ctP, { hs with ss := ss3 }))

/-! ## The libp2p payload -/

/-- Data signed by the identity key: the prefix then the static Noise public
key (noise spec, "Static Key Authentication"). -/
def sigInput (staticPub : ByteArray) : ByteArray :=
  Bytes.ofString "noise-libp2p-static-key:" ++ staticPub

/-- Build our `NoiseHandshakePayload`. -/
def buildPayload (identity : Keys.PrivKey) (staticPub : ByteArray)
    (muxers : List String) : IO (Option ByteArray) := do
  let sig? ← identity.sign (sigInput staticPub)
  match sig? with
  | none => pure none
  | some sig =>
    match ← identity.publicKey with
    | none => pure none
    | some pub =>
      pure (some (Messages.encodeNoisePayloadB
        { identityKey := Bytes.toNatList (Keys.marshalPubKey pub)
          identitySig := Bytes.toNatList sig
          extensions := some { webtransportCerthashes := [], streamMuxers := muxers } }))

/-- Validate a received `NoiseHandshakePayload`: decode it, check the
signature over `sigInput staticPub` and return the identity key together
with the muxers the peer advertised in its extensions (empty when absent). -/
def verifyPayload (payload : ByteArray) (staticPub : ByteArray) :
    IO (Option (Keys.PubKey × List String)) := do
  match Messages.decodeNoisePayload? payload with
  | none => pure none
  | some p =>
    match Keys.unmarshalPubKey? (Bytes.ofNatList p.identityKey) with
    | none => pure none
    | some pub => do
      if ← pub.verify (sigInput staticPub) (Bytes.ofNatList p.identitySig) then
        pure (some (pub, (p.extensions.map (·.streamMuxers)).getD []))
      else pure none

/-! ## The security transport -/

/-- The default muxer list advertised in the handshake extension. -/
def defaultMuxers : List String := ["/yamux/1.0.0", "/mplex/6.7.0"]

/-- Wrap a connection in the two transport cipher states. Reads go through
the same buffered reader the handshake used. -/
def secureConnR (reader : BufReader) (conn : Connection)
    (enc₀ dec₀ : CipherState) : IO Connection := do
  let enc ← IO.mkRef enc₀
  let dec ← IO.mkRef dec₀
  let read : IO (Option ByteArray) := do
    match ← readFramed reader with
    | none => pure none
    | some ct => do
      let d ← dec.get
      match ← d.decrypt ByteArray.empty ct with
      | none => pure none
      | some (pt, d') => dec.set d'; pure (some pt)
  let write := fun (b : ByteArray) => do
    -- chunk plaintext into frames of at most maxMessage - 16 bytes (the
    -- Noise spec's 65535 cap includes the 16-byte Poly1305 tag)
    let chunkSize := maxMessage - 16
    let mut off := 0
    while off < b.size do
      let len := min chunkSize (b.size - off)
      let e ← enc.get
      let chunk := b.extract off (off + len)
      match ← e.encrypt ByteArray.empty chunk with
      | none => break
      | some (ct, e') => enc.set e'; writeFramed conn ct
      off := off + len
  pure { read := read, write := write, close := conn.close,
         localAddr := conn.localAddr, remoteAddr := conn.remoteAddr }

def roleIsInitiator : Role → Bool
  | .initiator => true
  | .responder => false

/-- The noise-libp2p handshake over `conn`; returns an encrypted connection
with the verified remote peer id. `muxers` is what we advertise in the
handshake extension - keep it equal to the host's actual muxer list so the
remote's extension-based selection can only land on a muxer we have. -/
def handshake (identity : Keys.PrivKey) (staticPriv : ByteArray)
    (role : Role) (conn : Connection)
    (muxers : List String := defaultMuxers) : IO (Option SecureConn) := do
  let hs? ← HandshakeState.init (roleIsInitiator role) staticPriv
  match hs? with
  | none => pure none
  | some hs0 =>
    let localStaticPub? ← OpenSsl.x25519Pubkey staticPriv
    match localStaticPub? with
    | none => pure none
    | some localStaticPub =>
    let payload? ← buildPayload identity localStaticPub muxers
    match payload? with
    | none => pure none
    | some localPayload =>
    let reader ← BufReader.ofConn conn
    if roleIsInitiator role then
      -- -> e
      match ← hs0.writeMsg1 ByteArray.empty with
      | none => pure none
      | some (m1, hs1) => do
        writeFramed conn m1
        -- <- e, ee, s, es ++ payload
        match ← readFramed reader with
        | none => pure none
        | some w2 => do
          match ← hs1.readMsg2 w2 with
          | none => pure none
          | some (remotePayload, hs2) => do
            let remoteKey? ← verifyPayload remotePayload hs2.rs.get!
            match remoteKey? with
            | none => pure none
            | some (remoteKey, remoteMuxers) => do
              -- -> s, se ++ payload
              match ← hs2.writeMsg3 localPayload with
              | none => pure none
              | some (m3, hs3) => do
                writeFramed conn m3
                let (k1, k2) := hs3.ss.split
                let c ← secureConnR reader conn k1 k2
                let some localPub ← identity.publicKey | pure none
                pure (some
                  { toConnection := c
                    localPeer := PeerId.ofPublicKey localPub
                    remotePeer := PeerId.ofPublicKey remoteKey
                    remoteMuxers := remoteMuxers })
    else
      match ← readFramed reader with
      | none => pure none
      | some w1 => do
        match ← hs0.readMsg1 w1 with
        | none => pure none
        | some (_, hs1) => do
          match ← hs1.writeMsg2 localPayload with
          | none => pure none
          | some (m2, hs2) => do
            writeFramed conn m2
            match ← readFramed reader with
            | none => pure none
            | some w3 => do
              match ← hs2.readMsg3 w3 with
              | none => pure none
              | some (remotePayload, hs3) => do
                let remoteKey? ← verifyPayload remotePayload hs3.rs.get!
                match remoteKey? with
                | none => pure none
                | some (remoteKey, remoteMuxers) => do
                  let (k1, k2) := hs3.ss.split
                  let c ← secureConnR reader conn k2 k1
                  let some localPub ← identity.publicKey | pure none
                  pure (some
                    { toConnection := c
                      localPeer := PeerId.ofPublicKey localPub
                      remotePeer := PeerId.ofPublicKey remoteKey
                      remoteMuxers := remoteMuxers })

/-- The noise-libp2p `SecurityProtocol` over a per-connection static key.
`muxers` is advertised in the handshake extension (see `handshake`). -/
def security (identity : Keys.PrivKey) (staticPriv : ByteArray)
    (muxers : List String := defaultMuxers) : SecurityProtocol where
  name := "/noise"
  handshake := fun role conn => handshake identity staticPriv role conn muxers

end LeanP2P.Noise
