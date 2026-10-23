import LeanP2P.Crypto.OpenSsl
import LeanP2P.Crypto.Pb
import LeanP2P.Crypto.PeerId
import LeanP2P.Crypto.Cid
import LeanP2P.Crypto.Base58
import LeanP2P.Crypto.Multibase
/-!
# Keys and PeerId (VECTOR_TEST_PLAN.md, phase 2 step 13)

The four libp2p key types with the peer-ids spec's marshaling:

- `PublicKey` / `PrivateKey` protobuf: `required KeyType Type = 1`,
  `required bytes Data = 2` (vendor/specs/peer-ids). Encoding is
  deterministic as the spec demands: minimal varints, tag order, all
  fields - `Pb.encodeFields` by construction.
- `Data` per type (matching the go-libp2p fixtures in
  `vendor/go-libp2p/core/crypto/test_data`): Ed25519 raw 32-byte public
  key (private: 64-byte seed||public, 32-byte seed or legacy 96-byte
  seed||pub||pub accepted); secp256k1 33-byte compressed public and
  32-byte scalar private; ECDSA P-256 SPKI public and SEC1 (RFC 5915;
  PKCS#8 accepted on import) private; RSA SPKI public and PKCS#1
  private.
- Signing: Ed25519 (RFC 8032), secp256k1 BIP-62 low-S DER over
  SHA-256(msg), ECDSA P-256 DER over SHA-256(msg), RSA
  RSASSA-PKCS1-v1_5 over SHA-256(msg) - all through the OpenSSL backend.
- `PeerId.ofPublicKey`: marshal the public key; at most 42 bytes -> identity
  multihash (so every Ed25519 id is a `12D3KooW...` id), otherwise
  sha2-256 (peer-ids spec, "Peer Ids").
- String forms: legacy base58btc multihash and CIDv1 `libp2p-key`
  multibase (base32 by default, base36 accepted); parsing accepts both and
  validates the multicodec and the peer multihash shape.
-/

namespace LeanP2P.Keys

/-! ## Key types -/

/-- The peer-ids `KeyType` enum. -/
inductive KeyType where
  | rsa        -- 0
  | ed25519    -- 1
  | secp256k1  -- 2
  | ecdsa      -- 3
  deriving Repr, BEq, DecidableEq

instance : ToString KeyType where
  toString
    | .rsa => "rsa" | .ed25519 => "ed25519"
    | .secp256k1 => "secp256k1" | .ecdsa => "ecdsa"

def KeyType.toNat : KeyType → Nat
  | .rsa => 0 | .ed25519 => 1 | .secp256k1 => 2 | .ecdsa => 3

def KeyType.ofNat? : Nat → Option KeyType
  | 0 => some .rsa | 1 => some .ed25519 | 2 => some .secp256k1
  | 3 => some .ecdsa | _ => none

/-- A public key: type plus the `Data` encoding of its type. -/
structure PubKey where
  keyType : KeyType
  raw : ByteArray
  deriving Repr, BEq

/-- A private key: type plus the `Data` encoding of its type. -/
structure PrivKey where
  keyType : KeyType
  raw : ByteArray
  deriving Repr, BEq

/-! ## Protobuf marshaling -/

/-- A DER structure at the very least starts with a SEQUENCE tag and a
length (a 2-byte minimum); full parsing is the backend's job. -/
def derOk (d : ByteArray) : Bool :=
  d.size ≥ 8 ∧ d[0]! == 0x30

/-- Key `Data` shapes (peer-ids spec + go-libp2p): public keys - Ed25519
raw 32 bytes, secp256k1 compressed point 33 bytes, ECDSA/RSA a DER
structure (SPKI). Private keys - Ed25519 32 (seed), 64 (seed||pub) or 96
(legacy seed||pub||pub) bytes, secp256k1 32-byte scalar, ECDSA/RSA DER
(SEC1/PKCS#8, PKCS#1). A key whose data does not fit its type must not
unmarshal - a truncated key would still derive a (bogus) peer id. -/
def pubKeyDataOk (kt : KeyType) (d : ByteArray) : Bool :=
  match kt with
  | .ed25519 => d.size = 32
  | .secp256k1 => d.size = 33
  | .ecdsa => derOk d
  | .rsa => derOk d

def privKeyDataOk (kt : KeyType) (d : ByteArray) : Bool :=
  match kt with
  | .ed25519 => d.size = 32 ∨ d.size = 64 ∨ d.size = 96
  | .secp256k1 => d.size = 32
  | .ecdsa => derOk d
  | .rsa => derOk d

/-- Deterministic `PublicKey` protobuf bytes (fields in tag order, minimal
varints). -/
def marshalPubKey (k : PubKey) : ByteArray :=
  Pb.encodeFieldsB
    [(1, .varint k.keyType.toNat), (2, .bytes (Bytes.toNatList k.raw))]

def unmarshalPubKey? (b : ByteArray) : Option PubKey := do
  let fs ← Pb.decodeFieldsB? b
  let t ← Pb.getVarint? 1 fs
  let d ← Pb.getBytes? 2 fs
  let kt ← KeyType.ofNat? t
  if pubKeyDataOk kt (Bytes.ofNatList d) then
    pure { keyType := kt, raw := Bytes.ofNatList d }
  else none

/-- Deterministic `PrivateKey` protobuf bytes. -/
def marshalPrivKey (k : PrivKey) : ByteArray :=
  Pb.encodeFieldsB
    [(1, .varint k.keyType.toNat), (2, .bytes (Bytes.toNatList k.raw))]

def unmarshalPrivKey? (b : ByteArray) : Option PrivKey := do
  let fs ← Pb.decodeFieldsB? b
  let t ← Pb.getVarint? 1 fs
  let d ← Pb.getBytes? 2 fs
  let kt ← KeyType.ofNat? t
  if privKeyDataOk kt (Bytes.ofNatList d) then
    pure { keyType := kt, raw := Bytes.ofNatList d }
  else none

/-! ## Signing and verification (dispatch over the backend) -/

/-- Sign a message. Ed25519 signs the raw message; the DER schemes hash
with SHA-256 first (per the peer-ids spec). -/
def PrivKey.sign (k : PrivKey) (msg : ByteArray) : IO (Option ByteArray) := do
  match k.keyType with
  | .ed25519 =>
      -- preferred Data form: 64-byte seed||public; also accept a bare
      -- 32-byte seed and the legacy 96-byte seed||pub||pub
      let seed := k.raw.extract 0 32
      OpenSsl.ed25519Sign seed msg
  | .secp256k1 => OpenSsl.secp256k1Sign k.raw msg
  | .ecdsa => OpenSsl.ecdsaP256Sign k.raw msg
  | .rsa => OpenSsl.rsaSign k.raw msg

/-- Verify a signature. -/
def PubKey.verify (k : PubKey) (msg sig : ByteArray) : IO Bool := do
  match k.keyType with
  | .ed25519 => if k.raw.size = 32 then OpenSsl.ed25519Verify k.raw msg sig
                else pure false
  | .secp256k1 => OpenSsl.secp256k1Verify k.raw msg sig
  | .ecdsa => OpenSsl.ecdsaP256Verify k.raw msg sig
  | .rsa => OpenSsl.rsaVerify k.raw msg sig

/-- The public key of a private key (peer-ids spec: implementations SHOULD
be able to produce the public key from the private key). -/
def PrivKey.publicKey (k : PrivKey) : IO (Option PubKey) := do
  match k.keyType with
  | .ed25519 =>
      if k.raw.size = 64 then
        -- preferred: seed||public
        pure (some { keyType := .ed25519, raw := k.raw.extract 32 64 })
      else if k.raw.size = 96 then
        -- legacy: seed||public||public; the two copies must be identical
        let p1 := k.raw.extract 32 64
        let p2 := k.raw.extract 64 96
        if p1 = p2 then pure (some { keyType := .ed25519, raw := p1 })
        else pure none
      else if k.raw.size = 32 then
        match ← OpenSsl.ed25519Pubkey k.raw with
        | some pub => pure (some { keyType := .ed25519, raw := pub })
        | none => pure none
      else pure none
  | .secp256k1 =>
      match ← OpenSsl.secp256k1Pubkey k.raw with
      | some pub => pure (some { keyType := .secp256k1, raw := pub })
      | none => pure none
  | .ecdsa =>
      match ← OpenSsl.ecdsaP256PrivToPub k.raw with
      | some spki => pure (some { keyType := .ecdsa, raw := spki })
      | none => pure none
  | .rsa =>
      match ← OpenSsl.rsaPrivToPub k.raw with
      | some spki => pure (some { keyType := .rsa, raw := spki })
      | none => pure none

/-! ## Peer id derivation -/

end LeanP2P.Keys

namespace LeanP2P

/-- libp2p peer id of a public key (peer-ids spec): marshal the key; at
most 42 bytes -> identity multihash (inlined key), else sha2-256
multihash. -/
def PeerId.ofPublicKey (k : Keys.PubKey) : PeerId where
  bytes :=
    let m := Keys.marshalPubKey k
    if m.size ≤ 42 then
      Bytes.ofNatList (Multihash.identity (Bytes.toNatList m))
    else
      Bytes.ofNatList (Multihash.sha256 (Bytes.toNatList m))

/-- Legacy text form: base58btc-encoded multihash (`Qm...`,
`12D3KooW...`). -/
def PeerId.toBase58 (p : PeerId) : String :=
  Base58.encode (Bytes.toNatList p.bytes)

/-- New text form: CIDv1 with the `libp2p-key` multicodec, base32
(`bafz...`). -/
def PeerId.toCidString (p : PeerId) : String :=
  match Multihash.decode? (Bytes.toNatList p.bytes) with
  | some mh => Cid.toString (Cid.libp2pKeyV1 mh)
  | none => ""

/-- Parse a peer id (peer-ids spec "Decoding"): `1`/`Qm` prefix -> bare
base58btc multihash; otherwise multibase CIDv1 whose multicodec must be
`libp2p-key`. Both forms are validated as peer multihashes. -/
def PeerId.ofString? (s : String) : Option PeerId := do
  let cs := s.toList
  if cs.head? = some '1' ∨ s.startsWith "Qm" then
    let bs ← Base58.decode? s
    let mh ← Multihash.decode? bs
    if Multihash.validPeer mh then some { bytes := Bytes.ofNatList bs }
    else none
  else do
    let (_, bytes) ← Multibase.decode? s
    let c ← Cid.ofBytes? (Bytes.toNatList bytes)
    match c with
    | .v1 codec mh =>
        if codec = Cid.codecLibp2pKey ∧ Multihash.validPeer mh then
          some { bytes := Bytes.ofNatList (Multihash.encode mh) }
        else none
    | .v0 _ => none  -- CIDv0 text form is the Qm... branch above

end LeanP2P
