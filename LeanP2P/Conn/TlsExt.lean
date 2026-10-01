import LeanP2P.Crypto.Keys
import LeanP2P.Crypto.OpenSsl
import LeanP2P.Crypto.PeerId
/-!
# TLS certificate extension (VECTOR_TEST_PLAN.md, phase 3 step 17)

The libp2p TLS handshake (`/tls/1.0.0`, vendor/specs/tls/tls.md) encodes the
host key into an X.509 certificate extension with OID
`1.3.6.1.4.1.53594.1.1`, carried in a self-signed certificate:

- `SignedKey ::= SEQUENCE { publicKey OCTET STRING, signature OCTET STRING }`
  (ASN.1 DER; the OCTET STRINGS carry the serialized `PublicKey` protobuf
  and the signature);
- the signature is over the UTF-8 string `libp2p-tls-handshake:`
  concatenated with the certificate's own `SubjectPublicKeyInfo` DER;
- the peer id is derived from the embedded public key (peer-ids spec,
  identity inlining included), which the dialer verifies against the id it
  intended to reach.

DER parsing of the certificate itself (extension lookup, SPKI export,
self-signature check) goes through the OpenSSL backend - the phase 2
decision; the `SignedKey` structure is decoded in pure Lean below.
-/

namespace LeanP2P.TlsExt

/-! ## Minimal DER (ASN.1) decoder for SignedKey -/

/-- One DER TLV: tag, header length (tag + length bytes), content. -/
structure DerTlv where
  tag : Nat
  headerLen : Nat
  content : ByteArray

/-- Read one TLV at offset `i` (short and long-form lengths). -/
def Der.readTlv (bs : ByteArray) (i : Nat) : Option DerTlv := do
  let tag ← bs[i]?
  let l1 ← bs[(i + 1)]?
  if l1.toNat < 128 then
    some { tag := tag.toNat, headerLen := 2,
           content := bs.extract (i + 2) (i + 2 + l1.toNat) }
  else
    let n := l1.toNat - 128
    if n = 0 ∨ n > 4 then none
    else
      let len := (List.range n).foldl (fun acc k =>
        match bs[(i + 2 + k)]? with
        | some d => acc * 256 + d.toNat
        | none => acc) 0
      some { tag := tag.toNat, headerLen := 2 + n,
             content := bs.extract (i + 2 + n) (i + 2 + n + len) }

/-- ASN.1 tags used by SignedKey. -/
def Der.tagSequence : Nat := 0x30
def Der.tagOctetString : Nat := 0x04

/-- `SignedKey ::= SEQUENCE { publicKey OCTET STRING, signature OCTET STRING }` -/
def decodeSignedKey? (der : ByteArray) : Option (ByteArray × ByteArray) := do
  let seq ← Der.readTlv der 0
  if seq.tag != Der.tagSequence then none
  let k ← Der.readTlv seq.content 0
  let s ← Der.readTlv seq.content (k.headerLen + k.content.size)
  if k.tag != Der.tagOctetString ∨ s.tag != Der.tagOctetString then none
  some (k.content, s.content)

/-! ## Certificate validation -/

structure CertKey where
  /-- The host public key from the extension (the peer id is derived from it). -/
  pubKey : Keys.PubKey
  /-- The certificate's own SPKI DER (part of the signed data). -/
  spki : ByteArray

/-- Extract and validate the libp2p key of a certificate DER:
self-signature, extension lookup, `SignedKey` decode, signature over
`"libp2p-tls-handshake:" ++ SPKI`. Returns the embedded host key. -/
def validateCert (cert : ByteArray) : IO (Option CertKey) := do
  -- the certificate must be self-signed (the spec's certificates are)
  if !(← OpenSsl.x509SelfSigned cert) then
    return none
  match ← OpenSsl.x509Libp2pExt cert with
  | none => return none
  | some (spki, extValue) => do
    match decodeSignedKey? extValue with
    | none => return none
    | some (pubBytes, signature) => do
      match Keys.unmarshalPubKey? pubBytes with
      | none => return none
      | some pub => do
        let signed := Bytes.ofString "libp2p-tls-handshake:" ++ spki
        if ← pub.verify signed signature then
          return (some { pubKey := pub, spki := spki })
        else
          return none

/-- The peer id a certificate authenticates (spec: compare against the id
the connection was dialed for). -/
def CertKey.peerId (ck : CertKey) : PeerId := PeerId.ofPublicKey ck.pubKey

end LeanP2P.TlsExt
