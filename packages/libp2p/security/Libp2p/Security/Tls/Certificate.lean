import Crypto
import Bytes
import Libp2p.Identity
import Libp2p.Security.Tls.Constants
import Libp2p.Security.Tls.SignedKey

/-!
# The libp2p certificate

A libp2p TLS endpoint proves its host key through a self-signed X.509
certificate (the TLS spec, "Peer Authentication"). The certificate's
own key is a fresh one, unrelated to the host key, and the host key
travels in the libp2p Public Key Extension as a `SignedKey`: the
marshaled host public key, and the host key's signature over
`signaturePrefix` and the certificate's SubjectPublicKeyInfo.

This module issues our certificate (`Identity.issue`) and checks the
peer's (`verify`). Both run over the `Crypto` facade, whose X.509
helpers parse and sign the DER (root ARCHITECTURE §3.6, §4.6).

## The checks, in order

Each MUST of the spec maps to one step of `verify`, and each step has
its own error arm:

1. The certificate parses, carries the extension, carries no extension
   twice, and carries no unknown critical extension (`Crypto.inspect`):
   "Endpoints MUST abort the connection attempt if the certificate
   contains critical extensions that the endpoint does not understand",
   and "If this extension is missing, endpoints MUST abort". The
   backend names the broken rule, and each rule has its own arm.
2. The self-signature verifies (`Crypto.selfSigned`): "Endpoints MUST
   abort the connection attempt if … the certificate's self-signature
   is not valid".
3. The time is inside NotBefore and NotAfter: "an endpoint MUST check
   these conditions and abort the connection attempt if (a) the
   presented certificate is not yet valid, OR (b) if it is expired".
4. The extension value decodes as a `SignedKey`, and its public key
   unmarshals as a libp2p `PublicKey`.
5. The host key's signature verifies over the prefix and the
   certificate's SPKI: "Peers MUST verify the signature, and abort the
   connection attempt if signature verification fails".
6. The peer id derives from the host key.

The chain rule ("Endpoints MUST abort the connection attempt if more
than one certificate is received") is the TLS engine's, since only the
handshake sees the chain (`net/tls`, the verify callback). The check
of the derived peer id against the expected one belongs to the
upgrader, as for Noise (root §4.9).

The spike's `Conn/TlsExt.lean` ran these checks with two differences.
Its shim checked the validity window against the process clock, with
both ends outside the window. Here the caller gives the time, and both
ends belong to the window (RFC 5280 §4.1.2.5). Its shim refused every
critical extension but the libp2p one, the ones OpenSSL understands
included. Here the backend accepts the understood ones.
-/

set_option autoImplicit false

namespace Libp2p.Security.Tls

open Libp2p.Identity

/-- Why a peer certificate failed the libp2p checks (the module doc,
"The checks, in order"). -/
inductive CertError where
  /-- The DER does not parse as one certificate. -/
  | malformed
  /-- The libp2p Public Key Extension is missing. -/
  | missingExtension
  /-- An extension appears twice (RFC 5280 §4.2). -/
  | duplicateExtension
  /-- An extension is critical, and we do not understand it. -/
  | unknownCriticalExtension
  /-- The self-signature does not verify. -/
  | selfSignature
  /-- The time is before NotBefore. -/
  | notYetValid
  /-- The time is after NotAfter. -/
  | expired
  /-- The extension value is no DER `SignedKey`. -/
  | extension
  /-- The `SignedKey` public key is no libp2p `PublicKey`. -/
  | publicKey (e : Identity.Error)
  /-- The host key's signature over the certificate key does not
  verify. -/
  | signature
  /-- The host key derives no peer id. -/
  | peerId (e : Identity.Error)
  deriving Repr

/-- The error as text, for the detail of a `Core.Error`. -/
def CertError.toString : CertError → String
  | .malformed => "the certificate does not parse"
  | .missingExtension => "the certificate lacks the libp2p extension"
  | .duplicateExtension => "the certificate carries an extension twice"
  | .unknownCriticalExtension => "the certificate carries an unknown critical extension"
  | .selfSignature => "the certificate's self-signature does not verify"
  | .notYetValid => "the certificate is not yet valid"
  | .expired => "the certificate has expired"
  | .extension => "the libp2p extension holds no SignedKey"
  | .publicKey e => s!"the libp2p extension holds no public key: {repr e}"
  | .signature => "the host key's signature over the certificate key does not verify"
  | .peerId e => s!"the host key derives no peer id: {repr e}"

instance : ToString CertError := ⟨CertError.toString⟩

/-- The `CertError` of a refusal by `Crypto.inspect`. `inspect` answers
`invalidInput` only for a required OID that does not parse, and
`extensionOid` parses, so every other error reads as `malformed`,
fail-closed. -/
private def CertError.ofInspect : Crypto.CryptoError → CertError
  | .invalidCertificate .missingExtension => .missingExtension
  | .invalidCertificate .duplicateExtension => .duplicateExtension
  | .invalidCertificate .unknownCriticalExtension => .unknownCriticalExtension
  | _ => .malformed

/-- The bytes the host key signs: the prefix, then the certificate's
SubjectPublicKeyInfo DER. -/
def signedData (spki : ByteArray) : ByteArray :=
  signaturePrefix.toUTF8 ++ spki

/-- What the checks of a peer certificate prove: the host key and the
peer id it derives. -/
structure Verified where
  /-- The host public key from the extension. -/
  publicKey : PubKey
  /-- The peer id of the host key. -/
  peer : PeerId

/-- Check a peer certificate (DER) at `now`, seconds since the Unix
epoch (the module doc, "The checks, in order"). -/
def verify (der : ByteArray) (now : Int) : Except CertError Verified := do
  let cert ← (Crypto.inspect der extensionOid).mapError CertError.ofInspect
  unless Crypto.selfSigned der do throw .selfSignature
  if now < cert.notBefore then throw .notYetValid
  if cert.notAfter < now then throw .expired
  let some sk := SignedKey.decode? (Bytes.toNatList cert.extension) | throw .extension
  let pub ← (PubKey.unmarshal? (Bytes.ofNatList sk.publicKey)).mapError .publicKey
  unless pub.verify (signedData cert.spki) (Bytes.ofNatList sk.signature) do
    throw .signature
  let peer ← (PeerId.ofPubKey pub).mapError .peerId
  return { publicKey := pub, peer }

/-- Why issuing our own certificate failed. -/
inductive IssueError where
  /-- The host key gives no public key. -/
  | publicKey (e : Identity.Error)
  /-- The host key could not sign the certificate key. -/
  | sign (e : Identity.Error)
  /-- The `SignedKey` exceeds `maxDerLength`: the host key or its
  signature is too long for the extension. -/
  | encode
  /-- The backend could not derive the certificate key's SPKI, draw a
  certificate key, or issue the certificate. -/
  | backend (e : Crypto.CryptoError)
  deriving Repr

/-- The error as text, for a log line or a test failure. -/
def IssueError.toString : IssueError → String
  | .publicKey e => s!"the host key gives no public key: {repr e}"
  | .sign e => s!"signing the certificate key failed: {repr e}"
  | .encode => "the SignedKey exceeds the DER length cap"
  | .backend e => s!"the backend could not issue the certificate: {repr e}"

instance : ToString IssueError := ⟨IssueError.toString⟩

/-- Our side of the handshake: the certificate and its private key,
both DER. -/
structure Identity where
  /-- The self-signed certificate that carries our host key. -/
  certificate : ByteArray
  /-- The certificate's own P-256 private key, SEC1 DER. -/
  certificateKey : ByteArray

/-- Issue our certificate for the host key `key` on the certificate key
`certKey` (P-256, SEC1 DER), valid from `backdateSeconds` before `now`
for `validitySeconds`. The extension is non-critical, as go-libp2p
marks it (`extensionCritical`, `vendor/go-libp2p/p2p/security/tls/crypto.go`,
line 30); the spec allows both. -/
def Identity.issue (key : PrivKey) (certKey : ByteArray) (now : Int) :
    ExceptT IssueError IO Identity := do
  let spki ← ExceptT.mk (pure ((Crypto.p256PublicKey certKey).mapError .backend))
  let pub ← ExceptT.mk (pure (key.toPublic.mapError .publicKey))
  let sig ← ExceptT.mk ((·.mapError .sign) <$> (key.sign (signedData spki)).run)
  let sk : SignedKey := { publicKey := Bytes.toNatList pub.marshal, signature := Bytes.toNatList sig }
  let some value := sk.encode? | throw .encode
  let cert ← ExceptT.mk ((·.mapError .backend) <$>
    (Crypto.issue certKey extensionOid (Bytes.ofNatList value) false
      (now - backdateSeconds) (now + validitySeconds)).run)
  return { certificate := cert, certificateKey := certKey }

/-- Issue our certificate on a fresh P-256 certificate key. The spec
asks for a key unrelated to the host key ("SHOULD NOT be related"),
and a fresh key is one. -/
def Identity.generate (key : PrivKey) (now : Int) : ExceptT IssueError IO Identity := do
  let certKey ← ExceptT.mk ((·.mapError .backend) <$> Crypto.p256Generate.run)
  Identity.issue key certKey now

end Libp2p.Security.Tls
