import Libp2p.Core.ProtocolId

/-!
# The TLS constants

The ids, names, and numbers of the libp2p TLS spec
(`vendor/specs/tls/tls.md`) that this package uses, each with one home
(PRINCIPLES 1.5). The spec fixes the protocol id, the extension OID,
the signature prefix, and the ALPN name. The certificate's validity
times follow go-libp2p, since the spec only asks that a certificate be
valid when the peer receives it; each docstring says which.
-/

set_option autoImplicit false

namespace Libp2p.Security.Tls

/-- The id that multistream-select negotiates for TLS ("Handshake
Protocol": "it MUST be identified with the following protocol ID"). -/
def protocolId : Core.ProtocolId := ⟨"/tls/1.0.0"⟩

/-- The OID of the libp2p Public Key Extension, which IANA allocated
to the libp2p project ("libp2p Public Key Extension"). -/
def extensionOid : String := "1.3.6.1.4.1.53594.1.1"

/-- The prefix of the signed data: the UTF-8 string, then the
certificate's SubjectPublicKeyInfo DER ("libp2p Public Key
Extension"). -/
def signaturePrefix : String := "libp2p-tls-handshake:"

/-- The ALPN protocol of libp2p ("ALPN"; the QUIC spec, "ALPN"). -/
def alpn : String := "libp2p"

/-- How far back NotBefore lies, one hour, so a peer whose clock runs
behind ours still finds the certificate valid. go-libp2p sets the same
(`certTemplate`, `vendor/go-libp2p/p2p/security/tls/crypto.go`, line
280: `NotBefore: time.Now().Add(-time.Hour)`). -/
def backdateSeconds : Nat := 3600

/-- The lifetime of our certificate, 100 years of 365 days, as
go-libp2p's `certValidityPeriod` (`crypto.go`, line 25). A certificate
lives as long as its identity, and the spec asks no rotation. -/
def validitySeconds : Nat := 100 * 365 * 24 * 3600

/-- The largest DER length this package reads or writes: 65535 bytes,
two length bytes. A `SignedKey` holds a marshaled public key and a
signature, and the largest of both, an RSA-8192 key and its signature,
stays near 2 KiB. A declared length past the cap is a malformed value
(root §5.1). -/
def maxDerLength : Nat := 65535

end Libp2p.Security.Tls
