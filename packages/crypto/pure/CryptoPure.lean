import CryptoPure.Constants
import CryptoPure.Preprocess
import CryptoPure.Sha256
import CryptoPure.Sha512
import CryptoPure.Sha1
import CryptoPure.Hmac
import CryptoPure.Hkdf

/-!
# CryptoPure

The pure copies of the crypto primitives (ARCHITECTURE §4.6): SHA-256,
SHA-512, SHA-1, HMAC, and HKDF, with their theorems. They are the
audited implementations and the oracles of the W3.3 cross-check.
Callers import the `Crypto` facade, never this package. The package
docs live under `docs/` beside this file.
-/
