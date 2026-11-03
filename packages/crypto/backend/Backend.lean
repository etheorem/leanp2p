import Backend.Error
import Backend.Sized
import Backend.Sym
import Backend.Sign
import Backend.X509

/-!
# Backend

The OpenSSL 3 shim behind the crypto interface (root ARCHITECTURE
§4.6): one C file, `c/p2pcrypto.c`, and the `@[extern]` bindings over
it. Production callers import the `Crypto` facade, never this root
(§3.6). This package's own suite imports it directly. The package docs
live under `docs/` beside this file.

This directory is a nested Lake package with its own `lakefile.lean`,
because the C build is the one target the root `lakefile.toml` cannot
express.
-/
