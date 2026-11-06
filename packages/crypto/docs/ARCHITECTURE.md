# leanp2p crypto facade: architecture

The `Crypto` library is the one crypto import of every caller (root
ARCHITECTURE §3.6). It names the production implementation of each
primitive and holds the `Rng` seam (§3.1). It lives at the group
directory, beside the two leaf packages: `crypto/backend`, the OpenSSL
3 shim, and `crypto/pure`, the audited copies. The etheorem hazmat pins
are the third source. This pair is the facade's own record (§2). The
two leaf pairs keep their sides of the relation, and they point here
for the routes and the cross-check.

## Modules

| Module | Holds, and why |
|---|---|
| `Crypto.lean` | the route table: one `export` or `abbrev` line per primitive, and the imports of the sources |
| `Crypto/P256.lean` | the route for ECDSA P-256 verification: the adapter from the SPKI key and the DER signature to the raw `(hash, r, s, qx, qy)` interface of `LeanHazmatP256` |
| `Crypto/Rng.lean` | the `Rng` seam, its production value over `randomBytes`, and the seeded test value |

The route table stays a list of one-line routes, so a reader sees every
production choice on one screen. The P-256 adapter is code with its own
contract, so it gets its own module. The seam is a structure with two
values, and §3.1 puts it here. All declarations live in the `Crypto`
namespace.

## Routes

| Primitive | Production route | Why |
|---|---|---|
| SHA-1, SHA-512, HMAC-SHA-256, HKDF-SHA-256 | `crypto/backend` | §4.6: the backend is the production path for every primitive it binds |
| SHA-256 | `crypto/backend`, the interim fallback | the `LeanHazmatSha256` pin is out (backend PLAN, "Pin outcomes") |
| keccak-256 | `LeanHazmatKeccak` | §4.6. No own shim exists. |
| ECDSA P-256 verify | `LeanHazmatP256`, through `Crypto/P256.lean` | §4.6. The backend PLAN, "Pin outcomes", gives the adapter to this unit. |
| ECDSA P-256 derive, re-encode, sign, key generation | `crypto/backend` | the etheorem family binds verification only |
| secp256k1 derive, point check, sign over a message or a digest, verify, key generation | `crypto/backend` | the etheorem verifier accepts a high S, and §4.6 requires a low S (backend PLAN, "Pin outcomes") |
| Ed25519, X25519, RSA, ChaCha20-Poly1305, X.509, random bytes, the other generators | `crypto/backend` | no other source binds them |

The facade also re-exports the types of the backend: `CryptoError`,
`Key32`, `Digest32`, `Nonce12`, and `Certificate`, with their checked
constructors. A caller then needs no second import to build an
argument or to match an error.

## Public surface

Every name in the route table keeps the type of its production source,
so the facade adds no lift and no wrapper. A route to another source
keeps that type too. The swap rule of §3.6 depends on it. To move a
primitive, change the right-hand side of one line, and the new source
must fit the stated type. The suite demonstrates one such swap (PLAN,
"Test milestones").

`keccak256` keeps the etheorem type `ByteArray → ByteArray`, with no
`Except`. The etheorem shim has no failure arm for a digest. A wrapper
that invents one adds an error arm that no input reaches.

## Owned contracts

1. **The facade is the only crypto import above the crypto group.** No
   module outside `packages/crypto/` imports `Backend`, `CryptoPure`,
   or a `LeanHazmat` package (§3.6). Rule 4 of
   `scripts/lint-imports.sh` checks it, and it reads every module of a
   line with several `import` commands. The suites under `Tests/` are
   exempt, because they test the sources one by one.
2. **The P-256 route accepts what go-libp2p accepts.** The verifier
   takes the key as SubjectPublicKeyInfo DER, the form the backend
   verifier takes. go-libp2p parses the key with `x509.ParsePKIXPublicKey`
   (`vendor/go-libp2p/core/crypto/ecdsa.go`, line 103). Go's
   `crypto/x509` then parses the point with
   `ecdsa.ParseUncompressedPublicKey` (go1.27.3,
   `crypto/x509/parser.go`, line 355), so a compressed or a hybrid
   point fails there. The route accepts exactly the 91-byte SPKI of an
   uncompressed P-256 point. The signature must be strict DER (X.690
   §10): one SEQUENCE of two minimal positive INTEGERs, and no
   trailing byte. Each rule has a differential case against the
   backend verifier.
3. **The verifier fold holds through the route.** The route returns
   `Bool`. `false` covers a key or a signature that does not parse, a
   SHA-256 fault, and a signature that does not verify (backend
   ARCHITECTURE, "Trust boundary").
4. **The seeded `Rng` replays.** The sequence of a seed is one byte
   stream, and a draw takes the next `n` bytes of it. Two values from
   one seed give the same bytes for the same total drawn, however the
   caller splits its draws. A caller refactor then keeps its fixtures.
   The value keeps its byte offset in a `Conc.OnceRef`, and each draw
   claims its range with one `updateGet`. Two tasks that draw at once
   never receive the same bytes (§4.1, rule 3).
5. **The cross-check covers every family both sides implement.**
   SHA-1, SHA-256, SHA-512, HMAC-SHA-256, and HKDF-SHA-256 run through
   the pure copies and the production path, and the answers agree
   (PLAN, "Test milestones"). Ed25519, ChaCha20-Poly1305, and
   keccak-256 have no pure copy, so their vectors pin them (backend
   PLAN, unit 2 milestones).

## Decisions

- **The P-256 route keeps SHA-256 inside the primitive.** ECDSA P-256
  in libp2p signs SHA-256 of the message, and the backend verifier
  hashes inside OpenSSL. The route hashes with `Backend.sha256`. The
  hash is part of the routed primitive, so a swap of the facade's
  `sha256` line leaves the route unchanged.
- **Both P-256 verifiers take the uncompressed point only.** OpenSSL
  loads a compressed or hybrid point from an SPKI, and go-libp2p
  rejects both (contract 2). One check, `Backend.p256SpkiUncompressed`,
  holds the rule. The route and `Backend.p256Verify` both call it, so
  the layout has one home. The two verifiers then agree, and a swap
  back to the backend changes no answer.
- **The seeded `Rng` hashes with the backend SHA-256.** Block `i` of a
  seed is SHA-256(seed ‖ `i` as 8 big-endian bytes). SHA-256 is one
  fixed function, so the bytes are the same on every machine. The
  backend binding keeps the facade free of a `crypto/pure` import, and
  the pure copies stay the oracles of the cross-check.
- **The cross-check lives in the test tree.** Root PLAN W3.3 asks for
  the comparison at the IO edge. `Tests/CryptoCross.lean` imports the
  facade and the pure package. It is the one module that imports both
  implementations.

## What the facade must not depend on

- No group to its left: no net and no libp2p (§2). Rule 2 of the lint
  keeps that word out of every `.lean` file of the group.
- From `base`, `base/conc` only, for the `OnceRef` of the seeded `Rng`.
- No codec. A route moves bytes. The framing of a key or a digest
  belongs to the caller.
- No `crypto/pure` in the library. The pure copies enter through the
  cross-check suite only.
