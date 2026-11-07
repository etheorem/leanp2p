# leanp2p crypto facade: plan

This plan refines the root `docs/PLAN.md` for the `Crypto` facade. The
root plan owns the order across packages. Unit 1 below is the root unit
W3.3. Its root dependencies are W3.1 (`crypto/pure`) and W3.2
(`crypto/backend`). Unit 2 of the backend plan is the backend side of
the same root unit, and it points here.

The done-when of each unit is
the root row plus the root definition of done. The surface follows
ARCHITECTURE §3.6 and §4.6, the owned contracts hold, and the carried
tests pass, also with `LEAN_NUM_THREADS=1`. The import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair (ARCHITECTURE §2) | written, and consistent with the root docs and the two leaf pairs |
| 1 | W3.1, W3.2 | the route table `Crypto.lean`, the P-256 route `Crypto/P256.lean`, the `Rng` seam `Crypto/Rng.lean`, rule 4 of the import lint, and the two suites below | the milestones below pass, and the root W3.3 row holds |

## Consumers

W5.1 (`libp2p/identity`) derives, signs, and verifies through the
facade. W5.3 (Noise) takes X25519, ChaCha20-Poly1305, SHA-256, and
HKDF from it, and it draws its ephemeral keys through the `Rng` seam.
Its fixed-key test value takes the seeded `Rng`. W6.1 takes
keccak-256 and secp256k1 key recovery. W5.6 signs and verifies.

## Test milestones

Every case is concrete. The suites follow the test-runner layout of
root W0.2.

- **The facade check** (`Tests/Facade.lean`): the module imports
  `Crypto` and no source package. It names every route of the
  architecture table, so the build fails on a missing name. The three
  routes that leave the backend, and the interim fallback, appear at
  their stated types. Rule 4 of the import lint holds over `packages/`.
- **The `Rng` seam** (`Tests/Facade.lean`): two seeded values from one
  seed replay the same draws, and each draw has the requested length.
  The first 32 bytes of a seed are SHA-256(seed ‖ 8 zero bytes).
  Split draws give the bytes of one joined draw. Two seeds differ, and
  two draws in a row differ. Two tasks that draw 16 times each from
  one value receive 32 distinct blocks. A draw past `maxRandomBytes`
  is `invalidInput` on both values. The production value draws
  through `randomBytes`, and two draws differ.
- **The swap demonstration** (`Tests/CryptoCross.lean`): one line
  routes `sha256` to the pure copy at the stated type of the facade.
  A call site written against the name gives the same digests under
  both routes.
- **The cross-check, direction one** (`Tests/CryptoCross.lean`): the
  vector decides. The RFC entries of `hashes-rfc.json` and the `sha1`
  and `sha2-256` digests of `multihash-examples.json` run through the
  pure copy and the production path. Both answers match the expected
  bytes. The pure HKDF extract also matches the PRK of each
  RFC 5869 entry. The sweeps of the pure plan run through both sides,
  and the answers agree:
  - SHA-256 and SHA-1 at 0, 1, 55, 56, 63, 64, 65, 119, 120, 128,
    and 1000 bytes
  - SHA-512 at 0 to 300, 511, 512, 513, 1000, and 4096 bytes
  - HMAC-SHA-256 with keys of 0, 1, 63, 64, 65, 128, and 200 bytes
  - HKDF-SHA-256 at 0, 1, 31, 32, 33, 64, and 1000 bytes, and at the
    255-block limit and one byte past it, where both sides fail
- **The cross-check, direction two** (`Tests/CryptoCross.lean`): the
  production path decides. 48 inputs per family come from the
  production `Rng`, with random lengths across the block edges. They
  run through the production path first, and the pure copy must give
  the same bytes. The families are SHA-1, SHA-256, SHA-512,
  HMAC-SHA-256, and HKDF-SHA-256 (extract and expand against the
  one-shot binding).
- **The P-256 route** (`Tests/CryptoCross.lean`), differential against
  `Backend.p256Verify`:
  - the go fixture of `keys-go-libp2p.json`: both accept
  - a tampered message: both reject
  - the high-S twin: both accept, since neither side has a low-S rule
    for P-256
  - a non-minimal INTEGER, a negative INTEGER, and a trailing byte:
    both reject
  - a long-form SEQUENCE length, a third INTEGER, a SET tag in place of
    the SEQUENCE tag, and an INTEGER longer than 32 bytes: both reject
  - a compressed and a hybrid SPKI of the fixture key: both reject,
    as go does
  - a byte string that is no SPKI, the RSA fixture, and the secp256k1
    SPKI of the strictness fixtures: both reject
  - eight fresh keys and signatures from the backend generator: both
    accept, and both reject a tampered message
- **The secp256k1 recovery route** (`Tests/CryptoCross.lean`). The
  backend binds no recovery, so the backend derivation is the
  reference. For eight fresh keys, a recovery id from 0 to 3 gives
  back the point of the signer, from the low S and from its high-S
  twin. A recovery id past 3 gives the empty answer.

## Vector stance

The unit adds no vector file. The cross-check reuses the files of the
two leaf pairs: `hashes-rfc.json`, `multihash-examples.json`,
`keys-go-libp2p.json`, and the generated `backend-strictness.json`.
The sweep inputs and the generated inputs need no provenance record.
The suite builds the sweep inputs from their lengths, and the
production `Rng` draws the generated inputs at run time.
