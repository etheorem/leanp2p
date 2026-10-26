# leanp2p bytes: plan

This plan refines the root `docs/PLAN.md` for `base/bytes`. The root
plan owns the order across packages (PLAN.md, "How to read this
plan"). Unit 1 below is the root unit W1.2, and it depends on `W0`.
Its done-when is the root row plus the root definition of done: the
surface follows ARCHITECTURE §4.2 and §3.2, the contracts hold, the
carried property tests pass, the suite passes under `+RTS -N1`, and
the import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W0 | the conversions of ARCHITECTURE §4.2 (`ofNatList`, `toNatList`, `ofString`, `toString?`, `ofHex?`, `toHex`, `xorWith`), the `Codec` and `LawfulCodec` classes, the shared `DecodeError`, and the generic round-trip harness (root W1.2) | the root W1.2 row holds: the surface exists, the model pins hold, the harness closes a round-trip for a test codec, and the suite passes under `+RTS -N1` |

Unit 0 is done. Unit 1 is the only implementation unit of the
package.

## Test milestones (unit 1)

Behavior tests close unit 1. The carried tests are the byte-model
round-trips and the fuzz-equivalence shape, which move here from the
spike's multiaddr and protobuf suites (ARCHITECTURE §7, row 2). The
suite follows the root test-runner layout of W0.2, and the `-N1` pass
is required.

The package has no wire vectors of its own. The RFC and multiformats
vectors arrive with the codec packages (root W2), and the vector
infrastructure arrives with root W0.3.

- Model round-trip: `ofNatList (toNatList b) = b` for a generated
  `b : ByteArray`, and `toNatList (ofNatList l) = l` for a generated
  `l : List Nat` with values below 256.
- String round-trip: `toString? (ofString s) = some s` for a generated
  `s : String`. `toString?` returns `none` for bytes with no UTF-8
  reading, for example the single byte `0xC3`.
- Hex round-trip: `ofHex? (toHex b) = some b` for a generated
  `b : ByteArray`. An odd-length input returns `none`. A non-hex digit
  returns `none`.
- `xorWith` with a key and then with the same key again returns the
  data. An empty key returns the data unchanged. Byte `i` of the
  output equals `data[i] ^^^ key[i % key.size]`. The test checks this
  property with a 3-byte key over a 7-byte payload.
- The test codec reports both error kinds through `decode?`: an
  input cut before the value completes yields `.error .truncated`,
  and a wrong tag yields `.error .malformed`.
- The generic harness closes a round-trip for a test codec: a small
  test type carries the `Codec` instance, proves `LawfulCodec`, and
  passes the harness. This check runs before the first codec package
  uses the harness (root W2).
