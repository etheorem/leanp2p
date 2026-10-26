# leanp2p varint: plan

This plan refines the root `docs/PLAN.md` for `codec/varint`. The root
plan owns the order across packages (PLAN.md, "How to read this
plan"). Unit 1 below is the root unit W2.1, and it depends on W1.2.
Its done-when is the root row plus the root definition of done: the
surface follows ARCHITECTURE §4.3, the owned contracts hold, the
carried tests pass, the suite passes under `+RTS -N1`, and the import
lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W1.2 | the `UVarint` newtype, the model core, the instances, the theorems, and the `ByteArray` path of the package architecture (root W2.1) | the root W2.1 row holds: the encoder, the decoder, and the theorems exist, and an over-long varint is a protocol error (`malformed`) |

Unit 0 is done. Unit 1 is the only implementation unit of the
package.

## Consumers

W2.2 (`codec/proto`) and W2.3 (`codec/multiformats`) both list W2.1
among their dependencies (root PLAN). The surface freeze of unit 1 is
what lets them start. They frame their lengths through this package
and inherit its error boundary. Unit 1 is the first unit of track A,
and the root critical path runs through it. The root plan counts W2.1
among the contention points, so it goes first inside its wave.

## Test milestones (unit 1)

Behavior tests close unit 1. The suite follows the root test-runner
layout of W0.2, and the `-N1` pass is required.

- The spec examples for 1, 127, 128, and 300 match a fixed table:
  `0x01`, `0x7F`, `0x80 0x01`, and `0xAC 0x02`, in the model form and
  in the `ByteArray` form. Zero follows from the rule: the encoding
  is the single terminator byte `0x00`. The values 255 and 16384
  arrive with the vector suite (root W0.3).
- A non-minimal form is rejected as `malformed`: `0x80 0x00` for zero
  and `0x81 0x00` for one.
- A 10-byte prefix, nine continuation bytes and one more, is rejected
  as `malformed`.
- A cut prefix is reported as `truncated`; the single byte `0x80` is
  the example.
- The `ByteArray` path is pinned to the model over generated inputs:
  the value, the error kind, and the consumed length agree with
  `decode? (toNatList b)`.
- Round-trip over generated values inside the budget, through the
  generic harness of `base/bytes`: `decode? (encode v)` returns `v`
  and no rest, and the model pin passes once for `UVarint`. The
  package writes no round-trip loop of its own (`base/bytes` docs,
  owned contract 2).

## Vector stance

Unit 1 runs the varint vector suite through the W0.3 infrastructure.
The suite holds the RFC examples and the recorded counterexample
`0x81 0x00` (`VECTORS.lock`; ARCHITECTURE §6, §7 row 3). The fixed
table and the property tests above are the package's own additions on
top of the suite.
