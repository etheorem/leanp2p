import Tests.Support
import Tests.Vectors

/-!
# Test entry point

One module per suite, each naming the upstream file it mirrors.
`lake test` runs the driver; the exit code is nonzero only on real
failures. Documented gaps (todo) and skipped vectors stay visible in the
summary without failing the run. The concurrency-sensitive suites also
pass under a single capability: `lake test -- +RTS -N1 -RTS`
(ARCHITECTURE §6).
-/

def main : IO UInt32 := do
  let r ← Tests.Runner.new
  Tests.Vectors.run r
  r.summary
