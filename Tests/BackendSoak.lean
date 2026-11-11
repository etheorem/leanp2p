import Tests.Support
import Backend

/-!
# Backend soak (unit W3.2, sub-unit 1b)

The borrowed-argument regression of `packages/crypto/backend/docs/PLAN.md`
(contract 1). An owned `ByteArray` parameter that the shim never
releases leaks the whole argument on every call. The spike's review
measured 200,000 SHA-256 calls: RSS grew from 14 MB to 526 MB, and to
9.5 MB after the fix (PRINCIPLES 4.1).

The soak drives 200,000 calls through six borrowed bindings in turn,
each on a freshly allocated 4 KiB input:
- SHA-256
- HMAC-SHA-256
- ChaCha20-Poly1305 seal
- P-256 verify (the input is the message)
- the two X.509 helpers (the input is no certificate, so they fail at
  the parse, after the shim reads the argument)

A binding whose argument leaks costs 4 KiB on each of its calls, about
130 MiB over the run. The check passes when RSS grows by less than
32 MiB. A reused input would hide the leak, because a leaked reference
to one object costs no memory. So every call gets a new input.

RSS comes from `/proc/self/status`, so the check runs on Linux only.
Elsewhere the runner skips it and prints the reason.
-/

set_option autoImplicit false

namespace Tests

open Backend

/-- The resident set size in KiB (`VmRSS` of `/proc/self/status`), or
`none` where the file or the line is missing. -/
private def rssKiB : IO (Option Nat) := do
  let path : System.FilePath := "/proc/self/status"
  unless ← path.pathExists do return none
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.startsWith "VmRSS:" then
      return ((line.drop 6).trimAscii.takeWhile Char.isDigit).toNat?
  return none

/-- The calls of the soak. -/
def soakCalls : Nat := 200000

/-- The RSS growth the soak allows, in KiB. -/
def soakBudgetKiB : Nat := 32 * 1024

def BackendSoak.run (r : Runner) : IO Unit := do
  r.section "crypto/backend soak" "PRINCIPLES 4.1 (the borrowed-argument leak)"
  let some before ← rssKiB
    | r.skip "borrowed-argument soak" "no /proc/self/status on this system"
  let some key := Key32.ofByteArray? (ByteArray.mk (Array.replicate 32 1))
    | r.check "soak: key" false
  let some nonce := Nonce12.ofByteArray? (ByteArray.mk (Array.replicate 12 2))
    | r.check "soak: nonce" false
  -- A real uncompressed P-256 key, so `p256Verify` reaches the shim.
  let some priv := (← p256Generate.run).toOption | r.check "soak: P-256 generate" false
  let some spki := (p256PublicKey priv).toOption | r.check "soak: P-256 derive" false
  let sig := ByteArray.mk (Array.replicate 70 3)
  -- The checksum keeps every result live, so no call is dead code.
  let mut checksum : Nat := 0
  let mut errors : Nat := 0
  for i in [0:soakCalls] do
    let input := ByteArray.mk (Array.replicate 4096 (i % 251).toUInt8)
    match i % 6 with
    | 0 | 1 | 2 =>
      let out := match i % 6 with
        | 0 => sha256 input
        | 1 => hmacSha256 input input
        | _ => chachaSeal key nonce input input
      match out with
      | .ok b => checksum := checksum + (b.get! 0).toNat
      | .error _ => errors := errors + 1
    | 3 => checksum := checksum + (p256Verify spki input sig).toNat
    | 4 =>
      -- The input is no certificate: an answer other than the error
      -- counts as an error of the soak.
      match inspect input "1.3.6.1.4.1.53594.1.1" with
      | .error (.invalidCertificate .malformed) => checksum := checksum + 1
      | _ => errors := errors + 1
    | _ => checksum := checksum + (selfSigned input).toNat
  let some after ← rssKiB | r.check "soak: RSS readable after the run" false
  let grown := after - before
  r.check s!"soak: {soakCalls} borrowed calls grow RSS by {grown} KiB (budget {soakBudgetKiB} KiB)"
    (grown < soakBudgetKiB)
  r.check s!"soak: every call succeeded ({errors} errors, checksum {checksum})" (errors == 0)

end Tests
