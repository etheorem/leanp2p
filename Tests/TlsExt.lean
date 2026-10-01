import Tests.Support

/-!
# TLS certificate extension suite (VECTOR_TEST_PLAN.md, phase 3 step 17)

Mirrors the four "Test vectors" of vendor/specs/tls/tls.md: valid
self-signed certificates authenticating an ED25519, an ECDSA and a
secp256k1 peer id, plus an invalid certificate whose SignedKey signature
does not verify. For the valid ones the suite checks the derived peer id
against the spec's expected value (base58btc form).
-/

open LeanP2P Tests

namespace Tests

def TlsExtSuite.run (r : Runner) : IO Unit := do
  r.section "TLS certificate extension"
    "libp2p/specs tls/tls.md \"Test vectors\" (3 valid + 1 invalid certificate)"

  let j ← loadJson "tls-ext.json"
  let cases ← jArr "tls-ext.json" j "cases"
  for c in cases do
    let name ← jStr "tls-ext.json" c "name"
    let certHex ← jStr "tls-ext.json" c "certHex"
    let peerId? ← jStr? "tls-ext.json" c "peerId"
    let cert ← hexBytesByteArray certHex
    let ck? ← TlsExt.validateCert cert
    match peerId? with
    | some want => do
      r.check s!"tls {name}: certificate accepted" ck?.isSome
      match ck? with
      | none => r.check s!"tls {name}: peer id" false
      | some ck =>
        let got := PeerId.toBase58 ck.peerId
        r.check s!"tls {name}: peer id {want}" (got == want)
    | none =>
      r.check s!"tls {name}: invalid certificate rejected" ck?.isNone

end Tests
