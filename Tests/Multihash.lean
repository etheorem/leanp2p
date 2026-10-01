import Tests.Support
import Tests.Multibase

/-!
# Multihash + SHA-256 + CID suite

Mirrors: multiformats/multihash README example vectors (sha1, sha2-256 over
"multihash", in hex / base32pad-upper / base58btc / base64pad), pinned in
VECTORS.lock. SHA-256 correctness is additionally anchored by the NIST
example vectors hand-copied below (NIST publishes them as CSV, not in any
vendored repository).

Phase 1 steps 6-7: base32 / base64 forms now run through the Multibase
module, sha1 is implemented, and multihash decoding validates the function
code and digest length strictly. The peer-id CID forms from the peer-ids
spec (`bafz...` CIDv1 libp2p-key base32 and the bare base58btc multihash
`Qm...`) round-trip to the same multihash.
-/

open LeanP2P Tests

namespace Tests

/-- NIST FIPS 180 / "SHA Example Vectors" (csrc.nist.gov), sha256 over the
ASCII strings "abc" and the 56-bit "abcdbcdecdefdefgefghfghighijhi
jkijkljklmklmnlmnomnopnopq" message, plus the empty string. -/
def nistSha256 : List (String × String) :=
  [("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
   ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
   ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
     "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")]

def Multihash.run (r : Runner) : IO Unit := do
  r.section "multihash"
    "multiformats/multihash README.md (\"multihash\" examples) + NIST sha256 vectors \
     + peer-ids spec CID forms"

  -- NIST SHA-256 reference vectors.
  for (msg, hex) in nistSha256 do
    let want ← hexBytes hex
    r.check s!"sha256 nist \"{msg}\""
      (Sha256.digest (Bytes.toNatList (Bytes.ofString msg)) == want)

  -- Multihash README example vectors (all four encodings, both algorithms).
  let j ← loadJson "multihash-examples.json"
  for c in (← jArr "multihash-examples.json" j "cases") do
    let alg ← jStr "multihash-examples.json" c "algorithm"
    let input ← jStr "multihash-examples.json" c "input"
    let msg := Bytes.toNatList (Bytes.ofString input)
    for e in (← jArr "multihash-examples.json" c "encodings") do
      let kind ← jStr "multihash-examples.json" e "kind"
      let value ← jStr "multihash-examples.json" e "value"
      let name := s!"multihash {alg} of \"{input}\" as {kind}"
      match alg, kind with
      | "sha1", "hex" =>
        let want ← hexBytes value
        r.check name (Multihash.sha1 msg == want)
      | "sha2-256", "hex" =>
        let want ← hexBytes value
        r.check name (Multihash.sha256 msg == want)
      | alg, kind =>
        -- base32pad-upper / base58btc / base64pad go through Multibase
        let (multibaseKind, mhBytes) :=
          if alg == "sha1" then (kind, Multihash.sha1 msg)
          else (kind, Multihash.sha256 msg)
        -- the README values carry NO multibase prefix: strip it from the
        -- encoding and prepend it for decoding
        match mbKind? multibaseKind with
        | none => r.skip name
        | some base =>
            let enc := Multibase.encode base (Bytes.ofNatList mhBytes)
            r.check name ((enc.drop 1).toString == value)
            let prefixed := String.singleton (Multibase.prefixChar base) ++ value
            match Multibase.decode? prefixed with
            | some (b, out) =>
                r.check s!"{name} decode" (out == Bytes.ofNatList mhBytes)
                r.check s!"{name} decode base" (b == base)
            | none => r.check s!"{name} decode" false

  -- Multihash codec: identity / sha256 wrap / strict decode round trip.
  let hello ← hexBytes "000568656c6c6f"
  r.check "multihash identity"
    (Multihash.identity (Bytes.toNatList (Bytes.ofString "hello")) == hello)
  let specMh ← hexBytes "12209cbc07c3f991725836a3aa2a581ca2029198aa420b9d99bc0e131d9f3e2cbe47"
  r.check "multihash sha256 wrap"
    (Multihash.sha256 (Bytes.toNatList (Bytes.ofString "multihash")) == specMh)
  let digest := Sha256.digest (Bytes.toNatList (Bytes.ofString "multihash"))
  r.check "multihash decode roundtrip"
    (Multihash.decode? specMh == some { code := 0x12, digest })
  -- strict decode: length mismatch / trailing bytes / unknown code rejected
  r.check "multihash rejects trailing bytes"
    (Multihash.decode? (specMh ++ [0x00]) == none)
  r.check "multihash rejects unknown code" (Multihash.decode? [0x99, 0x00] == none)
  r.check "multihash rejects truncated digest" (Multihash.decode? (specMh.take 10) == none)

  -- peer-ids spec: the two spellings of the same peer id
  let qm := "QmYyQSo1c1Ym7orWxLYvCrM2EmxFTANf8wXmmE7DWjhx5N"
  let bafz := "bafzbeie5745rpv2m6tjyuugywy4d5ewrqgqqhfnf445he3omzpjbx5xqxe"
  match Cid.ofString? qm, Cid.ofString? bafz with
  | some c0, some c1 =>
      r.check "cid v0 parse" ((Cid.toString c0) == qm)
      r.check "cid v1 parse" ((Cid.toString c1) == bafz)
      r.check "cid v0/v1 same multihash" (Cid.mhOf c0 == Cid.mhOf c1)
      r.check "cid libp2p-key codec" (Cid.ofBytes? (Cid.toBytes c1) == some c1)
  | _, _ => r.check "cid parse bafz/Qm" false

  -- peer-id multihash validation used by multiaddr
  r.check "multihash validPeer sha256-32"
    (Multihash.validPeer { code := 0x12, digest := List.replicate 32 0 })
  r.check "multihash validPeer rejects sha256-31"
    (!Multihash.validPeer { code := 0x12, digest := List.replicate 31 0 })
  r.check "multihash validPeer identity"
    (Multihash.validPeer { code := 0x00, digest := [1, 2, 3] })
  r.check "multihash validPeer rejects sha1"
    (!Multihash.validPeer { code := 0x11, digest := List.replicate 20 0 })

end Tests
