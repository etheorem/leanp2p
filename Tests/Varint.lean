import Tests.Support

/-!
# unsigned-varint suite

Mirrors: multiformats/unsigned-varint README (spec examples and rules),
pinned in VECTORS.lock. Phase 1 step 5 made the implementation strict:
minimal encodings only, 9-byte cap, and a ByteArray decoder reporting the
bytes consumed.
-/

open LeanP2P Tests

namespace Tests

def Varint.run (r : Runner) : IO Unit := do
  r.section "varint" "multiformats/unsigned-varint README.md (examples + rules)"

  -- Spec examples from the README table, extracted by extract-vectors.py.
  let j ← loadJson "varint-examples.json"
  for e in (← jArr "varint-examples.json" j "examples") do
    let n ← jNat "varint-examples.json" e "n"
    let hex ← jStr "varint-examples.json" e "uvarintHex"
    let bs ← hexBytes hex
    r.check s!"varint example encode {n}" (Varint.encode n == bs)
    r.check s!"varint example decode {n}" (Varint.decode? bs == some (n, []))
    r.check s!"varint example ByteArray decode {n}"
      (Varint.decodeB? (Bytes.ofNatList bs) 0 == some (n, bs.length))

  -- Round-trip sweep over boundary values (spike original).
  for n in [0, 1, 127, 128, 273, 421, 443, 460, 16383, 16384, 4294967295,
      4294967296, 9007199254740991] do
    r.check s!"varint roundtrip {n}" (Varint.decode? (Varint.encode n) == some (n, []))
    r.check s!"varint ByteArray roundtrip {n}"
      (Varint.decodeB? (Varint.encodeB n) 0 == some (n, (Varint.encodeB n).size))
  r.check "varint 273 encoding" (Varint.encode 273 == [145, 2])

  -- README rule: varints must be minimally encoded; `{0x81 0x00}` decodes to
  -- 1 in Go but is not a legal multiformats varint. Theorem + runtime.
  r.check "varint rejects non-minimal 8100" (Varint.decode? [0x81, 0x00] == none)

  -- README rule: implementations MUST cap varints at 9 bytes (63 bits).
  let tenBytes := List.replicate 9 0xff ++ [0x01]
  r.check "varint rejects 10-byte encoding" (Varint.decode? tenBytes == none)
  r.check "varint accepts 9-byte 63-bit max encoding"
    (Varint.decode? (List.replicate 8 0xff ++ [0x7f]) ==
      some (0x7fffffffffffffff, []))
  r.check "varint rejects 2^63" (Varint.decode? (Varint.encode (2 ^ 63)) == none)


end Tests
