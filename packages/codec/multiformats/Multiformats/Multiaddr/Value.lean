import Multiformats.ComponentWire
import Multiformats.Cid
import Multiformats.Multiaddr.Ip
import Multiformats.Multiaddr.Percent

/-!
# Protocol values

Framing establishes byte bounds and widths before these checks run.
The pinned Go transcoders define the value checks. ECH follows the
pinned protocol specification: its text is multibase, not raw UTF-8.
Text presentation of a complete address is handled above this layer.
-/

set_option autoImplicit false

namespace Multiformats.Multiaddr

open ComponentWire (Frame)

/-- Big-endian values are used by ports and the memory transport. -/
def readBigEndian (bytes : List Nat) : Nat := bytes.foldl (fun n b => n * 256 + b) 0

/-- The caller checks the integer's range before requesting its fixed width. -/
def bigEndian (width value : Nat) : List Nat :=
  (List.range width).map fun i => value / 256 ^ (width - 1 - i) % 256

/-- Only valid UTF-8 enters a text-valued protocol. -/
private def utf8? (bytes : List Nat) : Except Error String :=
  match Bytes.toString? (Bytes.ofNatList bytes) with
  | some text => .ok text
  | none => .error .badValue

/-- A name or zone is nonempty and cannot introduce another component. -/
private def nameValid (bytes : List Nat) : Bool :=
  !bytes.isEmpty && !bytes.contains 47 &&
    (Bytes.toString? (Bytes.ofNatList bytes)).isSome

/-- A peer component carries an identity digest or a complete SHA-256 digest. -/
def validPeerHash (hash : Multihash) : Bool :=
  hash.code == .identity || (hash.code == .«sha2-256» && hash.digest.length == 32)

/-- Semantic validation adds no new framing assumptions. -/
def validFrame (frame : Frame) : Bool :=
  let bytes := frame.value
  match frame.proto with
  | .ip6zone | .dns | .dns4 | .dns6 | .dnsaddr | .sni => nameValid bytes
  | .unix => bytes.length ≥ 2 && bytes.head? == some 47 && bytes.getLast? != some 47 &&
      (Bytes.toString? (Bytes.ofNatList bytes)).isSome
  | .«http-path» => !bytes.isEmpty &&
      (Bytes.toString? (Bytes.ofNatList bytes)).isSome
  | .p2p => match Multihash.decode? bytes with
      | .ok (hash, _) => validPeerHash hash
      | .error _ => false
  | .certhash => match Multihash.decode? bytes with
      | .ok _ => true
      | .error _ => false
  | .onion => readBigEndian (bytes.drop 10) != 0
  | .onion3 => readBigEndian (bytes.drop 35) != 0
  | .garlic64 => bytes.length ≥ 386
  | .garlic32 => bytes.length == 32 || bytes.length ≥ 35
  | .ech => !bytes.isEmpty
  | _ => true

/-- The two onion forms differ only in host width. -/
private def onionValue? (hostBytes : Nat) (text : String) : Except Error (List Nat) := do
  match text.splitOn ":" with
  | [host, port] =>
      let decoded ← BitBase.decode? 5 "abcdefghijklmnopqrstuvwxyz234567" true 0 host
      let n ← decimal? port 65536
      if decoded.size != hostBytes || n == 0 then .error .badValue
      else .ok (Bytes.toNatList decoded ++ bigEndian 2 n)
  | _ => .error .badValue

/-- Both accepted peer text forms reduce to the bare multihash wire value. -/
def peerBytes? (text : String) : Except Error (List Nat) := do
  let hash ← if text.startsWith "Qm" || text.startsWith "1" then do
      let raw ← Base58.decode? text
      Multihash.ofByteArray? raw
    else do
      let cid ← Cid.ofString? text
      match cid with
      | .v1 .«p2p-key» hash => .ok hash
      | _ => .error .badValue
  if validPeerHash hash then .ok (Multihash.encode hash) else .error .badValue

/-- Protocol-specific parsing returns a checked frame rather than unchecked bytes. -/
def parseValue? (protocol : Protocol) (text : String) : Except Error Frame := do
  if text.utf8ByteSize > maxAddressBytes then .error .overCap
  else
    let bytes ← match protocol with
      | .ip4 => parseIp4? text
      | .ip6 => parseIp6? text
      | .tcp | .udp | .dccp | .sctp => bigEndian 2 <$> decimal? text 65536
      | .ipcidr => do .ok [← decimal? text 256]
      | .memory => bigEndian 8 <$> decimal? text (2 ^ 64)
      | .ip6zone | .dns | .dns4 | .dns6 | .dnsaddr | .sni | .unix =>
          .ok (Bytes.toNatList text.toUTF8)
      | .«http-path» => do .ok (Bytes.toNatList (← percentDecode? text).toUTF8)
      | .p2p => peerBytes? text
      | .onion => onionValue? 10 text
      | .onion3 => onionValue? 35 text
      | .garlic64 => Bytes.toNatList <$>
          BitBase.decode? 6 "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-~" false 4 text
      | .garlic32 => do
          let padding := (8 - text.length % 8) % 8
          let padded := text ++ String.ofList (List.replicate padding '=')
          Bytes.toNatList <$>
            BitBase.decode? 5 "abcdefghijklmnopqrstuvwxyz234567" false 8 padded false
      | .certhash | .ech => do
          let (_, bytes) ← Multibase.decode? text
          .ok (Bytes.toNatList bytes)
      | _ => if text.isEmpty then .ok [] else .error .badValue
    let frame ← ComponentWire.ofValue? protocol bytes
    if validFrame frame then .ok frame else .error .badValue

/-- Printing a value independently also checks its semantic constraints. -/
def valueString? (frame : Frame) : Except Error String := do
  if !validFrame frame then .error .badValue
  else
    let bytes := frame.value
    let buffer := Bytes.ofNatList bytes
    match frame.proto with
    | .ip4 => ip4String? bytes
    | .ip6 => ip6String? bytes
    | .tcp | .udp | .dccp | .sctp | .ipcidr | .memory => .ok (toString (readBigEndian bytes))
    | .ip6zone | .dns | .dns4 | .dns6 | .dnsaddr | .sni | .unix => utf8? bytes
    | .«http-path» => percentEncode <$> utf8? bytes
    | .p2p => .ok (Base58.encode buffer)
    | .onion | .onion3 =>
        let hostBytes := if frame.proto == .onion then 10 else 35
        let host := BitBase.encode 5 "abcdefghijklmnopqrstuvwxyz234567" 0
          (Bytes.ofNatList (bytes.take hostBytes))
        .ok (host ++ ":" ++ toString (readBigEndian (bytes.drop hostBytes)))
    | .garlic64 => .ok (BitBase.encode 6
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-~" 4 buffer)
    | .garlic32 => .ok (BitBase.encode 5 "abcdefghijklmnopqrstuvwxyz234567" 0 buffer)
    | .certhash | .ech => .ok ("u" ++ BitBase.encode 6
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_" 0 buffer)
    | _ => .ok ""

end Multiformats.Multiaddr
