import LeanP2P.Net.Varint
import LeanP2P.Crypto.Base58
import LeanP2P.Crypto.Multibase
import LeanP2P.Crypto.Multihash
import LeanP2P.Crypto.Cid
import LeanP2P.Crypto.Bytes
/-!
# Multiaddr (full protocol table)

Machine form: `(<uvarint code><value>)*` per multiformats/multiaddr. The
protocol table is the full protocols.csv (42 rows; `ipfs` is an alias of
`p2p`). Value codecs follow the upstream implementations (go-multiaddr
`transcoders.go`), with the divergences the vector suites force us to
resolve (VECTOR_TEST_PLAN.md section 5):

- `p2p` values: `Qm...`/`12D3KooW...` decode as base58btc multihashes,
  everything else as a multibase CIDv1 with the `libp2p-key` (0x72) codec;
  the wire value is the multihash. Printing follows the parsed form: base58
  for the former, CIDv1 base32 for the latter (Go prints base58 for both;
  js prints CIDs - both upstream suites round-trip with this rule).
- `unix` stores the path verbatim with its leading `/` (Go semantics; no
  percent decoding). `http-path` stores the percent-decoded path and
  re-encodes it when printing (Go semantics). `components` reports both in
  the js form (percent-decoded, `unix` without the leading slash).
- `memory` holds a length-prefixed string (protocols.csv size V and the js
  suite; go-multiaddr instead parses a u64 - a known upstream divergence).
- IPv4-mapped IPv6 addresses print dotted (`::ffff:1.2.3.4`, Go form);
  every other IPv6 prints RFC 5952 compressed.
- The empty text form parses to `none` (Go) while `toString {}` is `/` (js).
-/

namespace LeanP2P

inductive AddrComponent where
  | ip4 (a b c d : Nat)
  | ip6 (groups : List Nat)
  | ip6zone (zone : String)
  | ipcidr (bits : Nat)
  | tcp (port : Nat)
  | udp (port : Nat)
  | dccp (port : Nat)
  | sctp (port : Nat)
  | dns (name : String)
  | dns4 (name : String)
  | dns6 (name : String)
  | dnsaddr (name : String)
  | sni (name : String)
  | unix (path : String)
  | httpPath (path : String)
  | p2p (mhash : List Nat) (cidForm : Bool)
  | onion (host : List Nat) (port : Nat)
  | onion3 (host : List Nat) (port : Nat)
  | garlic64 (bs : List Nat)
  | garlic32 (bs : List Nat)
  | certhash (mh : List Nat)
  | memory (n : Nat)
  | ech (cfg : String)
  | udt | utp | tls | noise | quic | quicV1 | webtransport
  | http | https | ws | wss
  | p2pWebsocketStar | p2pStardust | p2pWebrtcStar | p2pWebrtcDirect
  | webrtcDirect | webrtc
  | p2pCircuit
deriving Repr, BEq

structure Multiaddr where
  components : List AddrComponent
deriving Repr, BEq

namespace Multiaddr

/-! ## Protocol table (multiformats/multiaddr protocols.csv) -/

/-- Official protocol codes. -/
def code : AddrComponent → Nat
  | .ip4 _ _ _ _ => 4
  | .tcp _ => 6
  | .udp _ => 273
  | .dccp _ => 33
  | .ip6 _ => 41
  | .ip6zone _ => 42
  | .ipcidr _ => 43
  | .dns _ => 53
  | .dns4 _ => 54
  | .dns6 _ => 55
  | .dnsaddr _ => 56
  | .sctp _ => 132
  | .udt => 301
  | .utp => 302
  | .unix _ => 400
  | .p2p _ _ => 421
  | .onion _ _ => 444
  | .onion3 _ _ => 445
  | .garlic64 _ => 446
  | .garlic32 _ => 447
  | .tls => 448
  | .sni _ => 449
  | .noise => 454
  | .quic => 460
  | .quicV1 => 461
  | .webtransport => 465
  | .certhash _ => 466
  | .http => 480
  | .httpPath _ => 481
  | .https => 443
  | .ws => 477
  | .wss => 478
  | .p2pWebsocketStar => 479
  | .p2pStardust => 277
  | .p2pWebrtcStar => 275
  | .p2pWebrtcDirect => 276
  | .webrtcDirect => 280
  | .webrtc => 281
  | .p2pCircuit => 290
  | .memory _ => 777
  | .ech _ => 9849

/-- Protocol names as printed (protocols.csv `name` column). -/
def name : AddrComponent → String
  | .ip4 _ _ _ _ => "ip4"
  | .tcp _ => "tcp"
  | .udp _ => "udp"
  | .dccp _ => "dccp"
  | .ip6 _ => "ip6"
  | .ip6zone _ => "ip6zone"
  | .ipcidr _ => "ipcidr"
  | .dns _ => "dns"
  | .dns4 _ => "dns4"
  | .dns6 _ => "dns6"
  | .dnsaddr _ => "dnsaddr"
  | .sctp _ => "sctp"
  | .udt => "udt"
  | .utp => "utp"
  | .unix _ => "unix"
  | .p2p _ _ => "p2p"
  | .onion _ _ => "onion"
  | .onion3 _ _ => "onion3"
  | .garlic64 _ => "garlic64"
  | .garlic32 _ => "garlic32"
  | .tls => "tls"
  | .sni _ => "sni"
  | .noise => "noise"
  | .quic => "quic"
  | .quicV1 => "quic-v1"
  | .webtransport => "webtransport"
  | .certhash _ => "certhash"
  | .http => "http"
  | .httpPath _ => "http-path"
  | .https => "https"
  | .ws => "ws"
  | .wss => "wss"
  | .p2pWebsocketStar => "p2p-websocket-star"
  | .p2pStardust => "p2p-stardust"
  | .p2pWebrtcStar => "p2p-webrtc-star"
  | .p2pWebrtcDirect => "p2p-webrtc-direct"
  | .webrtcDirect => "webrtc-direct"
  | .webrtc => "webrtc"
  | .p2pCircuit => "p2p-circuit"
  | .memory _ => "memory"
  | .ech _ => "ech"

/-! ## Binary codec -/

private def u16be (n : Nat) : List Nat := [n / 256 % 256, n % 256]

private def u64be (n : Nat) : List Nat :=
  [n / 2 ^ 56 % 256, n / 2 ^ 48 % 256, n / 2 ^ 40 % 256, n / 2 ^ 32 % 256,
    n / 2 ^ 24 % 256, n / 2 ^ 16 % 256, n / 2 ^ 8 % 256, n % 256]

private theorem u16be_decode (n : Nat) (h : n < 65536) :
    256 * (n / 256 % 256) + n % 256 = n := by omega

def encodeComp : AddrComponent → List Nat
  | .ip4 a b c d => Varint.encode 4 ++ [a, b, c, d]
  | .ip6 gs => Varint.encode 41 ++ gs.flatMap u16be
  | .ip6zone z => Varint.encode 42 ++ lenValue (Bytes.toNatList (Bytes.ofString z))
  | .ipcidr n => Varint.encode 43 ++ [n % 256]
  | .tcp p => Varint.encode 6 ++ u16be p
  | .udp p => Varint.encode 273 ++ u16be p
  | .dccp p => Varint.encode 33 ++ u16be p
  | .sctp p => Varint.encode 132 ++ u16be p
  | .dns n => Varint.encode 53 ++ lenValue (Bytes.toNatList (Bytes.ofString n))
  | .dns4 n => Varint.encode 54 ++ lenValue (Bytes.toNatList (Bytes.ofString n))
  | .dns6 n => Varint.encode 55 ++ lenValue (Bytes.toNatList (Bytes.ofString n))
  | .dnsaddr n => Varint.encode 56 ++ lenValue (Bytes.toNatList (Bytes.ofString n))
  | .sni n => Varint.encode 449 ++ lenValue (Bytes.toNatList (Bytes.ofString n))
  | .unix p => Varint.encode 400 ++ lenValue (Bytes.toNatList (Bytes.ofString p))
  | .httpPath p =>
      Varint.encode 481 ++ lenValue (Bytes.toNatList (Bytes.ofString p))
  | .p2p mh _ => Varint.encode 421 ++ Varint.encode mh.length ++ mh
  | .onion h p => Varint.encode 444 ++ h ++ u16be p
  | .onion3 h p => Varint.encode 445 ++ h ++ u16be p
  | .garlic64 bs => Varint.encode 446 ++ Varint.encode bs.length ++ bs
  | .garlic32 bs => Varint.encode 447 ++ Varint.encode bs.length ++ bs
  | .certhash mh => Varint.encode 466 ++ Varint.encode mh.length ++ mh
  | .memory n => Varint.encode 777 ++ u64be n
  | .ech s => Varint.encode 9849 ++ lenValue (Bytes.toNatList (Bytes.ofString s))
  | .udt => Varint.encode 301
  | .utp => Varint.encode 302
  | .tls => Varint.encode 448
  | .noise => Varint.encode 454
  | .quic => Varint.encode 460
  | .quicV1 => Varint.encode 461
  | .webtransport => Varint.encode 465
  | .http => Varint.encode 480
  | .https => Varint.encode 443
  | .ws => Varint.encode 477
  | .wss => Varint.encode 478
  | .p2pWebsocketStar => Varint.encode 479
  | .p2pStardust => Varint.encode 277
  | .p2pWebrtcStar => Varint.encode 275
  | .p2pWebrtcDirect => Varint.encode 276
  | .webrtcDirect => Varint.encode 280
  | .webrtc => Varint.encode 281
  | .p2pCircuit => Varint.encode 290
where
  lenValue (bs : List Nat) : List Nat := Varint.encode bs.length ++ bs

def encodeBin (ps : List AddrComponent) : List Nat :=
  ps.flatMap encodeComp

private def takeN (n : Nat) (rest : List Nat) : Option (List Nat × List Nat) :=
  if rest.length < n then none else some (rest.take n, rest.drop n)

/-- Fuel-based decoder: fuel bounds the component count. Validation follows
go-multiaddr: multihash-valued components are checked, onion ports are
nonzero, `ip6zone` must be directly followed by `ip6`, and fixed-size
values consume exactly their size. -/
def decodeBinF : Nat → List Nat → Option (List AddrComponent)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, bs => do
    let (code, rest) ← Varint.decode? bs
    match code with
    | 4 => do
        let (v, rest) ← takeN 4 rest
        some (AddrComponent.ip4 (v.getD 0 0) (v.getD 1 0) (v.getD 2 0) (v.getD 3 0) :: (← decodeBinF fuel rest))
    | 41 => do
        let (v, rest) ← takeN 16 rest
        let g i := 256 * (v.getD (2 * i) 0) + (v.getD (2 * i + 1) 0)
        some (AddrComponent.ip6 [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7] :: (← decodeBinF fuel rest))
    | 42 => do
        -- ip6zone: nonempty, no '/', and must be followed by ip6
        let (len, rest) ← Varint.decode? rest
        let (v, rest) ← takeN len rest
        let zone ← Bytes.toString? (Bytes.ofNatList v)
        guard (0 < v.length)
        guard (!zone.contains '/')
        let (code2, rest) ← Varint.decode? rest
        guard (code2 = 41)
        let (v, rest) ← takeN 16 rest
        let g i := 256 * (v.getD (2 * i) 0) + (v.getD (2 * i + 1) 0)
        some (AddrComponent.ip6zone zone :: AddrComponent.ip6 [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7] :: (← decodeBinF fuel rest))
    | 43 => do
        let (v, rest) ← takeN 1 rest
        some (AddrComponent.ipcidr (v.getD 0 0) :: (← decodeBinF fuel rest))
    | 6 => do
        let (v, rest) ← takeN 2 rest
        some (AddrComponent.tcp (256 * (v.getD 0 0) + (v.getD 1 0)) :: (← decodeBinF fuel rest))
    | 273 => do
        let (v, rest) ← takeN 2 rest
        some (AddrComponent.udp (256 * (v.getD 0 0) + (v.getD 1 0)) :: (← decodeBinF fuel rest))
    | 33 => do
        let (v, rest) ← takeN 2 rest
        some (AddrComponent.dccp (256 * (v.getD 0 0) + (v.getD 1 0)) :: (← decodeBinF fuel rest))
    | 132 => do
        let (v, rest) ← takeN 2 rest
        some (AddrComponent.sctp (256 * (v.getD 0 0) + (v.getD 1 0)) :: (← decodeBinF fuel rest))
    | 53 | 54 | 55 | 56 | 449 => do
        let (len, rest) ← Varint.decode? rest
        let (v, rest) ← takeN len rest
        let name ← Bytes.toString? (Bytes.ofNatList v)
        guard (0 < v.length)
        guard (!name.contains '/')
        let c := if code = 53 then AddrComponent.dns name
                 else if code = 54 then AddrComponent.dns4 name
                 else if code = 55 then AddrComponent.dns6 name
                 else if code = 56 then AddrComponent.dnsaddr name
                 else AddrComponent.sni name
        some (c :: (← decodeBinF fuel rest))
    | 400 => do
        -- unix is a path protocol and terminal: it is length-prefixed on the
        -- wire, but no component may follow it (go-multiaddr readMultiaddr)
        let (len, rest) ← Varint.decode? rest
        let (v, rest) ← takeN len rest
        guard (2 ≤ v.length)
        guard (v.getD 0 0 = 0x2f)
        guard (v.getD (v.length - 1) 1 != 0x2f)
        guard (rest = [])
        let p ← Bytes.toString? (Bytes.ofNatList v)
        some [AddrComponent.unix p]
    | 481 => do
        let (len, rest) ← Varint.decode? rest
        let (v, rest) ← takeN len rest
        guard (0 < v.length)
        let p ← Bytes.toString? (Bytes.ofNatList v)
        some (AddrComponent.httpPath p :: (← decodeBinF fuel rest))
    | 421 => do
        -- p2p: the value must be a well-formed peer multihash
        let (len, rest) ← Varint.decode? rest
        let (v, rest) ← takeN len rest
        let mh ← Multihash.decode? v
        guard (Multihash.validPeer mh)
        some (AddrComponent.p2p v false :: (← decodeBinF fuel rest))
    | 444 => do
        -- onion: 10-byte host + u16 port, port nonzero
        let (v, rest) ← takeN 12 rest
        let host := v.take 10
        let port := 256 * (v.getD 10 0) + (v.getD 11 0)
        guard (port != 0)
        some (AddrComponent.onion host port :: (← decodeBinF fuel rest))
    | 445 => do
        -- onion3: 35-byte host + u16 port, port nonzero
        let (v, rest) ← takeN 37 rest
        let host := v.take 35
        let port := 256 * (v.getD 35 0) + (v.getD 36 0)
        guard (port != 0)
        some (AddrComponent.onion3 host port :: (← decodeBinF fuel rest))
    | 446 => do
        let (len, rest) ← Varint.decode? rest
        let (v, rest) ← takeN len rest
        guard (386 ≤ v.length)
        some (AddrComponent.garlic64 v :: (← decodeBinF fuel rest))
    | 447 => do
        let (len, rest) ← Varint.decode? rest
        let (v, rest) ← takeN len rest
        guard (v.length = 32 ∨ 35 ≤ v.length)
        some (AddrComponent.garlic32 v :: (← decodeBinF fuel rest))
    | 466 => do
        let (len, rest) ← Varint.decode? rest
        let (v, rest) ← takeN len rest
        let _ ← Multihash.decode? v
        some (AddrComponent.certhash v :: (← decodeBinF fuel rest))
    | 777 => do
        -- memory is a big-endian u64 (go-multiaddr / rust-libp2p wire form)
        let (v, rest) ← takeN 8 rest
        some (AddrComponent.memory
          (v.getD 0 0 * 2 ^ 56 + v.getD 1 0 * 2 ^ 48 + v.getD 2 0 * 2 ^ 40 +
            v.getD 3 0 * 2 ^ 32 + v.getD 4 0 * 2 ^ 24 +
            v.getD 5 0 * 2 ^ 16 + v.getD 6 0 * 2 ^ 8 +
            v.getD 7 0) :: (← decodeBinF fuel rest))
    | 9849 => do
        let (len, rest) ← Varint.decode? rest
        let (v, rest) ← takeN len rest
        guard (0 < v.length)
        let s ← Bytes.toString? (Bytes.ofNatList v)
        some (AddrComponent.ech s :: (← decodeBinF fuel rest))
    | 301 => some (AddrComponent.udt :: (← decodeBinF fuel rest))
    | 302 => some (AddrComponent.utp :: (← decodeBinF fuel rest))
    | 448 => some (AddrComponent.tls :: (← decodeBinF fuel rest))
    | 454 => some (AddrComponent.noise :: (← decodeBinF fuel rest))
    | 460 => some (AddrComponent.quic :: (← decodeBinF fuel rest))
    | 461 => some (AddrComponent.quicV1 :: (← decodeBinF fuel rest))
    | 465 => some (AddrComponent.webtransport :: (← decodeBinF fuel rest))
    | 480 => some (AddrComponent.http :: (← decodeBinF fuel rest))
    | 443 => some (AddrComponent.https :: (← decodeBinF fuel rest))
    | 477 => some (AddrComponent.ws :: (← decodeBinF fuel rest))
    | 478 => some (AddrComponent.wss :: (← decodeBinF fuel rest))
    | 479 => some (AddrComponent.p2pWebsocketStar :: (← decodeBinF fuel rest))
    | 277 => some (AddrComponent.p2pStardust :: (← decodeBinF fuel rest))
    | 275 => some (AddrComponent.p2pWebrtcStar :: (← decodeBinF fuel rest))
    | 276 => some (AddrComponent.p2pWebrtcDirect :: (← decodeBinF fuel rest))
    | 280 => some (AddrComponent.webrtcDirect :: (← decodeBinF fuel rest))
    | 281 => some (AddrComponent.webrtc :: (← decodeBinF fuel rest))
    | 290 => some (AddrComponent.p2pCircuit :: (← decodeBinF fuel rest))
    | _ => none

def decodeBin (bs : List Nat) : Option (List AddrComponent) :=
  decodeBinF (bs.length + 1) bs

/-! ## Presentation codec -/

private def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def groupVal? (g : String) : Option Nat :=
  if g.isEmpty ∨ 4 < g.length then none
  else g.toList.foldlM (fun acc c => (acc * 16 + ·) <$> hexDigit? c) 0

private def groups? (t : String) : Option (List Nat) :=
  if t.isEmpty then some [] else t.splitOn ":" |>.mapM groupVal?

private def hexGroup (n : Nat) : String := String.mk (Nat.toDigits 16 n)

/-- Strict decimal: digits only (Lean's `toNat?` also accepts `_`
digit separators, so "8_0" would parse to 80 - a port or address value
must reject it). -/
private def decNat? (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty ∨ !cs.all (fun c => '0' ≤ c ∧ c ≤ '9') then none
  else some (cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)

/-- IPv4 octet: strict decimal without a leading zero (Go 1.17+ net.ParseIP
rejects `01`-style octets to avoid the classic octal ambiguity). -/
private def octet? (s : String) : Option Nat := do
  let n ← decNat? s
  guard (n < 256)
  guard (s.length = 1 ∨ s.toList.head? != some '0')
  some n

private def parseIp4? (s : String) : Option (Nat × Nat × Nat × Nat) :=
  match s.splitOn "." with
  | [a, b, c, d] => do
      let a ← octet? a; let b ← octet? b; let c ← octet? c; let d ← octet? d
      some (a, b, c, d)
  | _ => none

/-- Canonical IPv6 string (RFC 5952 style): lowercase groups, leading zeros
stripped, longest zero-run (ties: first) compressed; IPv4-mapped addresses
print dotted (the Go form, chosen over the js hex form in the plan). -/
def ip6String (gs : List Nat) : String :=
  if gs.length = 8 ∧ (gs.take 5).all (· == 0) ∧ gs.getD 5 0 = 0xffff then
    let (a, b) := (gs.getD 6 0, gs.getD 7 0)
    s!"::ffff:{a / 256}.{a % 256}.{b / 256}.{b % 256}"
  else
    let best := (List.range (gs.length + 1)).foldl (fun acc start =>
      let len := ((gs.drop start).takeWhile (· == 0)).length
      match acc with
      | some (bs, bl) =>
          if bl < len ∧ 2 ≤ len then some (start, len) else some (bs, bl)
      | none =>
          if 2 ≤ len then some (start, len) else none) none
    match best with
    | some (start, len) =>
        let before := (gs.take start).map hexGroup
        let after := (gs.drop (start + len)).map hexGroup
        (if before.isEmpty then "" else String.intercalate ":" before) ++
          "::" ++
          (if after.isEmpty then "" else String.intercalate ":" after)
    | none => String.intercalate ":" (gs.map hexGroup)

private def parseIp6? (s : String) : Option (List Nat) := do
  -- embedded IPv4 tail -> two hex groups
  let s ←
    if s.contains '.' then do
      let parts := s.splitOn ":"
      let last ← parts.getLast?
      let (a, b, c, d) ← parseIp4? last
      let g1 := a * 256 + b
      let g2 := c * 256 + d
      some (String.intercalate ":" parts.dropLast ++ ":" ++ hexGroup g1 ++ ":" ++ hexGroup g2)
    else some s
  if s.contains "::" then do
    let halves := s.splitOn "::"
    guard (halves.length = 2)
    let gl ← groups? (halves.getD 0 "")
    let gr ← groups? (halves.getD 1 "")
    let fill := 8 - gl.length - gr.length
    guard (1 ≤ fill)
    some (gl ++ List.replicate fill 0 ++ gr)
  else do
    let gs ← s.splitOn ":" |>.mapM groupVal?
    guard (gs.length = 8)
    some gs

/-! ### percent-encoding (http-path) -/

/-- Decode percent escapes over the **UTF-8 bytes** of `s` and validate
the result as UTF-8. `%XX` escapes carry bytes, not code points: a
percent-encoded non-ASCII path (`%C3%A9`) must decode to the two UTF-8
bytes of `é`, not to two Latin-1 characters, or the wire form of the
stored value re-encodes garbage. -/
def percentDecode? (s : String) : Option String := do
  let rec go (acc : List Nat) : List Nat → Option (List Nat)
    | [] => some acc
    | 0x25 :: a :: b :: rest => do
        let hi ← hexDigitB? a
        let lo ← hexDigitB? b
        go (acc ++ [hi * 16 + lo]) rest
    | 0x25 :: _ => none  -- dangling '%x'
    | c :: rest => go (acc ++ [c]) rest
  let bs ← go [] (Bytes.toNatList s.toUTF8)
  Bytes.toString? (Bytes.ofNatList bs)
where
  hexDigitB? (b : Nat) : Option Nat :=
    if b ≥ 0x30 ∧ b ≤ 0x39 then some (b - 0x30)
    else if b ≥ 0x61 ∧ b ≤ 0x66 then some (b - 0x61 + 10)
    else if b ≥ 0x41 ∧ b ≤ 0x46 then some (b - 0x41 + 10)
    else none

private def isUnreserved (b : Nat) : Bool :=
  (0x61 ≤ b ∧ b ≤ 0x7a) ∨ (0x41 ≤ b ∧ b ≤ 0x5a) ∨ (0x30 ≤ b ∧ b ≤ 0x39) ∨
    b == 0x2d ∨ b == 0x2e ∨ b == 0x5f ∨ b == 0x7e

/-- Percent-encode the UTF-8 bytes of `s` (unreserved ASCII passes
through; every other byte, including each byte of a multi-byte
sequence, becomes `%XX` - encoding code points instead of bytes emits
wrong wire bytes for any non-ASCII path). -/
def percentEncode (s : String) : String :=
  (Bytes.toNatList s.toUTF8).foldl (fun acc b =>
    if isUnreserved b then acc.push (Char.ofNat b)
    else acc ++ "%" ++ (hexByte (b / 16)) ++ hexByte (b % 16)) ""
where
  hexByte (n : Nat) : String := String.ofList [hexDigitChar n]
  hexDigitChar (n : Nat) : Char :=
    if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + n - 10)

/-! ### onion / garlic alphabets -/

/-- Lowercase RFC 4648 base32 body of `bs` (no prefix, no padding). -/
def b32Body (bs : List Nat) : String :=
  ((Multibase.encode .base32 (Bytes.ofNatList bs)).drop 1).toString

private def b32Char? (c : Char) : Option Nat :=
  Multibase.alphabetB32.toList.findIdx? (· == c)

/-- Onion / onion3 host: base32 lower, decoded MSB-first; exactly
`bytes` bytes (10 for onion from 16 chars, 35 for onion3 from 56). -/
def onionHost? (s : String) (bytes : Nat) : Option (List Nat) := do
  let chars := bytes * 8 / 5
  guard (s.length = chars)
  let bits ← s.toList.mapM b32Char?
  let out :=
    Id.run do
      let mut out : List Nat := []
      let mut acc := 0
      let mut accBits := 0
      for d in bits do
        acc := acc * 32 + d
        accBits := accBits + 5
        if accBits ≥ 8 then
          let shift := accBits - 8
          out := out ++ [acc / 2 ^ shift % 256]
          acc := acc % 2 ^ shift
          accBits := shift
      out
  guard (out.length = bytes)
  some out

private def parsePort? (s : String) : Option Nat := do
  let p ← decNat? s
  guard (0 < p ∧ p < 65536)
  some p

/-- i2p base64 alphabet: standard, with `-` and `~` in place of `+` and `/`. -/
private def garlic64Char? (c : Char) : Option Nat :=
  if c == '-' then some 62
  else if c == '~' then some 63
  else
    if c.isDigit then some (c.toNat - '0'.toNat + 52)
    else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
    else if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
    else none

private def garlic64EncodeByte (n : Nat) : Char :=
  if n < 26 then Char.ofNat ('A'.toNat + n)
  else if n < 52 then Char.ofNat ('a'.toNat + n - 26)
  else if n < 62 then Char.ofNat ('0'.toNat + n - 52)
  else if n = 62 then '-'
  else '~'

/-- garlic64 value: i2p base64 (MSB-first, `-`/`~` for `+`/`/`),
canonical `=` padding, decoded length ≥ 386. Parses its own output
including padded forms: the padding stays part of the scanned string, so
the final 2- or 3-char group (which `garlic64Print` pads) decodes. -/
def garlic64Parse? (s : String) : Option (List Nat) := do
  let cs := s.toList
  guard (cs.length % 4 != 1)
  -- '=' only in a canonical tail (at most one final group of padding)
  guard ((cs.dropWhile (fun c => c != '=')).all (fun c => c == '='))
  let rec go (acc : List Nat) : List Char → Option (List Nat)
    | [] => some acc
    | [a, b, '=', '='] => do
        let x ← garlic64Char? a
        let y ← garlic64Char? b
        guard (y % 16 = 0)
        some (acc ++ [(x * 4 + y / 16) % 256])
    | [a, b, c, '='] => do
        let x ← garlic64Char? a
        let y ← garlic64Char? b
        let z ← garlic64Char? c
        guard (z % 4 = 0)
        some (acc ++ [x * 4 + y / 16, (y % 16) * 16 + z / 4])
    | a :: b :: c :: d :: rest => do
        let x ← garlic64Char? a
        let y ← garlic64Char? b
        let z ← garlic64Char? c
        let w ← garlic64Char? d
        go (acc ++ [x * 4 + y / 16, (y % 16) * 16 + z / 4, (z % 4) * 64 + w]) rest
    | _ => none
  let bs ← go [] cs
  guard (386 ≤ bs.length)
  some bs

def garlic64Print (bs : List Nat) : String :=
  let enc := garlic64EncodeByte
  let rec go : List Nat → String
    | [] => ""
    | [a] =>
        String.ofList [enc (a / 4), enc ((a % 4) * 16), '=', '=']
    | [a, b] =>
        String.ofList [enc (a / 4), enc ((a % 4) * 16 + b / 16),
          enc ((b % 16) * 4), '=']
    | a :: b :: c :: rest =>
        String.ofList [enc (a / 4), enc ((a % 4) * 16 + b / 16),
            enc ((b % 16) * 4 + c / 64), enc (c % 64)] ++ go rest
  go bs

/-- garlic32 value: i2p base32 (lower), Go-compatible padding rules,
decoded length 32 or ≥ 35; trailing bits are ignored (Go's non-strict
base32). -/
def garlic32Parse? (s : String) : Option (List Nat) := do
  let n := s.length
  -- valid base32 final-group sizes: 2,4,5,7 chars (pad 6,4,3,1); plus 0
  guard (n % 8 = 0 ∨ n % 8 = 7 ∨ n % 8 = 5 ∨ n % 8 = 4 ∨ n % 8 = 2)
  let bits ← s.toList.mapM b32Char?
  let out :=
    Id.run do
      let mut out : List Nat := []
      let mut acc := 0
      let mut accBits := 0
      for d in bits do
        acc := acc * 32 + d
        accBits := accBits + 5
        if accBits ≥ 8 then
          let shift := accBits - 8
          out := out ++ [acc / 2 ^ shift % 256]
          acc := acc % 2 ^ shift
          accBits := shift
      out
  guard (out.length = 32 ∨ 35 ≤ out.length)
  some out

def garlic32Print (bs : List Nat) : String := b32Body bs

/-! ### p2p values -/

/-- Parse a p2p value: base58btc multihash (`Qm...`, `1...`) or a multibase
CIDv1 with the libp2p-key codec. Returns the multihash bytes and whether
the CIDv1 form must be used when printing. -/
def p2pValue? (s : String) : Option (List Nat × Bool) :=
  if s.startsWith "Qm" ∨ s.startsWith "1" then do
    let bs ← Base58.decode? s
    let mh ← Multihash.decode? bs
    guard (Multihash.validPeer mh)
    some (bs, false)
  else do
    let (_, bytes) ← Multibase.decode? s
    match ← Cid.ofBytes? (Bytes.toNatList bytes) with
    | .v0 mh => do
        guard (Multihash.validPeer mh)
        some (Multihash.encode mh, false)
    | .v1 codec mh => do
        guard (codec = Cid.codecLibp2pKey)
        guard (Multihash.validPeer mh)
        some (Multihash.encode mh, true)

private def p2pPrint (mh : List Nat) (cidForm : Bool) : String :=
  if cidForm then
    match Multihash.decode? mh with
    | some mh => Cid.toString (Cid.libp2pKeyV1 mh)
    | none => ""
  else Base58.encode mh

/-! ### text form -/

def toString (m : Multiaddr) : String :=
  if m.components.isEmpty then "/" else
  m.components.foldl (fun acc c =>
    acc ++ "/" ++ name c ++
      (match c with
        | .ip4 a b c d => s!"/{a}.{b}.{c}.{d}"
        | .ip6 gs => s!"/{ip6String gs}"
        | .ip6zone z => s!"/{z}"
        | .ipcidr n => s!"/{n}"
        | .tcp p => s!"/{p}"
        | .udp p => s!"/{p}"
        | .dccp p => s!"/{p}"
        | .sctp p => s!"/{p}"
        | .dns n => s!"/{n}"
        | .dns4 n => s!"/{n}"
        | .dns6 n => s!"/{n}"
        | .dnsaddr n => s!"/{n}"
        | .sni n => s!"/{n}"
        | .unix p => p
        | .httpPath p => s!"/{percentEncode p}"
        | .p2p mh cid => s!"/{p2pPrint mh cid}"
        | .onion h p => s!"/{b32Body h}:{p}"
        | .onion3 h p => s!"/{b32Body h}:{p}"
        | .garlic64 bs => s!"/{garlic64Print bs}"
        | .garlic32 bs => s!"/{garlic32Print bs}"
        | .certhash mh =>
            s!"/{Multibase.encode .base64url (Bytes.ofNatList mh)}"
        | .memory n => s!"/{n}"
        | .ech s => s!"/{s}"
        | _ => "")) ""

/-! ### text parsing -/

def valuedProto? (proto value : String) : Option AddrComponent :=
  if proto = "ip4" then do
    let (a, b, cc, d) ← parseIp4? value
    some (.ip4 a b cc d)
  else if proto = "ip6" then AddrComponent.ip6 <$> parseIp6? value
  else if proto = "ip6zone" then do
    guard (0 < value.length)
    guard (!value.contains '/')
    some (.ip6zone value)
  else if proto = "ipcidr" then do
    let n ← decNat? value
    guard (n < 256)
    some (.ipcidr n)
  else if proto = "tcp" then port? value .tcp
  else if proto = "udp" then port? value .udp
  else if proto = "dccp" then port? value .dccp
  else if proto = "sctp" then port? value .sctp
  else if proto = "dns" then name? value .dns
  else if proto = "dns4" then name? value .dns4
  else if proto = "dns6" then name? value .dns6
  else if proto = "dnsaddr" then name? value .dnsaddr
  else if proto = "sni" then name? value .sni
  else if proto = "p2p" ∨ proto = "ipfs" then do
    let (mh, cid) ← p2pValue? value
    some (.p2p mh cid)
  else if proto = "onion" then do
    match value.splitOn ":" with
    | [host, port] => do
        let h ← onionHost? host 10
        let p ← parsePort? port
        some (.onion h p)
    | _ => none
  else if proto = "onion3" then do
    match value.splitOn ":" with
    | [host, port] => do
        let h ← onionHost? host 35
        let p ← parsePort? port
        some (.onion3 h p)
    | _ => none
  else if proto = "garlic64" then AddrComponent.garlic64 <$> garlic64Parse? value
  else if proto = "garlic32" then AddrComponent.garlic32 <$> garlic32Parse? value
  else if proto = "certhash" then do
    let (_, bytes) ← Multibase.decode? value
    let mh ← Multihash.decode? (Bytes.toNatList bytes)
    some (.certhash (Multihash.encode mh))
  else if proto = "memory" then do
    let n ← decNat? value
    guard (n < 2 ^ 64)
    some (.memory n)
  else if proto = "ech" then do
    guard (0 < value.length)
    some (.ech value)
  else none
where
  port? (v : String) (k : Nat → AddrComponent) : Option AddrComponent := do
    let p ← decNat? v
    guard (p < 65536)
    some (k p)
  name? (v : String) (k : String → AddrComponent) : Option AddrComponent := do
    guard (0 < v.length)
    guard (!v.contains '/')
    some (k v)

def valuelessProto? (proto : String) : Option AddrComponent :=
  if proto = "quic" then some .quic
  else if proto = "quic-v1" then some .quicV1
  else if proto = "ws" then some .ws
  else if proto = "wss" then some .wss
  else if proto = "http" then some .http
  else if proto = "https" then some .https
  else if proto = "tls" then some .tls
  else if proto = "utp" then some .utp
  else if proto = "udt" then some .udt
  else if proto = "noise" then some .noise
  else if proto = "webtransport" then some .webtransport
  else if proto = "p2p-circuit" then some .p2pCircuit
  else if proto = "p2p-websocket-star" then some .p2pWebsocketStar
  else if proto = "p2p-stardust" then some .p2pStardust
  else if proto = "p2p-webrtc-star" then some .p2pWebrtcStar
  else if proto = "p2p-webrtc-direct" then some .p2pWebrtcDirect
  else if proto = "webrtc-direct" then some .webrtcDirect
  else if proto = "webrtc" then some .webrtc
  else none

mutual
/-- One protocol segment of the text form: `s` does not start with `/`
and is non-empty. Mutually recursive with `parseGo` (segment → boundary
→ segment). -/
private partial def parseSeg (fuel : Nat) (s : List Char) :
    Option (List AddrComponent) := do
  let proto := String.ofList (s.takeWhile (· != '/'))
  let rest := s.dropWhile (· != '/')
  if proto = "unix" then do
    -- the value is the rest of the address, verbatim, starting with '/'
    guard (0 < rest.length)
    let value := String.ofList rest
    guard (2 ≤ value.length)
    guard (!value.endsWith "/")
    some [AddrComponent.unix value]
  else if proto = "http-path" then do
    guard (0 < rest.length)
    let after := rest.drop 1
    let seg := String.ofList (after.takeWhile (· != '/'))
    let rest2 := after.dropWhile (· != '/')
    let p ← percentDecode? seg
    guard (0 < p.length)
    return AddrComponent.httpPath p :: (← parseGo fuel rest2)
  else if rest.isEmpty then
    match valuelessProto? proto with
    | some c => some [c]
    | none => none  -- valued protocol with no value
  else
    match valuelessProto? proto with
    | some c => return c :: (← parseGo fuel rest)
    | none => do
        let after := rest.drop 1
        let value := String.ofList (after.takeWhile (· != '/'))
        let rest2 := after.dropWhile (· != '/')
        let c ← valuedProto? proto value
        -- an ip6zone must be directly followed by ip6
        if c matches .ip6zone _ then
          let next := String.ofList ((rest2.drop 1).takeWhile (· != '/'))
          guard (next = "ip6")
        return c :: (← parseGo fuel rest2)

/-- Continue at a segment boundary: `s` is empty, or starts with exactly
one `/` separator (a second one means an empty segment, which names no
protocol). -/
private partial def parseGo (fuel : Nat) (s : List Char) :
    Option (List AddrComponent) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match s with
    | [] => some []
    | '/' :: rest' =>
        match rest' with
        | [] => none
        | '/' :: _ => none   -- empty segment: no protocol, no value
        | _ => parseSeg fuel' rest'
    | _ => parseSeg fuel' s

end

/-- Parse the text form. Strict like Go's `NewString`: the string must
start with `/`, segments must be non-empty (`//` fails - the empty
token names no protocol), one optional trailing `/` is tolerated. Path
protocols are handled at the raw-string level: `unix` consumes the rest
of the address verbatim, `http-path` takes one percent-escaped segment. -/
def parse? (s : String) : Option Multiaddr := do
  guard (s.startsWith "/")
  let cs := s.toList.drop 1
  -- one trailing '/' carries no meaning (Go, TestEqual/TestProtocolsWithString)
  let cs := match cs.getLast? with
    | some '/' => cs.dropLast
    | _ => cs
  guard (!cs.isEmpty)   -- the empty address is rejected (Go), even
                        -- though js prints `/` for it
  let comps ← parseGo (s.length + 1) cs
  some { components := comps }

/-! ## Wire codec (ByteArray, production)

The wire path reads and writes `ByteArray` directly: encoding pushes bytes
through a small builder, decoding indexes into the buffer. The `List Nat`
functions above are the proof-facing specification; the fuzz property tests
in `Tests/MultiaddrOps` check production/spec equivalence on every run
(`decodeBinB b = decodeBin (Bytes.toNatList b)` and
`encodeBinB cs = Bytes.ofNatList (encodeBin cs)`), so the two cannot drift.
-/

/-- Push the uvarint encoding of `n`. -/
def writeVarintB : Nat → ByteArray → ByteArray
  | n, b => if n < 128 then b.push (UInt8.ofNat n)
            else writeVarintB (n / 128) (b.push (UInt8.ofNat (n % 128 + 128)))
termination_by n => n
decreasing_by omega

/-- Push raw bytes. -/
def writeBytesB (bs : List Nat) (b : ByteArray) : ByteArray :=
  bs.foldl (fun acc n => acc.push (UInt8.ofNat n)) b

/-- Push a uvarint-length-prefixed byte string. -/
def writeLenValueB (bs : List Nat) (b : ByteArray) : ByteArray :=
  writeBytesB bs (writeVarintB bs.length b)

private def writeU16beB (n : Nat) (b : ByteArray) : ByteArray :=
  b.push (UInt8.ofNat (n / 256 % 256)) |>.push (UInt8.ofNat (n % 256))

/-- Binary bytes of one component (the wire encoder). -/
def encodeCompB (c : AddrComponent) : ByteArray :=
  let v (n : Nat) : ByteArray := writeVarintB n ByteArray.empty
  let bytes (s : String) : List Nat := Bytes.toNatList (Bytes.ofString s)
  match c with
  | .ip4 a b cc d => writeBytesB [a, b, cc, d] (v 4)
  | .ip6 gs => gs.foldl (fun acc g => writeU16beB g acc) (v 41)
  | .ip6zone z => writeLenValueB (bytes z) (v 42)
  | .ipcidr n => (v 43).push (UInt8.ofNat (n % 256))
  | .tcp p => writeU16beB p (v 6)
  | .udp p => writeU16beB p (v 273)
  | .dccp p => writeU16beB p (v 33)
  | .sctp p => writeU16beB p (v 132)
  | .dns n => writeLenValueB (bytes n) (v 53)
  | .dns4 n => writeLenValueB (bytes n) (v 54)
  | .dns6 n => writeLenValueB (bytes n) (v 55)
  | .dnsaddr n => writeLenValueB (bytes n) (v 56)
  | .sni n => writeLenValueB (bytes n) (v 449)
  | .unix p => writeLenValueB (bytes p) (v 400)
  | .httpPath p => writeLenValueB (bytes p) (v 481)
  | .p2p mh _ => writeBytesB mh (writeVarintB mh.length (v 421))
  | .onion h p => writeU16beB p (writeBytesB h (v 444))
  | .onion3 h p => writeU16beB p (writeBytesB h (v 445))
  | .garlic64 bs => writeLenValueB bs (v 446)
  | .garlic32 bs => writeLenValueB bs (v 447)
  | .certhash mh => writeLenValueB mh (v 466)
  | .memory n =>
      (v 777).push (UInt8.ofNat (n / 2 ^ 56 % 256))
        |>.push (UInt8.ofNat (n / 2 ^ 48 % 256))
        |>.push (UInt8.ofNat (n / 2 ^ 40 % 256))
        |>.push (UInt8.ofNat (n / 2 ^ 32 % 256))
        |>.push (UInt8.ofNat (n / 2 ^ 24 % 256))
        |>.push (UInt8.ofNat (n / 2 ^ 16 % 256))
        |>.push (UInt8.ofNat (n / 2 ^ 8 % 256))
        |>.push (UInt8.ofNat (n % 256))
  | .ech s => writeLenValueB (bytes s) (v 9849)
  | .udt => v 301
  | .utp => v 302
  | .tls => v 448
  | .noise => v 454
  | .quic => v 460
  | .quicV1 => v 461
  | .webtransport => v 465
  | .http => v 480
  | .https => v 443
  | .ws => v 477
  | .wss => v 478
  | .p2pWebsocketStar => v 479
  | .p2pStardust => v 277
  | .p2pWebrtcStar => v 275
  | .p2pWebrtcDirect => v 276
  | .webrtcDirect => v 280
  | .webrtc => v 281
  | .p2pCircuit => v 290

/-- Binary bytes of the address (the wire encoder). -/
def encodeBinB (ps : List AddrComponent) : ByteArray :=
  ps.foldl (fun acc c => acc.append (encodeCompB c)) ByteArray.empty

/-- Varint at index `i`: `(value, next index)`. -/
private def readVarintB (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  match Varint.decodeBAt? 9 b i with
  | some (v, c) => some (v, i + c)
  | none => none

private def takeNB (n : Nat) (b : ByteArray) (i : Nat) :
    Option (List Nat × Nat) :=
  if i + n ≤ b.size then some (Bytes.toNatList (b.extract i (i + n)), i + n)
  else none

/-- Fuel-bounded wire decoder over `ByteArray`: fuel bounds the component
count, the index tracks the read position. Validation matches the List
specification, including the terminal path rule (no component after
`unix`) and the 8-byte big-endian `memory` value. -/
def decodeBinFB : Nat → ByteArray → Nat → Option (List AddrComponent)
  | 0, _, _ => none
  | f + 1, b, i =>
      if b.size ≤ i then some []
      else do
        let (code, ci) ← readVarintB b i
        match code with
        | 4 => do
            let (v, i') ← takeNB 4 b ci
            some (AddrComponent.ip4 (v.getD 0 0) (v.getD 1 0) (v.getD 2 0)
              (v.getD 3 0) :: (← decodeBinFB f b i'))
        | 41 => do
            let (v, i') ← takeNB 16 b ci
            let g k := 256 * (v.getD (2 * k) 0) + (v.getD (2 * k + 1) 0)
            some (AddrComponent.ip6 [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7] ::
              (← decodeBinFB f b i'))
        | 42 => do
            let (len, ci) ← readVarintB b ci
            let (v, i') ← takeNB len b ci
            let zone ← Bytes.toString? (Bytes.ofNatList v)
            guard (0 < v.length)
            guard (!zone.contains '/')
            let (code2, ci2) ← readVarintB b i'
            guard (code2 = 41)
            let (v, i'') ← takeNB 16 b ci2
            let g k := 256 * (v.getD (2 * k) 0) + (v.getD (2 * k + 1) 0)
            some (AddrComponent.ip6zone zone :: AddrComponent.ip6
              [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7] :: (← decodeBinFB f b i''))
        | 43 => do
            let (v, i') ← takeNB 1 b ci
            some (AddrComponent.ipcidr (v.getD 0 0) :: (← decodeBinFB f b i'))
        | 6 => do
            let (v, i') ← takeNB 2 b ci
            some (AddrComponent.tcp (256 * (v.getD 0 0) + (v.getD 1 0)) ::
              (← decodeBinFB f b i'))
        | 273 => do
            let (v, i') ← takeNB 2 b ci
            some (AddrComponent.udp (256 * (v.getD 0 0) + (v.getD 1 0)) ::
              (← decodeBinFB f b i'))
        | 33 => do
            let (v, i') ← takeNB 2 b ci
            some (AddrComponent.dccp (256 * (v.getD 0 0) + (v.getD 1 0)) ::
              (← decodeBinFB f b i'))
        | 132 => do
            let (v, i') ← takeNB 2 b ci
            some (AddrComponent.sctp (256 * (v.getD 0 0) + (v.getD 1 0)) ::
              (← decodeBinFB f b i'))
        | 53 | 54 | 55 | 56 | 449 => do
            let (len, ci) ← readVarintB b ci
            let (v, i') ← takeNB len b ci
            let nm ← Bytes.toString? (Bytes.ofNatList v)
            guard (0 < v.length)
            guard (!nm.contains '/')
            let c := if code = 53 then AddrComponent.dns nm
                     else if code = 54 then AddrComponent.dns4 nm
                     else if code = 55 then AddrComponent.dns6 nm
                     else if code = 56 then AddrComponent.dnsaddr nm
                     else AddrComponent.sni nm
            some (c :: (← decodeBinFB f b i'))
        | 400 => do
            -- path protocol, terminal: length-prefixed value, and the
            -- buffer must end after it
            let (len, ci) ← readVarintB b ci
            let (v, i') ← takeNB len b ci
            guard (2 ≤ v.length)
            guard (v.getD 0 0 = 0x2f)
            guard (v.getD (v.length - 1) 1 != 0x2f)
            guard (i' = b.size)
            let p ← Bytes.toString? (Bytes.ofNatList v)
            some [AddrComponent.unix p]
        | 481 => do
            let (len, ci) ← readVarintB b ci
            let (v, i') ← takeNB len b ci
            guard (0 < v.length)
            let p ← Bytes.toString? (Bytes.ofNatList v)
            some (AddrComponent.httpPath p :: (← decodeBinFB f b i'))
        | 421 => do
            let (len, ci) ← readVarintB b ci
            let (v, i') ← takeNB len b ci
            let mh ← Multihash.decode? v
            guard (Multihash.validPeer mh)
            some (AddrComponent.p2p v false :: (← decodeBinFB f b i'))
        | 444 => do
            let (v, i') ← takeNB 12 b ci
            let port := 256 * (v.getD 10 0) + (v.getD 11 0)
            guard (port != 0)
            some (AddrComponent.onion (v.take 10) port :: (← decodeBinFB f b i'))
        | 445 => do
            let (v, i') ← takeNB 37 b ci
            let port := 256 * (v.getD 35 0) + (v.getD 36 0)
            guard (port != 0)
            some (AddrComponent.onion3 (v.take 35) port :: (← decodeBinFB f b i'))
        | 446 => do
            let (len, ci) ← readVarintB b ci
            let (v, i') ← takeNB len b ci
            guard (386 ≤ v.length)
            some (AddrComponent.garlic64 v :: (← decodeBinFB f b i'))
        | 447 => do
            let (len, ci) ← readVarintB b ci
            let (v, i') ← takeNB len b ci
            guard (v.length = 32 ∨ 35 ≤ v.length)
            some (AddrComponent.garlic32 v :: (← decodeBinFB f b i'))
        | 466 => do
            let (len, ci) ← readVarintB b ci
            let (v, i') ← takeNB len b ci
            let _ ← Multihash.decode? v
            some (AddrComponent.certhash v :: (← decodeBinFB f b i'))
        | 777 => do
            -- memory: exactly 8 bytes, big-endian u64
            let (v, i') ← takeNB 8 b ci
            some (AddrComponent.memory
              (v.getD 0 0 * 2 ^ 56 + v.getD 1 0 * 2 ^ 48 + v.getD 2 0 * 2 ^ 40 +
                v.getD 3 0 * 2 ^ 32 + v.getD 4 0 * 2 ^ 24 +
                v.getD 5 0 * 2 ^ 16 + v.getD 6 0 * 2 ^ 8 +
                v.getD 7 0) :: (← decodeBinFB f b i'))
        | 9849 => do
            let (len, ci) ← readVarintB b ci
            let (v, i') ← takeNB len b ci
            guard (0 < v.length)
            let s ← Bytes.toString? (Bytes.ofNatList v)
            some (AddrComponent.ech s :: (← decodeBinFB f b i'))
        | 301 => some (AddrComponent.udt :: (← decodeBinFB f b ci))
        | 302 => some (AddrComponent.utp :: (← decodeBinFB f b ci))
        | 448 => some (AddrComponent.tls :: (← decodeBinFB f b ci))
        | 454 => some (AddrComponent.noise :: (← decodeBinFB f b ci))
        | 460 => some (AddrComponent.quic :: (← decodeBinFB f b ci))
        | 461 => some (AddrComponent.quicV1 :: (← decodeBinFB f b ci))
        | 465 => some (AddrComponent.webtransport :: (← decodeBinFB f b ci))
        | 480 => some (AddrComponent.http :: (← decodeBinFB f b ci))
        | 443 => some (AddrComponent.https :: (← decodeBinFB f b ci))
        | 477 => some (AddrComponent.ws :: (← decodeBinFB f b ci))
        | 478 => some (AddrComponent.wss :: (← decodeBinFB f b ci))
        | 479 => some (AddrComponent.p2pWebsocketStar :: (← decodeBinFB f b ci))
        | 277 => some (AddrComponent.p2pStardust :: (← decodeBinFB f b ci))
        | 275 => some (AddrComponent.p2pWebrtcStar :: (← decodeBinFB f b ci))
        | 276 => some (AddrComponent.p2pWebrtcDirect :: (← decodeBinFB f b ci))
        | 280 => some (AddrComponent.webrtcDirect :: (← decodeBinFB f b ci))
        | 281 => some (AddrComponent.webrtc :: (← decodeBinFB f b ci))
        | 290 => some (AddrComponent.p2pCircuit :: (← decodeBinFB f b ci))
        | _ => none

/-- Wire decoder over `ByteArray`. -/
def decodeBinB (b : ByteArray) : Option (List AddrComponent) :=
  decodeBinFB (2 * b.size + 1) b 0

/-! ## Byte API -/

/-- Binary bytes (List Nat view) of the address. This is the
proof-facing specification encoding; the wire bytes are
`toByteArray`. -/
def toBytes (m : Multiaddr) : List Nat :=
  encodeBin m.components

/-- Parse from the `List Nat` byte view. -/
def ofBytes? (bs : List Nat) : Option Multiaddr := do
  return { components := ← decodeBin bs }

/-- Binary bytes of the address (the production wire encoder). -/
def toByteArray (m : Multiaddr) : ByteArray :=
  encodeBinB m.components

/-- Parse from binary bytes (the production wire decoder). -/
def ofByteArray? (b : ByteArray) : Option Multiaddr := do
  return { components := ← decodeBinB b }

/-! ## Operations API (go-multiaddr / js-multiaddr) -/

/-- Append `extra` to `m`. -/
def encapsulate (m extra : Multiaddr) : Multiaddr :=
  { components := m.components ++ extra.components }

private def lastIndexOf (haystack needle : List AddrComponent) : Option Nat :=
  ((List.range (haystack.length + 1)).filter (fun i =>
      i + needle.length ≤ haystack.length ∧
      (haystack.drop i).take needle.length == needle)).getLast?

/-- Remove the last occurrence of `sub` from `m` and everything after it
(Go semantics). `sub` not contained: returns `m` unchanged. Contained but
nothing remains: `none` (Go nil). See `decapsulateThrow?` for the js
convention where a missing subaddress is an error. -/
def decapsulate? (m sub : Multiaddr) : Option Multiaddr :=
  match lastIndexOf m.components sub.components with
  | none => some m  -- Go: not contained -> unchanged
  | some i =>
      let kept := m.components.take i
      if kept.isEmpty then none else some { components := kept }

/-- js `.decapsulate`: `none` when the subaddress is not contained (js
throws), otherwise the Go result. -/
def decapsulateThrow? (m sub : Multiaddr) : Option Multiaddr :=
  match lastIndexOf m.components sub.components with
  | none => none
  | some _ => decapsulate? m sub

/-- Remove the last occurrence of a component with the given code and
everything after it. Missing codes leave the address unchanged
(js decapsulateCode). -/
def decapsulateCode (m : Multiaddr) (c : Nat) : Multiaddr :=
  let idx := (m.components.zipIdx.filter (fun (x, _) => code x = c))
    |>.map (fun (_, i) => i) |>.getLast?
  match idx with
  | none => m
  | some i => { components := m.components.take i }

/-- Split into single-component addresses (Go Split). -/
def split (m : Multiaddr) : List Multiaddr :=
  m.components.map (fun c => { components := [c] })

/-- Join split addresses back (Go Join). -/
def join (ms : List Multiaddr) : Multiaddr :=
  { components := ms.flatMap (·.components) }

/-- A protocol-value view of a component, as reported by js
`getComponents`: `none` for value-less protocols. -/
structure Component where
  code : Nat
  name : String
  value : Option String
deriving Repr, BEq

/-- js-style components: p2p values print base58, `unix` drops the leading
slash and percent-decodes, `http-path` reports the decoded path. -/
def component : AddrComponent → Component
  | c@(.ip4 a b cc d) => ⟨code c, name c, some s!"{a}.{b}.{cc}.{d}"⟩
  | c@(.ip6 gs) => ⟨code c, name c, some (ip6String gs)⟩
  | c@(.ip6zone z) => ⟨code c, name c, some z⟩
  | c@(.ipcidr n) => ⟨code c, name c, some s!"{n}"⟩
  | c@(.tcp p) => ⟨code c, name c, some s!"{p}"⟩
  | c@(.udp p) => ⟨code c, name c, some s!"{p}"⟩
  | c@(.dccp p) => ⟨code c, name c, some s!"{p}"⟩
  | c@(.sctp p) => ⟨code c, name c, some s!"{p}"⟩
  | c@(.dns n) => ⟨code c, name c, some n⟩
  | c@(.dns4 n) => ⟨code c, name c, some n⟩
  | c@(.dns6 n) => ⟨code c, name c, some n⟩
  | c@(.dnsaddr n) => ⟨code c, name c, some n⟩
  | c@(.sni n) => ⟨code c, name c, some n⟩
  | c@(.unix p) =>
      ⟨code c, name c,
       percentDecode? (String.ofList (p.toList.drop 1))⟩
  | c@(.httpPath p) => ⟨code c, name c, some p⟩
  | c@(.p2p mh _) => ⟨code c, name c, some (Base58.encode mh)⟩
  | c@(.onion h p) => ⟨code c, name c, some s!"{b32Body h}:{p}"⟩
  | c@(.onion3 h p) => ⟨code c, name c, some s!"{b32Body h}:{p}"⟩
  | c@(.garlic64 bs) => ⟨code c, name c, some (garlic64Print bs)⟩
  | c@(.garlic32 bs) => ⟨code c, name c, some (garlic32Print bs)⟩
  | c@(.certhash mh) =>
      ⟨code c, name c,
       some ((Multibase.encode .base64url (Bytes.ofNatList mh)).drop 1).toString⟩
  | c@(.memory n) => ⟨code c, name c, some s!"{n}"⟩
  | c@(.ech s) => ⟨code c, name c, some s⟩
  | c => ⟨code c, name c, none⟩

/-- js `getComponents`. -/
def getComponents (m : Multiaddr) : List Component :=
  m.components.map component

/-- Go `Protocols()`: the (code, name) list. -/
def protocols (m : Multiaddr) : List (Nat × String) :=
  m.components.map (fun c => (code c, name c))

/-- Value text of a component in the Go `ValueForProtocol` convention
(`unix` verbatim with its slash, `http-path` percent-escaped, value-less
protocols the empty string). -/
def valueText : AddrComponent → String
  | .ip4 a b cc d => s!"{a}.{b}.{cc}.{d}"
  | .ip6 gs => ip6String gs
  | .ip6zone z => z
  | .ipcidr n => s!"{n}"
  | .tcp p => s!"{p}"
  | .udp p => s!"{p}"
  | .dccp p => s!"{p}"
  | .sctp p => s!"{p}"
  | .dns n => n
  | .dns4 n => n
  | .dns6 n => n
  | .dnsaddr n => n
  | .sni n => n
  | .unix p => p
  | .httpPath p => percentEncode p
  | .p2p mh cid => p2pPrint mh cid
  | .onion h p => s!"{b32Body h}:{p}"
  | .onion3 h p => s!"{b32Body h}:{p}"
  | .garlic64 bs => garlic64Print bs
  | .garlic32 bs => garlic32Print bs
  | .certhash mh => ((Multibase.encode .base64url (Bytes.ofNatList mh)).drop 1).toString
  | .memory n => s!"{n}"
  | .ech s => s
  | .udt => ""
  | .utp => ""
  | .tls => ""
  | .noise => ""
  | .quic => ""
  | .quicV1 => ""
  | .webtransport => ""
  | .http => ""
  | .https => ""
  | .ws => ""
  | .wss => ""
  | .p2pWebsocketStar => ""
  | .p2pStardust => ""
  | .p2pWebrtcStar => ""
  | .p2pWebrtcDirect => ""
  | .webrtcDirect => ""
  | .webrtc => ""
  | .p2pCircuit => ""

/-- Go `ValueForProtocol`: first match; `none` when the protocol is absent. -/
def valueForProtocol? (m : Multiaddr) (c : Nat) : Option String := do
  let comp ← m.components.find? (fun x => code x = c)
  some (valueText comp)

/-- Go `ProtocolsWithString`: the protocol names in a string, WITHOUT
parsing values - every `/`-separated token must be a known protocol name.
Empty tokens (double slashes) are rejected. -/
def protocolsWithString? (s : String) : Option (List (Nat × String)) :=
  let body := (s.toList.dropWhile (· == '/')).reverse
  let body := (body.dropWhile (· == '/')).reverse
  if body.isEmpty then some [] else
  let toks := (String.ofList body).splitOn "/"
  (toks.mapM nameToCode).map (fun codes =>
    (codes.zip toks).map (fun p => (p.1, p.2)))
where
  nameToCode : String → Option Nat
    | "ip4" => some 4 | "tcp" => some 6 | "udp" => some 273
    | "dccp" => some 33 | "ip6" => some 41 | "ip6zone" => some 42
    | "ipcidr" => some 43 | "dns" => some 53 | "dns4" => some 54
    | "dns6" => some 55 | "dnsaddr" => some 56 | "sctp" => some 132
    | "udt" => some 301 | "utp" => some 302 | "unix" => some 400
    | "p2p" => some 421 | "ipfs" => some 421 | "onion" => some 444
    | "onion3" => some 445 | "garlic64" => some 446 | "garlic32" => some 447
    | "tls" => some 448 | "sni" => some 449 | "noise" => some 454
    | "quic" => some 460 | "quic-v1" => some 461
    | "webtransport" => some 465 | "certhash" => some 466
    | "http" => some 480 | "http-path" => some 481 | "https" => some 443
    | "ws" => some 477 | "wss" => some 478
    | "p2p-websocket-star" => some 479 | "p2p-stardust" => some 277
    | "p2p-webrtc-star" => some 275 | "p2p-webrtc-direct" => some 276
    | "webrtc-direct" => some 280 | "webrtc" => some 281
    | "p2p-circuit" => some 290 | "memory" => some 777 | "ech" => some 9849
    | _ => none

/-- Structural equality of components (includes the p2p print form). -/
def equal (m1 m2 : Multiaddr) : Bool := m1.components == m2.components

/-- Go `Contains`. -/
def contains (ms : List Multiaddr) (m : Multiaddr) : Bool := ms.contains m

/-- Deduplicate, keeping the first occurrence (go-multiaddr Unique). -/
def uniqueAddrs (ms : List Multiaddr) : List Multiaddr :=
  ms.foldl (fun acc m => if acc.contains m then acc else acc ++ [m]) []

/-- Go `FilterAddrs`. -/
def filterAddrs (ms : List Multiaddr) (p : Multiaddr → Bool) : List Multiaddr :=
  ms.filter p

/-! ## Marshalers -/

/-- JSON form: a JSON string carrying the text form (Go MarshalJSON). -/
def toJSON (m : Multiaddr) : String :=
  let t := toString m
  String.ofList
    ('"' :: (t.toList.flatMap (fun c =>
      if c == '"' then ['\\', '"']
      else if c == '\\' then ['\\', '\\']
      else [c])) ++ ['"'])

/-- Parse the JSON form. -/
def ofJSON? (s : String) : Option Multiaddr := do
  match s.toList with
  | [] => none
  | '"' :: rest =>
      match rest.reverse with
      | '"' :: revBody =>
          let rec unesc (acc : List Char) : List Char -> Option String
            | [] => some (String.ofList acc.reverse)
            | '\\' :: c :: rest => unesc (c :: acc) rest
            | ['\\'] => none
            | c :: rest => unesc (c :: acc) rest
          let t ← unesc [] revBody.reverse
          parse? t
      | _ => none
  | _ => none

/-! ## Round-trip properties (VECTOR_TEST_PLAN.md phase 1 step 10)

For every component kind whose value does not pass through UTF-8 strings or
percent/base transcoding, binary decoding of the encoding returns the
component. The theorems below are stated on the `List Nat` proof view
(`encodeBin` / `decodeBin`); string-transcoded kinds (dns*, sni, unix,
http-path, ech, ip6zone) would need UTF-8 round-trip lemmas that the byte
model does not track and are covered by the vector suites and fuzz property
tests instead. Proved here: the 18 value-less protocols and the two u16
port protocols (tcp, udp).
-/

/-- The 18 value-less protocols. -/
def isValueless : AddrComponent → Bool
  | .udt | .utp | .tls | .noise | .quic | .quicV1 | .webtransport | .http
  | .https | .ws | .wss | .p2pWebsocketStar | .p2pStardust | .p2pWebrtcStar
  | .p2pWebrtcDirect | .webrtcDirect | .webrtc | .p2pCircuit => true
  | _ => false

/-- Empty input decodes to the empty address for any positive fuel. -/
theorem decodeBinF_nil : ∀ f : Nat, 0 < f → decodeBinF f [] = some [] := by
  intro f hf0
  match f with
  | 0 => omega
  | f' + 1 => rfl

/-- One-component round trip for tcp: decoding the encoding rebuilds the
component from the two big-endian value bytes. -/
theorem decodeBinF_tcp (f : Nat) (x y : Nat) (hx : x < 256) (hy : y < 256) :
    decodeBinF (f + 1 + 1) ([6, x, y] : List Nat) =
      some [AddrComponent.tcp (256 * x + y)] := by
  have hd : Varint.decodeF 9 [6, x, y] = some (6, [x, y]) := rfl
  simp only [decodeBinF, Varint.decode?]
  rw [hd]
  simp only [Bind.bind, Option.bind_some]
  simp only [takeN]
  simp
  rw [decodeBinF_nil (f + 1) (by omega)]
  rfl

/-- End-to-end round trip for tcp: the u16 port is composed from the two
big-endian value bytes. -/
theorem decodeBin_encodeBin_tcp (p : Nat) (h : p < 65536) :
    decodeBin (encodeBin [AddrComponent.tcp p]) = some [AddrComponent.tcp p] := by
  have hx : p / 256 % 256 < 256 := by omega
  have hy : p % 256 < 256 := by omega
  have hform : encodeBin [AddrComponent.tcp p] = [6, p / 256 % 256, p % 256] := by
    simp [encodeBin, encodeComp, u16be, Varint.encode]
  have h := decodeBinF_tcp 2 (p / 256 % 256) (p % 256) hx hy
  rw [hform]
  show decodeBinF (2 + 1 + 1) ([6, p / 256 % 256, p % 256] : List Nat) = _
  rw [show (256 * (p / 256 % 256) + p % 256) = p from by omega] at h
  exact h

/-- One-component round trip for udp (273 encodes as the two varint bytes
145, 2). -/
theorem decodeBinF_udp (f : Nat) (x y : Nat) (hx : x < 256) (hy : y < 256) :
    decodeBinF (f + 1 + 1) ([145, 2, x, y] : List Nat) =
      some [AddrComponent.udp (256 * x + y)] := by
  have hd : Varint.decodeF 9 [145, 2, x, y] = some (273, [x, y]) := rfl
  simp only [decodeBinF, Varint.decode?]
  rw [hd]
  simp only [Bind.bind, Option.bind_some]
  simp only [takeN]
  simp
  rw [decodeBinF_nil (f + 1) (by omega)]
  rfl

/-- End-to-end round trip for udp. -/
theorem decodeBin_encodeBin_udp (p : Nat) (h : p < 65536) :
    decodeBin (encodeBin [AddrComponent.udp p]) = some [AddrComponent.udp p] := by
  have hx : p / 256 % 256 < 256 := by omega
  have hy : p % 256 < 256 := by omega
  have hform : encodeBin [AddrComponent.udp p] =
      [145, 2, p / 256 % 256, p % 256] := by
    simp [encodeBin, encodeComp, u16be, Varint.encode]
  have h := decodeBinF_udp 2 (p / 256 % 256) (p % 256) hx hy
  rw [hform]
  show decodeBinF (2 + 1 + 1) ([145, 2, p / 256 % 256, p % 256] : List Nat) = _
  rw [show (256 * (p / 256 % 256) + p % 256) = p from by omega] at h
  exact h

set_option maxHeartbeats 2000000 in
/-- Value-less components survive a binary round trip. -/
theorem decodeBin_encodeBin_valueless (c : AddrComponent)
    (h : isValueless c = true) :
    decodeBin (encodeBin [c]) = some [c] := by
  cases c <;> simp_all [isValueless] <;>
    simp [encodeBin, encodeComp, Varint.encode, decodeBin, decodeBinF,
      Varint.decode?, takeN] <;> rfl

