# leanp2p libp2p mux: architecture

`libp2p/mux` holds the `Muxer` values that the ordered configuration
lists of §3.1 carry. The seam types live in `libp2p/core`, and this
package fills them (§3.1, §9, delta 10). yamux is the P0 value:
`Mux.yamux` assigns the `/yamux/1.0.0` id to the session of
`net/yamux`, a session that knows no libp2p (§4.9). mplex is the P2
value, later in the same package, kept for go interop. The eth2
networking spec removed mplex, so no consensus unit waits on it (§8).
The spike validated the yamux parity rule live against go-libp2p, and
the mplex identity rule against the go-mplex spec and in-process (go
v0.50 removed mplex, so the matrix's mplex cells were skipped). The
same node code ran under both muxers in-process and over loopback TCP
(PRINCIPLES 1.3).

## Modules

| Module | Holds, and why |
|---|---|
| `Libp2p/Mux.lean` | the root module; one import line per public submodule |
| `Libp2p/Mux/Constants.lean` | `Mux.yamuxId` (`/yamux/1.0.0`), `Mux.mplexId` (`/mplex/6.7.0`), `Mux.testId`, and the 1 MiB mplex message cap; the named ids of §3.4 and the cap of §5.1, one home per fact (§3.8) |
| `Libp2p/Mux/Yamux.lean` | `Mux.yamux`, the yamux value over the session of `net/yamux` |
| `Libp2p/Mux/Mplex.lean` | the mplex message codec and `Mux.mplex` (P2, §8); the spike reference is `Conn/Mplex.lean` (§10 row 15, §7 row 10) |
| `Libp2p/Mux/Test.lean` | the `Muxer` test value under the fixed id `Mux.testId` (§3.1) |

All declarations live in the `Libp2p.Mux` namespace, and the root
module re-exports the public submodules.

The test value needs no wire format. Its `id` is the fixed
`Mux.testId` of `Constants.lean`, and its `open` builds a session over
any `Connection`, streams and all, with ids handed out from a fixed
sequence. A suite above the transport dials itself over the sim pair
and predicts every id (§3.1, PRINCIPLES 1.4).

## Public surface

- `Mux.yamux : Muxer` carries `id := Mux.yamuxId` and the core seam's
  `open : Role → Connection → ByteArray → ExceptT Core.Error IO
  MuxSession` (§4.9; the core pair, public surface). The `Role` picks
  the stream-id parity inside the session entry of `net/yamux` (the
  yamux pair, public surface). The `ByteArray` argument is the
  negotiation leftover; `open` hands it to the session entry as data,
  and the session loop turns it into the first `Event` (§4.7).
- The error mapping happens once, in `Yamux.lean`: the value lifts the
  session failure into `Core.Error` with one `Except.mapError` (§3.5).
  The upgrader and the host match on `Core.Error` alone.
- The test value of `Test.lean`, per the core pair's assignment (the
  core pair, public surface, "Test values").
- `Mux.mplex : Muxer` is the P2 surface: `id := Mux.mplexId`, the pure
  message codec, and a session that keys streams by
  `(id, initiator)`. The declared message length is capped at 1 MiB
  (§5.1), with the cap named in `Constants.lean`.
- `MuxSession.openStream` carries a `ProtocolId`; the decisions below
  record it (the core pair, public surface).

## Owned contracts and how the package keeps them

1. **The seam carries `id : ProtocolId`, and code compares ids
   only** (§3.1, §3.4). The string literals `/yamux/1.0.0` and
   `/mplex/6.7.0` appear in `Constants.lean` and in no production
   code. The negotiator sees `ProtocolId` values.
2. **A seam value holds no protocol decisions** (§3.1). `Mux.yamux`
   moves the role, the connection, and the leftover into the session
   entry of `net/yamux`, and maps the error back. The frames are that
   package's business.
3. **Lifecycle is part of the seam** (§3.1, §4.1). The `MuxSession`
   each value returns exposes `close : IO Unit` and the session
   completion, and the owner closes and then joins.
4. **Half-close follows the spec exactly, in both muxers** (§5.3,
   PRINCIPLES 2.2). Close ends the write direction of the closer, and
   the read direction keeps working, so the response after our FIN
   still arrives. Reset aborts both directions. The yamux session
   carries its own half-close suite in `net/yamux` (the yamux pair,
   plan); the mplex suite of the plan pins the same sentence, with the
   case the spike's old test missed.
5. **The mplex identity rule is the go-compatibility contract**
   (§4.9). Both sides number their streams from zero, so an id alone
   names no stream, and the session keys every stream by
   `(id, initiator)`. The flag bit routes each inbound message to the
   key it names. The spike validated the rule against the go-mplex
   spec, in-process, and the suite keeps the validation.
6. **The 1 MiB cap is checked before allocation** (§5.1,
   PRINCIPLES 2.3). A declared length over the cap is a protocol
   error, and it tears the session down. The number lives in
   `Constants.lean`, beside the ids.

## Decisions

- **The yamux session lives in `net/yamux`, and the value lives
  here** (§4.9). The session knows no libp2p, so a libp2p-free
  consumer can use it, and the id assignment stays a one-line decision
  at the seam (§9, delta 10). A new muxer lands as a new value, with
  no edit to the upgrader (PRINCIPLES 1.3).
- **One `open` field with a `Role`, following the core pair's fold.**
  The spike split the directions into two seam entries; the core pair
  folded them into one field and left the parity rules inside the
  implementation packages (the core pair, decisions). The yamux value
  passes the `Role` through, and the session entry picks the parity.
- **`MuxSession.openStream` takes a `ProtocolId`.** The spike's
  `MuxHandle.openStream` took the name, mplex put it in its NewStream
  frame, and the other muxers ignored it (§10 row 12; the core pair,
  plan). §3.4 calls a bare `String` a smell, and every real caller
  passes a protocol id, so the seam carries the id. The seam keeps one
  signature, so `Mux.yamux` and `Mux.mplex` stay interchangeable at
  every call site. The yamux value drops the id before it calls the
  session of `net/yamux`, whose SYN frame has no field for it. The
  mplex wire label is the id's string form: the frame carries the name
  as its data, a label the spec gives no semantic value.
- **mplex is P2 and stays in this package's plan** (§8). The eth2 spec
  removed it, so consensus never waits, and older go-libp2p peers and
  other stacks still speak it, so the interop surface of §4.9 stays
  real. Root PLAN W5.4 carries the unit, and §7 row 10 puts mplex last
  inside the libp2p row.

## What the package must not depend on

- Inside libp2p, `core` only (§2: core → {security, mux}). No import
  of `libp2p/security`, `libp2p/negotiate`, `libp2p/host`,
  `libp2p/protocols`, or `libp2p/identity`. A muxer knows no
  `PeerId`, and the `MuxSession` surface names only streams.
- From the net group, `net/yamux` and `net/streams` (§2). The yamux
  value imports the session entry of `net/yamux`; the mplex and test
  sessions import `Connection` and the `Stream` seam. `core` defines
  no re-export for `Connection`, so these modules import `net/streams`
  directly and record the import here, per the core pair's rule (the
  security pair records the same import).
- From the codec group, `codec/varint` only: the mplex header and
  length are uvarints, and §2's group chain puts `codec` to the right
  of `libp2p`.
- From `base`, what the mplex loop needs: `Chan`, `TaskSet`, and
  `OnceRef` from `base/conc`, and the byte model, `DecodeError`, and
  the `Codec`/`LawfulCodec` classes from `base/bytes`, the sets the
  yamux pair lists for the same job.
- No crypto. The muxer runs after security and moves plaintext, and no
  field names a key, a hash, or a cipher.
