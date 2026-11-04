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
| `Libp2p/Mux/Constants.lean` | `Mux.yamuxId` (`/yamux/1.0.0`), `Mux.mplexId` (`/mplex/6.7.0`), `Mux.testId` (`/leanp2p/test-mux/1.0.0`), and `Mux.mplexMessageCap` (1 MiB); the named ids of §3.4 and the cap of §5.1, one home per fact (§3.8) |
| `Libp2p/Mux/Yamux.lean` | `Mux.yamux`, the yamux value over the session of `net/yamux`; the `Role` conversion below |
| `Libp2p/Mux/Mplex.lean` | the mplex message codec and `Mux.mplex` (P2, §8); the spike reference is `Conn/Mplex.lean` (§10 row 15, §7 row 10) |
| `Libp2p/Mux/Test.lean` | `Mux.test : Muxer`, the test value under `Mux.testId` (§3.1) |

All declarations live in the `Libp2p.Mux` namespace, and the root
module re-exports the public submodules.

The test value needs no wire format. Its name is `Mux.test : Muxer`,
and its home is `Libp2p/Mux/Test.lean`. Its `id` is `Mux.testId`.
`Mux.testId.toString = "/leanp2p/test-mux/1.0.0"`. This
repository-local protocol id is used only by test suites.

`open` builds a session over any `Connection`. An `initiator` session
issues `1`, then `3`, then `5`, and so on. A `responder` session
issues `2`, then `4`, then `6`, and so on. Each new session starts
again at the first id of its role. The sequences are disjoint, so the
two ends of one sim pair can open at the same time and still receive
different ids. Stream id `0` stays unused. This role partition is a
test-local rule for predictable, collision-free ids. It does not
define Yamux wire behavior. A suite above the transport dials itself
over the sim pair and predicts every id (§3.1, PRINCIPLES 1.4).

## Public surface

- `Mux.yamux : Muxer` carries `id := Mux.yamuxId` and the core seam's
  `open : Role → Connection → ByteArray → ExceptT Core.Error Async
  MuxSession` (§4.9; the core pair, public surface). `Yamux.lean`
  converts `Role` as the decision below records, and the session entry
  of `net/yamux` then applies that package's parity. The `ByteArray`
  argument is the negotiation leftover. `open` hands it to the session
  entry as data, and the session loop turns it into the first `Event`
  (§4.7).
- The error mapping happens once, in `Yamux.lean`: the value lifts the
  session failure into `Core.Error` with one `Except.mapError` (§3.5).
  The upgrader and the host match on `Core.Error` alone.
- `Mux.test : Muxer` is the test value of `Test.lean` (the core pair,
  public surface, "Test values"). Its id and its stream-id sequences
  are the fixed id and allocation rule above.
- `Mux.mplex : Muxer` is the P2 surface: `id := Mux.mplexId`, the pure
  message codec, and a session that keys streams by
  `(id, initiator)`. The declared message length is capped at
  `Mux.mplexMessageCap` (§5.1).
- `MuxSession.openStream` carries a `ProtocolId`; the decisions below
  record it (the core pair, public surface).

## Owned contracts and how the package keeps them

1. **The seam carries `id : ProtocolId`, and code compares ids
   only** (§3.1, §3.4). The string literals `/yamux/1.0.0`,
   `/mplex/6.7.0`, and `/leanp2p/test-mux/1.0.0` appear in
   `Constants.lean` and in no production code. The negotiator sees
   `ProtocolId` values.
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
   PRINCIPLES 2.3). `Mux.mplexMessageCap` names that 1 MiB limit.
   `Constants.lean` owns it, beside the ids. A declared length over
   the cap is a protocol error, and it tears the session down.
   `Mux.mplex` rejects that length before allocation.

## Decisions

- **The yamux session lives in `net/yamux`, and the value lives
  here** (§4.9). The session knows no libp2p, so a libp2p-free
  consumer can use it, and the id assignment stays a one-line decision
  at the seam (§9, delta 10). A new muxer lands as a new value, with
  no edit to the upgrader (PRINCIPLES 1.3).
- **`Libp2p/Mux/Yamux.lean` converts `Role`, and the Yamux session
  applies parity.** The core pair folded the spike's client and server
  entries into one `open` field (the core pair, decisions). The
  adapter then maps the role. `Core.Role.initiator` selects the Yamux
  client side, which opens odd ids, starting at `1` and advancing by
  two. `Core.Role.responder` selects the Yamux server side, which
  opens even ids, starting at `2` and advancing by two. Yamux reserves
  stream id `0` for session messages. An inbound SYN creates a stream
  when its id has the remote parity. A SYN whose id has the local
  parity creates no stream state. `Libp2p/Mux/Yamux.lean` translates
  `Core.Role` to the side selector that the final W4.3 public API
  exports. `net/yamux` keeps its own client and server sides and
  imports no libp2p module.
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
- From `base`, what the mplex loop needs: `Async`, `Chan`, `TaskSet`,
  and `OnceRef` from `base/conc`, and the byte model, `DecodeError`, and
  the `Codec`/`LawfulCodec` classes from `base/bytes`, the sets the
  yamux pair lists for the same job.
- No crypto. The muxer runs after security and moves plaintext, and no
  field names a key, a hash, or a cipher.
