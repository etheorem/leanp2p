# leanp2p: architecture of the implementation

This document is the blueprint for the **real implementation**, which
starts from scratch. The `spike` branch of this repository holds the
**reference implementation**. It covers phases 0 to 5, and its
`VECTOR_TEST_PLAN.md` records how we validated it. When you implement
a piece, check the spike branch for the wire bytes, the algorithm
shape, the captured vectors, and the regression tests. Check its
hardening rules too. They record every bug that the spike and the
review found.

Use the spike as a reference and this document as the spec. Where the
two differ (bounded channels, the select primitive, the package split,
the code shape), this document wins. A better local design is welcome
while the mechanisms of §3 and the contracts of §4 and §5 hold.

Each rule below states its reason. The spike found its bugs where these
rules were missing, and the review found the rest.

---

## 1. Goal and non-goals

Goal: a libp2p node in Lean 4. It interoperates with go-libp2p on
`tcp + /noise + /yamux`. It is safe against hostile peers on every
pre-authentication byte. It shuts down deterministically. Its protocol
cores are machine-checked.

Non-goals for v1: QUIC and WebTransport transports, kad-dht, NAT
traversal, browser dialing, and TLS and mplex beyond their seams.
Gossipsub is in scope, and §8 ranks it. The layering leaves room for
every non-goal, and no part of the design depends on their absence.

## 2. Package layout

The implementation starts from scratch as one repository with a
`packages/` tree. The tree has two levels. The first level holds the
**groups**: foundations, encodings, crypto, networking, the libp2p
stack, and command-line executables. Each group holds its packages.

```
packages/
  base/                        foundations, no wire-format knowledge
    conc/                      Chan, Pipe, TaskSet, OnceRef, withinDeadline
    bytes/                     List-Nat byte model <-> ByteArray/String
  codec/                       encodings shared by everything above
    varint/                    unsigned varint (multiformats and protobuf both need it)
    multiformats/              multihash, multibase, base58, cid, multiaddr
    proto/                     protobuf wire codec
  crypto/
    Crypto.lean                the facade every caller imports (§3.6)
    pure/                      sha256/sha512/sha1/hmac/hkdf: pure Lean, proved
    backend/                   OpenSSL 3 C shim + @[extern] bindings
  net/                         connections and framing
    streams/                   Connection/Listener/Transport, BufReader,
                               Framing, Stream, tcp transport
    yamux/                     the stream muxer
  libp2p/                      the protocol stack
    identity/                  keys, peer ids
    core/                      ProtocolId, Core.Error, the libp2p seam types
    security/                  Noise XX as a SecurityProtocol value; TLS deferred
    mux/                       Muxer values: yamux (over net/yamux), mplex
    negotiate/                 multistream-select, upgrader
    host/                      swarm/host, peerstore, dedup, deadlines
    protocols/                 identify, ping, echo (demo)
  cli/                         command-line executables: demo node,
                               ping node, interop harness; config and wiring
```

The dependency rules have no exceptions, and a grep in CI enforces
them:

- **Between groups**: `cli → libp2p → net → crypto → codec → base`. A
  group imports only the groups to its right.
- **Within groups, downward only**: `net/yamux → net/streams`,
  `codec/{proto,multiformats} → codec/varint`, and inside `libp2p`
  `identity → core → {security, mux} → negotiate → host → protocols`.
  Implementations import `core`. `negotiate` and `host` import `core`
  and no implementation (§3.1).
- No package left of `libp2p` mentions libp2p, so other projects can
  use these packages.

Varint gets its own package. The multiformats spec and protobuf both
frame lengths with it, and neither should own it. The *key marshaling*
forms (the SEC1/SPKI/PKCS#1 choices and the key-type protobuf) belong
to `libp2p/identity`. `crypto/backend` exposes only the primitives
(§4.6).

The repository is one Lake package. Each leaf is one `lean_lib`, and
the `Crypto` facade is one more, rooted at the group directory (§3.6).
If external users appear, a later mechanical move can split the
packages into separate repositories. Until then, version skew is a
bigger risk than coupling.

**What `cli/` is for.** `cli/` holds everything whose job ends at
`main`: executable entry points, command-line and config parsing, and
the *wiring*. The wiring turns the generic seams into a running node.
It picks the `Transport`, the `SecurityProtocol` list, the muxers, and
the stream handlers. From the spike, `cli/` gets `Main.lean`,
`PingNode.lean`, and the interop harness executables. Two rules keep
`cli/` small:

- `cli/` contains **no protocol logic and no reusable code**. Code that
  a second binary might want goes down into `libp2p/` or lower.
- `cli/` is **disposable**. A consumer project, such as an Ethereum
  consensus client, brings its own node binary and uses only the
  libraries. Our `cli/` serves the demo and the interop and test-plan
  harnesses. It also shows, as running code, how to compose the stack.

**Per-package documentation.** The documentation follows the tree. The
repository keeps this file in `docs/` (cross-package contracts,
dependency rules, priorities). `docs/PLAN.md` sits beside it
(implementation order and parallel work units). Every leaf package
carries two documents of its own:

- `packages/<group>/<pkg>/docs/ARCHITECTURE.md`: the internal design
  of the package. It gives the module map and the public surface. It
  names the §4 and §5 contracts that the package owns and says how the
  package keeps them. It records the decisions with their reasons, and
  what the package must not depend on.
- `packages/<group>/<pkg>/docs/PLAN.md`: the work units of the package
  and their order. It lists the dependencies on units of other
  packages, by the unit id from the root `PLAN.md`. It also names the
  test and vector milestones that close each unit.

The hierarchy is strict. Package docs refine the root docs and never
contradict them. A contract change starts at the root, and the package
docs follow it. Writing the two package documents is the **first work
unit of every package** (see `PLAN.md`).

## 3. How the parts connect

Lean gives six ways to join two pieces of code. Each one answers a
single question: who chooses between implementations, and when? This
section gives each way one job. The table in §3.10 is the rule, and the
subsections give the reasons. A package document may refine these
shapes. To swap one mechanism for another, change this section first.

| Mechanism | Who chooses, and when | Used for |
|---|---|---|
| structure value (a **seam**) | a peer, an address, or the configuration, at runtime | transports, security protocols, muxers, stream handlers, policy hooks, the clock, the random source |
| typeclass (a **class**) | the type, at elaboration | wire codecs, protobuf messages, equality and hashing of identifiers |
| inductive with total maps (a **closed set**) | a table in a spec | key types, frame types and flags, protocol codes, roles, error kinds |
| pure transition function (a **core**) | nobody; data in, data out | every protocol state machine and every codec |
| module boundary (an **import**) | the build | the production crypto implementation, constants, generated tables |
| macro | syntax, at elaboration | nothing, unless the four conditions of §3.9 hold |

One more form, the proof-carrying newtype, chooses nothing. It carries
a fact (a size, a parity, a validated shape) from the boundary check to
every use (§3.7).

Choose the mechanism with these questions, in order:

1. **Who chooses the implementation?** A peer or the configuration at
   runtime: a seam. The type: a class. A finite table in a spec: a
   closed set. The build: an import.
2. **Does it hold state across messages?** Yes: a core plus one loop
   task (§3.3). No: a pure codec plus a validation function.
3. **How does it fail?** Through exactly one of the three channels of
   §3.5.
4. **Does the spec fix a size or a shape?** Check it once at the
   boundary and carry the proof (§3.7).

### 3.1 Seams: structure values for runtime choices

A seam is a `structure` whose fields are the operations of one role in
the stack. `Transport`, `SecurityProtocol`, `Muxer`, `StreamHandler`,
the policy hooks (connection gater, resource manager, address ranker),
`Clock`, and `Rng` are seams. libp2p picks one of each per address or
per negotiation. The host holds them in lists ordered by preference. A
typeclass needs existential packaging to hold an ordered list of unlike
implementations. That packaging *is* a structure, so the seam uses a
structure directly.

**Where the types live.** `Transport`, `Connection`, and `Stream` live
in `net/streams`. `SecurityProtocol`, `Muxer`, `StreamHandler`, and the
policy hooks live in `libp2p/core` (§4.9). `Clock` lives in
`base/conc`, and `Rng` lives in the `Crypto` facade (§3.6). The values
live with their implementations: `Noise.securityProtocol` in
`libp2p/security`, `Mux.yamux` in `libp2p/mux`. The upgrader imports
the types only.

Rules:

- **A seam carries its wire name as data.** Every seam that
  multistream-select negotiates (`SecurityProtocol`, `Muxer`,
  `StreamHandler`) has an `id : ProtocolId` field. The negotiator
  compares `ProtocolId` values only (§3.4).
- **A seam value holds no protocol decisions.** Its fields call a core
  (§3.3) and move bytes. When a seam field needs a `match` on wire
  data, move that match into the core.
- **Every seam has two values from the start**: the production value
  and a test value. The test values are the in-memory transport, a
  clock that the test advances, a seeded `Rng`, and a security protocol
  with fixed keys. Every suite above the transport runs on the test
  values (PRINCIPLES 1.4).
- **Lifecycle is part of the seam.** A seam value that creates tasks or
  holds a connection exposes `close : IO Unit`. It also exposes a
  completion that the owner can wait on (a `Task`, or the `TaskSet`
  itself). The owner can then close it and join it (§4.1, rule 2).
- **A seam exposes no `IO.Ref`.** State belongs to the loop task behind
  the seam (§3.3) or to a host registry (§3.8).
- **The ordered lists are configuration.** `cli/`, or the binary of a
  consumer, assembles them and passes them to `Host.new`. No code below
  `cli/` hard-codes which transport or muxer exists.

### 3.2 Classes: typeclasses for behavior the type fixes

A class fits when exactly one sensible implementation exists per type,
and the code knows the type where it is written. Three groups of
classes cover the stack:

- **`Codec α`** for every pure wire codec: `encode : α → List Nat` and
  `decode? : List Nat → Except DecodeError (α × List Nat)` over the
  byte model (§4.2). The instances are the varint newtype, the yamux
  `Header`, `Multiaddr`, `Multihash`, `Cid`, `Pb.Fields`, and the
  multistream message. `DecodeError` is the shared inductive of
  `base/bytes`. It separates `truncated` (more bytes may complete the
  value) from `malformed` (a protocol error, so the reader stops
  waiting). §4.3 and §5.2 demand that distinction. **`LawfulCodec α`**,
  a `Prop` class, states the round-trip law, and each instance proves
  it. One generic property harness (`∀ [Codec α] [LawfulCodec α]`)
  pins the production `ByteArray` path to the model for every codec at
  once (§6).
- **`ProtoMessage α`** for every libp2p protobuf message:
  `toFields : α → Pb.Fields` and
  `ofFields? : Pb.Fields → Except Pb.Error α`. The instance holds the
  field table as data, and one generic encoder serves every message.
  The class lives in `codec/proto`. The instances live next to the
  message types in `libp2p`.
- **The standard classes** on identifiers: `BEq`, `DecidableEq`,
  `Hashable`, `Ord`, `Repr`, and `ToString` on `PeerId`, `ProtocolId`,
  `StreamId`, `Multiaddr`, and `KeyType`. Derive them. Write one by hand
  only when the derived one breaks the spec, for example a `ToString`
  that must print the text form of the spec.

Rules:

- **One instance per type, and no instance on a core type.** No project
  class gets an instance on `Nat`, `String`, `ByteArray`, `List`, or
  `Option`. Wrap the type first (`structure UVarint where val : Nat`).
  Two instances on one type, or an instance on a type that the package
  does not own, is the orphan problem. Instance search gives no warning
  for it.
- **Instances live with the type.** The module that defines the type
  defines its instances. One exception: when the package of the type
  cannot import the class, the instance lives in the module that
  defines the class.
- **A class never returns `IO`.** A method in `IO` belongs in a seam,
  so make it a structure value.
- **No `Coe`, `CoeFun`, or `CoeDep` instances.** Conversions are named
  functions (`PeerId.toBytes`, `Multiaddr.ofString?`). A coercion hides
  the place where bytes change form. Every encoding bug so far sat at
  such a place.
- **Instance search stays one step deep.** Lean finds an instance from
  the head type alone, or from one container over an instance
  (`Codec (List α)`). Use no chains, no `outParam`, and no default
  instances.

### 3.3 Cores: pure state machines, one loop per connection

Every protocol that holds state across messages is a pure transition
function. Its state, inputs, and outputs are plain data:

```lean
structure State where …   -- no IO.Ref, no function, no Task
inductive Event where …   -- bytes arrived; the application wrote, opened,
                          -- or closed a stream; a tick; a seed
inductive Action where …  -- write these bytes; deliver these bytes to
                          -- stream k; open stream k to the application;
                          -- answer tag t; close the connection
def step : State → Event → Except ProtocolError (State × List Action)
```

Multistream-select, the Noise handshake and transport, yamux, mplex,
the req/resp framework, and the gossipsub router all take this shape.
The IO shell is **one loop task per connection**. The loop receives
`Event`s from one bounded `Chan`, calls `step`, and performs the
`Action`s. It exits when `step` reports an error or the connection
closes. One reader task turns connection reads into `Event.bytes` on
the same channel. When the channel is full, the reader waits, and the
TCP window carries the back-pressure to the peer. Every byte that
arrives, every application write, every timer, and every random value
becomes an `Event` before the core sees it. The core never calls `IO`.

This shape replaces the spike sessions, which guard mutable fields one
by one and take a mutex per writer. It gives four things:

- **Tests step the machine.** A captured go-libp2p transcript is a list
  of `Event`s, and the expected frames are a list of `Action`s. The
  test needs no network, no tasks, and no timing. The hostile-frame
  suite is the same test with a different list.
- **`-N1` holds by construction.** The loop blocks on one channel.
  Nothing inside a session spins, polls, or takes a lock.
- **Little shared state remains.** One task owns the session state, so
  §4.1 rule 3 applies only to the host registries (§3.8).
- **Invariants become theorems.** The receive window never goes
  negative. Stream ids keep their parity. A retired id is never reused.
  Each one is a statement about `step`, and `simp` and `omega` close
  it.

Rules:

- `step` is total, so a core contains no `partial`. The loop that
  drives it is `partial`, and its docstring says why. It is the only
  `partial def` the package needs.
- `State`, `Event`, and `Action` derive `Repr` and `BEq`, so tests
  compare them by value. They carry no `IO.Ref`, `Task`, `IO.Promise`,
  or function.
- The shell learns about `State` only from the `Action`s. A shell that
  reads a window counter out of the state is a second state machine.
- **The shell correlates completions by tag.** An application write is
  `Event.write sid tag bytes`. The core answers with `Action.done tag`
  when the bytes have gone to the wire, or with `Action.refused tag e`
  when they cannot go. The shell maps tags to the promises that
  `Stream.write` waits on. Back-pressure stays exact (§5.1), and no
  promise enters the core.
- **Time and randomness are inputs.** `Event.tick now` carries the
  clock. A seed or key material arrives in the event that needs it,
  and the `Clock` and `Rng` seams of the shell supply them. A test
  cannot replay a core that reads the clock.
- **A core may call pure externs** (§3.6). SHA-256, HKDF, AEAD seal and
  open, and X25519 are deterministic functions, so the Noise core calls
  them directly.
- **The application view is a seam over the loop.** `Stream` is a
  structure. Its `read` takes from a per-stream bounded `Chan` that the
  loop fills. Its `write`, `close`, and `reset` post `Event`s. The
  handler never touches the loop.
- A protocol with one exchange and no session (identify, ping) needs
  no `step`. It needs a pure codec, a pure `validate`, and a short IO
  function. That function reads one message, validates it, and
  answers.

### 3.4 Closed sets: inductives with total maps

A set that the spec enumerates is an `inductive`. Examples: `KeyType`,
the yamux frame type and `GoAway` code, the multistream replies (`na`,
`ls`), the multiaddr protocol table, the multicodec and multibase
tables, `Role`, and every error kind (§3.5). No bare `Nat` or `String`
stands for a member of such a set.

Rules:

- `deriving DecidableEq, Repr, Hashable`, plus `Inhabited` only where a
  container needs it.
- Two total maps, `toCode : T → Nat` and `ofCode? : Nat → Option T`,
  with the theorem `ofCode?_toCode : ofCode? (toCode t) = some t`. The
  theorem is the conformance proof of the table, and `decide` closes
  it.
- **Flag sets are structures of `Bool`**, such as
  `{ syn, ack, fin, rst : Bool }`, with their own `Codec` instance. Bit
  arithmetic happens once, in the codec.
- **Open sets stay strings, wrapped.** Peers define protocol ids and
  agent versions, so these are `structure ProtocolId where toString :
  String` with derived `DecidableEq` and `Hashable`. The known ids are
  named constants in one module per package (`Mux.yamuxId`,
  `Identify.protocolId`). Code compares `ProtocolId` values, and string
  literals appear only in that module.

### 3.5 Errors: three channels, one per kind of failure

A function fails in exactly one of three ways, and its type says which:

| Channel | Type | Meaning |
|---|---|---|
| protocol failure | `Except E α`, `E` an inductive the package owns | the peer, or our own input, broke the spec |
| end of stream | `Option α` from a read, `none` | the peer finished; an orderly event |
| fault | `IO.Error`, thrown | the system failed: a socket error, an allocation failure, an FFI fault |

Rules:

- **A pure function returns `Except E α`.** It may return `Option` only
  when `none` has one meaning and the docstring states it (a lookup
  miss, the end of input). A decoder that returns `Option` cannot tell
  "truncated" from "malformed", and §5.2 needs that distinction at
  every layer.
- **Every package owns one error inductive** (`Varint.Error`,
  `Yamux.ProtocolError`, `Noise.Error`); a package that holds several
  independent protocols owns one per protocol, each mapped into
  `Core.Error` at its own seam. A seam returns `Core.Error`
  (§4.9), the coarse type that the upgrader and the host can act on.
  The implementation maps its own type into `Core.Error` once, at the
  seam value, with `Except.mapError`. `libp2p/host` wraps `Core.Error`
  in `Host.Error` with arms of its own, so the host and `cli/` match on
  one type.
- **An IO shell that can fail with a protocol error has the type
  `ExceptT E IO α`**, which is `IO (Except E α)` with `do` notation. A
  `throw` inside it throws `E`. An `IO.Error` from a socket passes
  underneath and reaches the owner as a fault.
- **No `IO.userError` for a protocol condition.** A string error hides
  the kind of failure from the code that must act on it.
- **A protocol failure closes the connection.** The core returns
  `.error e`. The loop tears the connection down and reports `e` to the
  owner through the completion of the session. An owner never learns
  of a failure by reading EOF (§5.2).

### 3.6 FFI bindings: pure where the function is pure

`crypto/backend` binds OpenSSL through `@[extern]` declarations. The
type of each binding states what the C function does:

- **Deterministic primitives are pure.** This covers SHA-256 and
  SHA-512, HMAC, HKDF, ChaCha20-Poly1305 seal and open, X25519, Ed25519
  sign and verify, every verifier, and every public-key derivation.
  Their bindings are `opaque f (… : @& ByteArray) : Option ByteArray`
  or `: Bool`, with no `IO`. The Lean interface lifts `Option` to
  `Except CryptoError`. A pure binding is a promise that the shim must
  keep: same input, same output, no read of global state, no side
  effect. The docstring of each binding records that promise.
- **Randomness is `IO`.** `randomBytes`, key generation, and the
  signatures that draw a random nonce (ECDSA P-256, secp256k1) return
  `IO (…)`. Ed25519 and RSASSA-PKCS1-v1_5 sign deterministically, so
  their bindings stay pure.
- Every `ByteArray` argument is borrowed (`@&`). The Lean side checks
  sizes into proof-carrying newtypes (§3.7) before the call, so the
  shim validates nothing twice.

**The facade.** Callers import `Crypto`, the root module of the group
at `packages/crypto/Crypto.lean`. No caller imports `crypto/backend`,
`crypto/pure`, or an etheorem package.
`Crypto` is one `lean_lib` made of `export` and
`abbrev` lines that name the production implementation of each
primitive: the backend for the primitives it binds, the etheorem
packages for the four primitives that route there. It also holds the
`Rng` seam. The pure package is the oracle home that the cross-check
(PLAN W3.3) runs against the production path. To move one
primitive to pure Lean or to another native library, change one line of
the facade. No call site changes. A class with a tag type
(`[Hasher Sha256]`) would give the same swap, at the cost of a class
parameter on every consumer. Nothing here chooses a hash by type, so
the import is the right mechanism.

### 3.7 Proof-carrying newtypes: check once at the boundary

The code checks a size or shape that the spec fixes where the bytes
enter. From there, it carries the result as a fact:

```lean
structure Key32 where
  bytes : ByteArray
  size_eq : bytes.size = 32

def Key32.ofByteArray? (b : ByteArray) : Option Key32 := …
```

`Key32`, `Nonce12`, `Digest32`, the 12-byte yamux header, `PeerId` (a
validated multihash), `StreamId` (with its parity), `Multiaddr` (a
validated component list), `Fields` (every entry fits the varint
budget of `codec/varint`, §4.5), and `ProtocolId` all take this form.
Lean erases the proof field at runtime, so the newtype costs nothing. A
core that takes `Key32` never indexes with `!` and never checks the
size again. `Vector UInt8 n` from core Lean does the same job for
fixed-size fields that stay in Lean. `ByteArray` with a size proof is
the form that crosses the FFI.

Use `abbrev` for a synonym with no invariant and no instances of its
own (a `Payload := ByteArray` synonym would be one). When a type needs
an instance or carries a fact, make it a `structure`.

### 3.8 Imports and host registries

The import graph is a mechanism too, with three binding uses:

- **Each package has one constants module** (`Yamux.Constants`,
  `Noise.Constants`) for caps, windows, timeouts, and protocol ids.
  Every other module of the package imports it (PRINCIPLES 1.5).
- **Generated tables are committed source.** The multiaddr protocol
  table and the multicodec table come from the vendored CSV. A Lean
  script, run with `lake env lean --run`, generates the `.lean` file,
  and the repository commits it. A test asserts that the file matches
  the CSV. Reviewers can read and grep a committed file. They cannot
  read or grep a macro expansion.
- **The facade** of §3.6 is the swap point for native implementations.

The host registries hold the shared state that remains after §3.3: the
live sessions by peer, the stream handlers by protocol id, and the
peerstore. Each registry is a `Std.HashMap` inside an `OnceRef`. Only a
pure update function, applied under `OnceRef.update`, changes it.
Liveness is a field in the table. The loop of a session sets it on exit
through the same update. The dedup rule is then one pure function over
the table, with no probe before a commit.

### 3.9 Macros: only when nothing else fits

No `syntax`, `macro`, `macro_rules`, `elab`, `notation`, or custom
`deriving` handler goes into a library package unless all four
conditions hold:

1. The generated shape appears by hand three or more times, and the
   copies have drifted or will drift.
2. The author tried a function, a class, a structure, and a committed
   generator (§3.8). The module docstring records why each one fails.
3. The macro is the only content of its module, so an import of it is
   a visible decision.
4. An `example` next to the macro shows the expansion, and the
   generated declarations carry docstrings.

The standard `deriving` handlers (`Repr`, `BEq`, `DecidableEq`,
`Hashable`, `Ord`, `Inhabited`) fall outside this rule. Use them
freely. `#guard` is the assertion form for vectors that the build
checks, and it needs no macro.

Four candidates already have answers. The protocol tables use a
generator (§3.8). Protobuf messages are hand-written `ProtoMessage`
instances over a field table. The vector suites are plain functions
and `#guard`. `Event` and `Action` stay written out in full, because a
reader must see every case.

### 3.10 The table

| Connection | Mechanism | Owner |
|---|---|---|
| which transport, security protocol, or muxer | seam (`Transport`, `SecurityProtocol`, `Muxer`); ordered lists from `cli/` | types: `net/streams`, `libp2p/core`; values: `libp2p/security`, `libp2p/mux` |
| which handler serves a stream | `Std.HashMap ProtocolId StreamHandler` in the host | `libp2p/host` |
| encoding of a wire type | `Codec α` + `LawfulCodec α` | the package of the type |
| a protobuf message | `ProtoMessage α` over a hand-written field table | `libp2p/*` |
| a spec enumeration or flag set | inductive + `toCode`/`ofCode?` + theorem; a `Bool` structure for flags | the package of the type |
| an identifier | newtype structure with derived `DecidableEq`, `Hashable`, `Ord` | `libp2p/identity`, `libp2p/core`, `codec/multiformats` |
| protocol state | pure `step`; one loop task fed by one reader task over a bounded `Chan Event` | each protocol package |
| the application view of a stream | `Stream` seam over the loop; tagged completions | `net/streams` |
| failure | `Except E`; `none` on EOF; `IO.Error` for faults | each package owns its `E` |
| time, randomness | `Event` inputs to the core; `Clock` and `Rng` seams in the shell | `base/conc`, `Crypto` |
| a crypto primitive | pure `@[extern]` behind the `Crypto` facade | `crypto` |
| a fixed size or validated form | proof-carrying newtype, checked at the boundary | the package of the type |
| a constant | one `Constants` module per package | each package |
| a table from a spec CSV | committed generator output | `codec/multiformats` |
| syntax | none, unless §3.9 holds | none |

## 4. The packages

**Dependency strategy for external implementations.** Some
dependencies already exist as mature implementations in another
language: crypto backends today, and compression, TLS, or QUIC stacks
later. We consume them in two phases: **FFI first, Lean later**. Phase
1 binds the existing library through a small C shim behind a Lean
interface, as `crypto/backend` does with OpenSSL 3. Phase 2 happens
only where it pays. It re-implements the dependency in pure Lean
*behind the same interface*, as the pure SHA/HMAC/HKDF modules of the spike
do. Theorems back that code, and a cross-check compares it with the FFI
at the IO edge.

The interfaces therefore allow a swap from the start. Callers depend on
the Lean interface (for crypto, the `Crypto` facade of §3.6) and never
on the FFI. A native implementation can then land, or roll back to the
FFI, with no change at a call site. For cryptographic primitives, the
constant-time code stays in the C shim, and the Lean version serves as
the verified cross-check. For other dependencies, such as snappy (§8),
the native replacement is the eventual goal.

### 4.1 `base/conc`: concurrency primitives

The package provides these primitives:

- `Chan`: a closeable FIFO with a capacity. Close broadcasts EOF after
  the drain.
- `select`: waits for the first of several parks to complete.
- `Pipe`: a byte queue.
- `TaskSet`: a set of owned tasks.
- `OnceRef`: an atomic cell.
- `withinDeadline`: a `select` over the work and a timer. On expiry,
  it closes what the work parks on.
- `Clock`: the time seam, with a test value that the test advances.

Three rules hold in every package above it:

1. **Never cancel; wake by close.** The runtime drops cancelled
   promises, so a cancel strands parked tasks. Every park must have a
   close that reaches it.
2. **Every task has an owner** that joins it. The RTS waits for tasks
   at exit, so only ownership makes exit possible.
3. **Shared state is atomic.** Change it through `OnceRef.update`.
   Never get and then set a bare `IO.Ref`.

The spike missed three requirements, and this package builds them from
the start. Every `Chan` has a capacity. An unbounded channel is a named
exception, with its reason in the docstring. `select` replaces every
hand-rolled first-of loop. `joinAll` reports task errors to the owner.
Lean v4.34 ships the primitives: `Std.Sync.CloseableChannel` with a
capacity, `Std.Async.Selectable`, and `Std.Async.Selector.sleep`.
`conc` wraps them so that no other package imports `Std.Sync` or
`Std.Async`. When the toolchain API moves, the wrapper is the one
module to change.

### 4.2 `base/bytes`: the byte model

The package holds the conversions between `List Nat` and `ByteArray`,
`String`, and hex. It also holds the `Codec` and `LawfulCodec` classes
(§3.2), the shared `DecodeError`, and the generic round-trip harness
that every codec package runs. The `List Nat` model is a deliberate
choice. Arithmetic proofs (`omega`) stay tractable on it, and the
verified codec cores state their theorems over it. Every production
path gets a `ByteArray` decoder and encoder. Fuzz property tests pin
each one to the model (`decodeBinB b = decodeBin (toNatList b)`), so
the proof view and the production view cannot drift.

### 4.3 `codec/varint`: unsigned varint

The LEB128 framing integer of the multiformats spec. The package
accepts minimal encodings only, at most 9 bytes (63 bits). It proves
the round-trip and inverse theorems. A varint that cannot complete
within the byte budget is a **protocol error**, and the decoder reports
it as `malformed` (§3.2). This removes the bug of a reader that
accumulates bytes forever at the source, and every consumer inherits
the fix.

### 4.4 `codec/multiformats`: the spec family

Multihash (strict decode, function table), multibase (full registry),
base58btc, CID v0 and v1, and multiaddr (the full protocols.csv table,
a strict text parser, a binary wire codec). This family carries its own
conformance suites: go and js vectors, and fuzz corpora. The suites
belong to the library, so a project that uses it without libp2p still
runs them.

The spike validated two rules, and they stay as requirements. Text
parsers are strict: a leading `/`, no empty segments, no `_` digit
separators, no leading-zero IPv4 octets. Percent codecs operate on the
UTF-8 bytes of the text.

### 4.5 `codec/proto`: protobuf wire codec

Encode and decode over the byte model, with lengths framed by
`codec/varint`. The encoding is deterministic by construction (the
fixed emit order of the field table, minimal varints). Decode keeps
unknown fields, and for a singular field the last occurrence wins. The
core carries a round-trip theorem. The `ProtoMessage` class (§3.2)
lives here. The libp2p
messages (`Keys`, `Identify`, `NoiseHandshakePayload`, `Envelope`,
`PeerRecord`) live *above* this package, in `libp2p`. They are
`ProtoMessage` instances over hand-written field tables.

### 4.6 `crypto`: the edge, the pure copies, and the bindings

Three kinds of code under one group:

- **`crypto/pure`**: the pure Lean implementations (SHA-256/512,
  SHA-1, HMAC, HKDF). Theorems back them, and they serve where a reader
  must audit the code. The backend is the production path for every
  primitive it binds, the digests included; the pure copies are the
  audited implementations and the oracles that the cross-check compares
  with the production path at the IO edge.
- **`crypto/backend`**: the OpenSSL 3 shim (`c/p2pcrypto.c` plus the
  bindings) for the primitives no etheorem package covers: Ed25519,
  X25519, RSA, SHA-1, SHA-512, HMAC, HKDF, ChaCha20-Poly1305, and
  X.509, plus randomness and key generation. This is the "FFI first"
  phase of the dependency strategy (§4 preamble). The package binds
  the mature implementation as it is. Nobody writes constant-time
  primitives in Lean. The pure package above is the "Lean later"
  phase, as verified cross-checks.
- **The etheorem bindings.** Where the etheorem monorepo already binds
  a primitive, the facade routes to its package, and this repo writes
  no second shim. Four primitives route there today: secp256k1
  (`LeanHazmatSecp256k1`, libsecp256k1), ECDSA P-256 (`LeanHazmatP256`,
  OpenSSL), SHA-256 (`LeanHazmatSha256`, OpenSSL and ISA-L), and
  keccak-256 (`LeanHazmatKeccak`, keccak-tiny). The etheorem facts
  constrain the integration: the monorepo pins Lean v4.29.1 against this
  repo's v4.34, the license is LGPL-3.0 with a contributor agreement,
  and the packages are monorepo-resident, with per-package publication
  repos promised but not yet present. Unit W3.2 owns the pins, the
  toolchain-compat checks, and the facade routes; a primitive whose
  pin does not build falls back to the `crypto/backend` shim for the
  interim, recorded in the plan. Keccak-256 is the one exception: no
  own shim exists for it, so a pin that does not build blocks W6.1
  until the pin builds or the owner records a re-vendor.

The spike rules stay:

- Every `ByteArray` argument to a shim is **borrowed** (`@&`). An
  owned parameter leaks one reference per call.
- Binding types follow §3.6: pure for deterministic primitives, `IO`
  for randomness. Callers import the `Crypto` facade only.
- Verifiers enforce the **key type and size**: P-256 SPKI only, RSA
  2048 to 8192 bits only, secp256k1 low-S only. The libsecp256k1
  default already rejects high-S, so the etheorem binding and the
  rule agree.
- X.509 validation checks the validity time and rejects unknown
  critical extensions.
- The libp2p key *marshalings* (the SEC1/PKCS#8/SPKI/PKCS#1 choices,
  the key-type protobuf) belong to `libp2p/identity`. The EVP surface
  stays here.

### 4.7 `net/streams`: connections and readers

The package holds these types:

- `Connection`: read, write, close, and the addresses.
- `Listener`.
- `Transport`: a seam (§3.1) with two values, the in-memory sim and
  TCP.
- `BufReader`: the shell helper for exact-length reads over one
  connection.
- `Framing`: length-prefix framing.
- `Stream`: the application view over the loop of a muxer (§3.3).

Two contracts live here, and no change may drop them:

- **TCP close discipline.** libuv drops cancelled promises, so `close`
  resolves the promise of the parked read itself. A double resolve is a
  no-op. `close` also sends a FIN to the peer. A failed write tears the
  connection down: the local read sees EOF, and the peer gets a FIN.
- **No reader strand.** The stage that over-reads owns those bytes and
  hands them on *as data*. Every upgrade stage takes the leftover
  `ByteArray` of the previous stage and returns its own, so the types
  show the hand-over. The leftover goes to the layer that reads at the
  same level:
  - ciphertext left after the Noise handshake seeds the reader of the
    Noise transport;
  - plaintext left after the muxer negotiation is the first `Event` of
    the muxer loop;
  - plaintext left after the protocol negotiation of a stream goes to
    the front of the stream (`Stream.prependBytes`).

  No two stages share a `BufReader`.

### 4.8 `net/yamux`: the interop muxer

The hashicorp spec over the `Connection` of `net/streams`: a 12-byte
header codec with a proved round-trip, the stream state machine, and
flow control. The spike hardened these rules, and they stay as
requirements:

- The receive window we grant (256 KiB initial) caps data frames, and
  the session checks each frame against it. Data beyond the window is a
  protocol error, and the session does not buffer it.
- Only a **SYN frame with the id parity of the remote** creates a
  stream. The session drops frames for unknown ids. Such frames must
  never create state that a later `openStream` could collide with.
- The session removes a stream once both sides have closed it, so the
  session map cannot grow without bound.
- A writer that uses part of a credit grant hands the wake token on to
  the next parked writer.
- The control queue has a cap, so a hostile ping flood cannot grow it.

### 4.9 `libp2p`: the protocol stack

Everything with libp2p semantics, in subpackages:

- **`identity/`**: keys and `PeerId` (peer-ids spec). It covers four
  key types, deterministic protobuf marshalings, identity inlining up
  to 42 bytes, and strict unmarshal. Strict unmarshal validates the key
  `Data` length per type, so a 31-byte Ed25519 key cannot derive an id.
  The package also owns the key *marshalings* that the crypto backend
  leaves out on purpose (§4.6).
- **`core/`**: the libp2p-wide types, with no protocol logic. It holds
  `ProtocolId` and `Core.Error`, the coarse error that every seam
  returns. `Core.Error` has the arms `protocol`, `authentication`,
  `timeout`, and `closed`. Each arm carries the error of the
  implementation, rendered for the log. `core/` also holds the seam
  structures that every implementation fills: `SecurityProtocol` with
  `SecureConn`, `Muxer` with `MuxSession`, `StreamHandler`, and the
  policy hooks. It depends on `identity` (for `PeerId`) and on
  `net/streams` (for `Connection` and `Stream`), and on nothing else.
- **`security/`**: Noise XX (`Noise_XX_25519_ChaChaPoly_SHA256`) as a
  pure core (§3.3). The handshake is a `step`, and its ephemeral keys
  arrive as an `Event`. A `SecurityProtocol` value wraps the core, with
  `handshake : Role → Connection → ByteArray → ExceptT Core.Error IO
  SecureConn`. The `ByteArray` holds what the negotiation over-read.
  The `SecureConn` already holds what the handshake over-read. A second
  value, with fixed keys, is the test value. Transport rules:
  - a failed AEAD open is a protocol error (§3.5), distinct from EOF,
    and it tears the connection down;
  - handshake payloads have a size cap (8 KiB) that applies before the
    pre-authentication decode;
  - a failed seal tears the connection down.

  The TLS extension is deferred (§8).
- **`negotiate/`**: multistream-select (1 KiB cap, `na` retry, `ls`,
  lazy dialer) and the upgrader.
- **`mux/`**: the `Muxer` values. yamux (P0) assigns the `/yamux/1.0.0`
  id to the session of `net/yamux`. That session lives in `net/yamux`
  because it does not know libp2p. mplex (P2) has go-compatible
  identity: both sides number from zero, and the session keys streams
  by `(id, initiator)`. The spike already validated this against the
  go behavior. Half-close follows the spec. Close ends the write
  direction of the closer only, and reset aborts both directions.
- **`host/`**: the upgrader pipeline (security → identity check →
  muxer) and per-peer connection dedup. Dedup follows the
  simultaneous-dial rule: during the race window, the connection that
  the larger id dialed loses. The rule is a pure update over the
  session table (§3.8). The package also holds the handler registry
  (`HashMap ProtocolId StreamHandler`), the peerstore, and
  `Host.Error`, which wraps `Core.Error` with arms of its own.
- **`protocols/`**: identify (with push) and ping, plus req/resp and
  gossipsub when they land (§8).
- **Policy seams**: connection gater, resource manager, address ranker.
  The interfaces exist now, and the implementations come later.

## 5. Cross-cutting invariants

The implementation must keep these invariants. Each one is testable,
and most already have a regression test in the spike.

1. **Bounded receive path.** Every length-prefixed read has a cap that
   applies before allocation. The framing caps are multistream 1 KiB,
   mplex 1 MiB, yamux 256 KiB, Noise frame 64 KiB, and Noise payload
   8 KiB before authentication. The receiver enforces flow control
   against the sender, and an over-long varint is a protocol error. The
   cost of one message on an anonymous connection depends on the cap
   alone.
2. **Verify before trust.** Every decode before authentication has a
   size cap, and a decode failure closes the connection. Every layer
   can tell a decode failure from EOF (§3.5). A failure is an `Except`
   value, EOF is `none`, and no function reports both through one
   `Option`.
3. **Half-close follows the muxer spec exactly.** In mplex and yamux,
   close ends the write direction of the closer. The response after our
   FIN must still arrive.
4. **Unauthenticated phases have a deadline** (`withinDeadline`; 30 s,
   as in go). A silent dial or listener fails, and no task parks
   forever. The deadline covers only the unauthenticated phase. An
   authenticated connection that sits idle never expires.
5. **Deterministic shutdown.** The order is: set the closing flag →
   close the listeners → close the pending (unauthenticated)
   connections → shut down the sessions → join the session loops →
   join the host tasks. Everything joins, and every park has a close
   that reaches it.
6. **One reader per physical stream.** Negotiation, handshake, secure
   transport, and muxer each read through their own reader. Each stage
   hands the bytes it over-read to the next stage as data (§4.7). A
   stage never re-reads what another stage consumed, and no two stages
   share a reader.

## 6. Verification strategy

The layers match how the spike validated each part:

1. **Theorems on pure cores.** The varint, protobuf, framing, and
   header codecs prove round-trip and inverse properties over the byte
   model, as `LawfulCodec` instances (§3.2). The protocol `step`
   functions (§3.3) prove their invariants: the window never goes
   negative, ids keep their parity, and a retired id is never reused.
2. **Pinned upstream vectors** (`VECTORS.lock`,
   `scripts/extract-vectors.py`). They live on the `spike` branch
   today, and PLAN.md W0.3 carries them into `main`. They include RFC
   test vectors, go-libp2p fixtures, multiformats CSVs, and captured
   transcripts (multistream traces, Noise transport, identify,
   envelopes).
3. **Fuzz property tests** for the `ByteArray` production paths. The
   decoder on the wire must equal the proved model. The generic `Codec`
   harness runs these tests once for every instance.
4. **Transcript tests on cores.** A captured go-libp2p exchange is a
   list of `Event`s, and the expected frames are a list of `Action`s.
   The test drives `step` with no task, no network, and no clock. The
   hostile-frame regressions are the same test with a different list.
5. **In-process end-to-end tests** over the hostile-transport sim (byte
   splitting, sim net) and loopback TCP. Every hardening rule above has
   a regression test.
6. **Interop matrix** against go-libp2p (dial and listen × muxers),
   plus the silent-peer and slow-reader scenarios.

The suite must keep passing under `+RTS -N1`, the starvation criterion
that the concurrency rules exist to meet.

## 7. Bootstrapping: the way to start

The implementation starts from scratch and builds bottom-up. Write each
package of §2 in dependency order, and use the **spike branch as the
working reference** while you do it. For every package, the spike holds
code that produces spec-correct wire bytes. It also holds a captured
vector suite and a list of regression tests distilled from real bugs.
Read it before you implement. Port its *tests*, because they encode the
contracts, and reuse its theorem statements.

Do not copy its files or match its internal structure. We wrote the
spike fast, and §3 replaces its code shape:

- sessions built from mutable fields with a mutex per writer become the
  cores and loops of §3.3;
- `Option` results become the error channels of §3.5;
- shared readers become the leftover hand-over of §4.7;
- raw strings become `ProtocolId` and the closed sets of §3.4.

Port the tests, keep the bytes, and design the code from §3.

The build order, one `packages/<group>/<pkg>` per step:

| # | Package | Reference (files on the `spike` branch) | Public surface | Tests to carry over | Notes |
|---|---|---|---|---|---|
| 1 | `base/conc` | `Conc.lean` | `Chan` (new/send/recv/close/drain), `Pipe`, `TaskSet` (new/spawn/joinAll), `OnceRef` (new/get/set/update), `withinDeadline` | contracts: FIFO, close = broadcast EOF after drain, idempotent close, parked-recv wake, joinAll waits, N×M atomic updates, deadline wakes parked work via the close hook | build bounded `Chan`, `select`, and task error surfacing *here*; the gossipsub queues of §8 need them |
| 2 | `base/bytes` | `Crypto/Bytes.lean` | `Bytes.{ofNatList,toNatList,ofString,toString?,ofHex?,toHex,xorWith,...}` | byte-model round-trips, fuzz equivalence (from the multiaddr/proto suites) | the package exists for the proof-facing `List Nat` model; document why |
| 3 | `codec/varint` | `Net/Varint.lean` | `encode(B)`, `decode?`, `decodeB?` + theorems | RFC examples, non-minimal/too-long rejection tests | over-long varint = protocol error, here at the source |
| 4 | `codec/proto` | `Crypto/Pb.lean` | `Fields`, `encodeFields(B)`, `decodeFields(B?)`, `get{Varint,Bytes,Sub,Str}?` (last-wins), `getAll*`, `hasField` | round-trip theorem, message-vector suite (field tables stay in libp2p) | deterministic encoding by construction |
| 5 | `codec/multiformats` | `Crypto/{Multihash,Multibase,Base58,Cid}.lean`, `Net/Multiaddr.lean` | as named, plus `Multiaddr.parse?/toString/toByteArray/ofByteArray?`, operations API | RFC/multiformats vector suites + go/js CSVs + fuzz corpora + proved round-trips | the strictness rules carry over (leading `/`, no empty segments, percent = UTF-8 bytes) |
| 6 | `crypto/pure` | `Crypto/{Sha256,Sha512,Sha1,Hmac,Hkdf}.lean` | digests, HMAC, HKDF | RFC vector suites + cross-checks against the production path | cross-checked against the production path at the IO edge |
| 7 | `crypto/backend` | `Crypto/OpenSsl.lean`, `c/p2pcrypto.c` | Ed25519/X25519/RSA sign+verify, SHA-1/SHA-512/HMAC/HKDF, ChaCha20-Poly1305 seal/open, X.509 helpers, randomness and key generation, plus the interim fallback bindings (SHA-256, secp256k1, ECDSA P-256) and the pins for LeanHazmatSecp256k1/P256/Sha256/Keccak with the v4.34 build checks; every `ByteArray` argument **borrowed** (`@&`) | fixture suites + verifier-strictness regressions (key type, RSA 2048-8192, low-S, X.509 validity + critical exts) | key *marshalings* go to `libp2p/identity` (§4.6); secp256k1, P-256, SHA-256, and keccak-256 route to the etheorem hazmat packages (§4.6) |
| 8 | `net/streams` | `Net/{Transport,Tcp}.lean`, `Conn/{Reader,Frame,Stream}.lean`, `Sim.lean` | `Connection`/`Listener`/`Transport`, `readExactly`, `BufReader`, `Framing`, `Stream` (+`prependBytes`), sim harness | TCP suite (dial/listen, mss over TCP, noise over TCP, muxers over TCP), silent-peer teardown | contracts: libuv close-wakes discipline; failed write = teardown; no reader strand (each stage hands its leftover on as data, §4.7) |
| 9 | `net/yamux` | `Conn/Yamux.lean` | header codec, session, muxer entry | yamux suite + hostile-frame regressions + interop prereqs | depends only on `Connection` from `net/streams`; caps, window enforcement, SYN-only creation, stream retirement, and wake hand-off carry over as contracts |
| 10 | `libp2p/*` | everything else in the spike (`Host.lean`, `Conn/{Upgrade,Security,Noise,TlsExt,Mplex}.lean`, `Crypto/{Keys,PeerId,Messages}.lean`, `Protocol/*`, `Peer/*`) | see §4.9 | node suite + noise suite + keys suite + interop prereqs | build order inside: identity → core → security/noise ∥ mux (yamux) → negotiate → host → protocols; mplex last (deferred for consensus, §8) |
| 11 | `cli/` | `Main.lean`, `PingNode.lean`, `Interop.lean`, `scripts/` | node binaries + harness | end-to-end demo + interop matrix | `VECTORS.lock`, `scripts/extract-vectors.py`, and `Tests/vectors/` arrive earlier, in PLAN.md W0.3 |

The *Public surface* column names the entry points of the spike, so
that the reader can find the reference. The package document fixes the
final names, shaped by §3. A `Codec` instance replaces an
`encode`/`decode?` pair. A `step` replaces the methods of a session. A
seam value replaces a bundle of IO closures.

**Definition of done per package.** The contracts of §4 hold, the
carried vector suites pass, and the dependency lint (the group chain of
§2) is green. Copy the test runner layout of the spike as it is: one
suite module per upstream file, `lake test`, and a required `-N1` pass.

## 8. Component priority: Ethereum consensus layer

The implementation targets a beacon-node (consensus-layer) client
first. This classification decides the build order. "Defer" means: the
interface seams exist, and no implementation work is scheduled.

**Required by consensus (build in this order):**

| Component | Why | Status in spike |
|---|---|---|
| TCP transport | consensus networking runs on TCP (and QUIC) | done |
| Noise XX (`/noise`) | the only security protocol in the eth2 networking spec | done |
| yamux | the required muxer over TCP (the spec removed mplex; QUIC muxes internally) | done, hardened |
| multistream-select | negotiation for security + muxer | done |
| multiformats (multiaddr/varint/peer-id multihash, base58/base32) | dialing, ENR ↔ multiaddr, peer ids | done |
| keys + peer id, **Ed25519** (+ secp256k1 host keys) | host identity; clients use Ed25519/secp256k1 | done (Ed25519 and secp256k1) |
| identify (+ identify-push) | peer metadata; gossipsub peer scoring | done (push is trivial) |
| protobuf codec + key/identify messages | identify, ENR, host keys | done |
| **req/resp framework** (`/eth2/.../ssz_sn`) | Status, BlocksByRange/ByRoot, BlobSidecarsByRange/ByRoot, Metadata, Ping, Goodbye; SSZ with **snappy** framing over libp2p streams | **new work** (snappy is a new dependency, bound FFI first per the §4 dependency strategy; SSZ encoding is pure Lean) |
| **gossipsub v1.1** | blocks, aggregates, slashings, exits, blob sidecars | **new work** (the largest component) |
| host/upgrade/peerstore, dedup, deadlines | everything above composes through them | done (TTLs/limits deferred) |
| ENR ↔ multiaddr/peer-id mapping | discovery integration (discv5 sits outside libp2p and outside this scope) | multiaddr side done; ENR codec new (simple RLP) |

**Optional (the spec allows them; build them when cheap):**

- QUIC transport. Many clients enable it, and it is the natural second
  transport. WebTransport may follow it.
- libp2p `/ipfs/ping/1.0.0` as a keepalive. It is cheap, and some
  clients use it. The consensus keepalive itself is the eth2 req/resp
  Ping.
- The CIDv1 (`bafz...`) text form of peer ids, for compatibility. The
  spike already built it.
- Hole punching (DCUtR, AUTONAT) and circuit relay. Some clients
  support them as experiments, and consensus works without them.

**Not needed for consensus (defer, keep the seams only):**

- **TLS 1.3 security and the X.509 libp2p extension.** The eth2 spec
  names Noise only. The spike work is done, and no more work is
  planned.
- **mplex.** The eth2 networking spec removed it.
- **RSA and ECDSA P-256 host keys.** Consensus clients use Ed25519 or
  secp256k1. RSA comes from the go-libp2p defaults, and the eth2 spec
  does not use it.
- **Peer records and signed envelopes (RFC 0002, RFC 0003).** Consensus
  does not use them. The spike work is done.
- **kad-dht, peer routing, content routing.** Consensus has no DHT.
- **rendezvous, fetch, mDNS.** discv5 does the discovery.
- **WebSockets, WebRTC, pnet (private networks), libp2p-HTTP.**
  Consensus networking does not use them.
- **Unix and memory multiaddr transports.** The multiformats table
  already has them, and libp2p needs no work for them.

For the build order, the critical path after the spike is
**req/resp + snappy → gossipsub v1.1 → ENR codec**. The `conc`
additions (bounded channels, `select`) come first, because the
gossipsub queues need them. Everything in the "not needed" list stays a
seam in the existing interfaces (`SecurityProtocol`, `Muxer`,
`Transport`, policy hooks). A later unit can fill each seam with no
change to the design.

## 9. Deltas: spike → implementation

The spike records these known gaps, and the implementation must close
them:

1. Bounded channels and back-pressure in `base/conc` (§7, step 1).
   Build them there, as part of the first package.
2. A keepalive or identity probe, so that the host notices dead
   sessions without waiting for a write failure or TCP EOF. Dedup needs
   this to retire sessions promptly.
3. Peerstore limits and TTLs. Address dedup is already done.
4. The connection gater and resource manager seams, filled with limits
   per peer and per connection: stream count, buffered bytes, and a
   memory ceiling.
5. A select primitive that replaces the polling deadline inside
   `withinDeadline`. The observable behavior stays the same.
6. QUIC transport. It comes after the consensus-critical protocols and
   before anything else in the optional list of §8.
7. The TCP transport binds `Std.Async.TCP` (public in v4.34, over the
   libuv of the toolchain) inside `net/streams` only. A second
   transport or a toolchain API change then touches one module.
8. Sessions as pure cores with one loop task each (§3.3). The spike
   sessions hold their state in mutable fields and serialize writers
   with a mutex. The implementation keeps none of that shape.
9. Typed errors (§3.5). The spike returns `Option` from every IO entry
   point and cannot tell EOF from failure. Here every package owns an
   error inductive.
10. Seam types in `libp2p/core` (§3.1). The spike defines each seam
    next to its first implementation, so its upgrader imports Noise and
    yamux. Here the upgrader imports `core` only.

## 10. Reference map (spike module → package)

The map shows where the content of each spike module goes in the
`packages/` tree (§2).

| Spike module | Package |
|---|---|
| `Conc.lean` | `base/conc` |
| `Crypto/Bytes.lean` | `base/bytes` |
| `Net/Varint.lean` | `codec/varint` |
| `Crypto/{Multihash,Multibase,Base58,Cid}.lean`, `Net/Multiaddr.lean` | `codec/multiformats` |
| `Crypto/Pb.lean` | `codec/proto` |
| `Crypto/{Sha256,Sha512,Sha1,Hmac,Hkdf}.lean` | `crypto/pure` |
| `Crypto/OpenSsl.lean`, `c/p2pcrypto.c` | `crypto/backend` (key forms → `libp2p/identity`) |
| `Net/{Transport,Tcp}.lean`, `Conn/{Reader,Frame,Stream}.lean` | `net/streams` |
| `Sim.lean` | `net/streams` test support (in-memory transport) |
| `Conn/Yamux.lean` | `net/yamux` |
| `Crypto/{Keys,PeerId}.lean` | `libp2p/identity` |
| `Conn/Security.lean` (the seam shape), `Conn/Upgrade.lean` (`MuxHandle`, `MuxChoice` shapes) | `libp2p/core` (as `SecurityProtocol`, `Muxer`, `MuxSession`) |
| `Conn/Noise.lean`, `Conn/TlsExt.lean` | `libp2p/security` (TlsExt deferred, §8) |
| `Protocol/Multiselect.lean`, `Conn/Upgrade.lean` | `libp2p/negotiate` |
| `Conn/Mplex.lean` | `libp2p/mux` |
| `Host.lean`, `Peer/Peerstore.lean` | `libp2p/host` |
| `Protocol/{Identify,Ping}.lean`, `Crypto/Messages.lean` | `libp2p/protocols` (the envelope and record tables of `Messages` are deferred, §8) |
| `Main.lean`, `PingNode.lean`, `Interop.lean` | `cli/` |
