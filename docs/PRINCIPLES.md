# leanp2p: engineering principles

`CLAUDE.md` states the rules. `ARCHITECTURE.md` owns the contracts. This
document explains the discipline behind both: what each principle means
in practice, and which incident earned it. Most incidents come from the
spike; the rest come from the review that followed it. When you judge an
edge case, judge it here first, then check the contracts.

Three kinds of rules appear below. **Rules of code** shape every file.
**Rules of protocol** shape how we treat the wire and the peer. **Rules
of process** shape how we verify and how we review. The division is
soft; a rule often pays in more than one place.

---

## 1. Rules of code

### 1.1 Literate by default

Write every module for a reader who knows one side of the project and
must learn the other. A libp2p spec section and a Lean idiom deserve the
same courtesy: a module docstring that names the spec section, a
declaration docstring that gives the why, and a one-line comment at each
non-obvious inference.

Inferences need this as much as idioms. Lean infers types, instances,
and motives; most of it is unremarkable. Some of it decides what the
code means: a coercion that forces defeq reduction, a match that relies
on an unfolded constructor, an instance chosen through a phantom tag.
When a reader must reconstruct the inference to follow the code, name
it. When the code reads cleanly without help, leave it alone.

The cost is paid once at write time. The reader pays the alternative
forever.

### 1.2 Single responsibility

One thing per file, per namespace, per definition. The spike's muxer
sessions once grew frame parsing, flow control, timers, and teardown in
one module; every fix became harder to place, and the review found bugs
in exactly the seams nobody owned. Split when a definition stops reading
top to bottom. A 1000-line module is a 1000-line function at a different
scale.

Practice: name the responsibility in the module docstring. If the
docstring needs the word "and" twice, split the module.

### 1.3 Open/Closed: extend through seams

A new transport, security protocol, or muxer lands as a new value of an
existing seam: `Transport`, `SecurityProtocol`, `MuxChoice`. The
upgrader never learns their names. When adding one requires editing the
dispatcher, the seam is wrong; fix the seam before adding the feature.

The spike kept these as structure values, and the payoff was concrete:
mplex and yamux swapped freely in every test, and the go interop matrix
ran the same node code under both. Typeclass seams serve the same
purpose where dispatch is static; structure values where it is dynamic.
Choose by how the choice is made at runtime, and keep the choice out of
the feature code.

### 1.4 Dependency inversion: code against seams, test against the sim

Protocol logic sees `Connection` and `Stream`, never a socket. A test
for a protocol runs over the in-memory sim transport; only the transport
suite touches real TCP. This is why the spike could step a yamux session
frame by frame, feed it a byte-splitting hostile transport, and replay a
go transcript, all without a network.

Practice: every seam consumer takes the seam as a parameter. Every seam
has a second implementation (the sim) that tests can use. A seam with
one implementation and one consumer is a seam in name only; that is
acceptable at the bottom of the graph, and a smell anywhere else.

### 1.5 One canonical home per fact

A frame layout is defined once, in the proved codec. The IO shell
imports it. Protocol constants (length caps, window sizes, timeouts,
protocol ids) live in one module and are imported everywhere. The spike
paid for this lesson more than once: the Noise write path re-derived its
chunk size from `maxMessage` instead of importing the constant, and the
two drifted until the review caught the mismatch.

Practice: when you reach for a constant and it is absent, add it to the
constants module first, then use it. When two copies already exist,
delete one and make the other importable. A fact with two homes has no
home.

### 1.6 No hidden coupling

`set_option` and `open` at file scope leak into every importer. Keep
them tight to the section that needs them. Do not rely on import order
for correctness; Lean gives you no error when the order stops working,
only a different elaboration.

The spike lost a day to a per-chunk stream cipher that re-keyed at
offset 0 for every read. The sim preserved write boundaries, so the bug
hid; TCP coalesced a yamux header with its payload, and the keystream
desynced. The coupling was real but invisible until a second transport
arrived. Coupling that a second implementation would expose is coupling
all the same; write the second implementation early (the sim exists for
exactly this).

### 1.7 Lean on Lean

The language gives you `deriving`, `simp` lemmas, `Decidable` +
`decide` for finite goals, structural recursion, and `termination_by`.
Use them before hand-rolling. Reach for `batteries` before writing a
list utility. Keep `mathlib` out; nothing here needs it, and its compile
cost is real.

Hand-rolled equivalents carry a second cost beyond the lines: readers
must verify them. Every line you delete from the trusted base is a line
nobody re-audits.

### 1.8 Strict checking

`set_option autoImplicit false` per file. No `sorry` in committed code
without a `TODO` and a tracking note. Unused variables and linter
warnings are build failures in spirit, even before CI enforces them.

The spike's review found seventeen `!` indexes and thirty `partial`
defs, and could check every one quickly because each said why it was
safe. That is the standard: strictness makes review cheap. A missed
implicit, a widened type, or a silenced linter moves the cost from the
author to every future reader.

### 1.9 Stringly-typed is a smell

Protocol ids, multicodecs, and flag kinds get named constants or
inductives in one module. If behavior decides by comparing raw strings
or magic numbers, promote them. The yamux flag bits (`SYN`, `ACK`,
`FIN`, `RST`) and the frame types are the model: named once, imported
everywhere, and the header codec proves the encoding.

A scattered literal has a failure mode worse than ugliness: two sites
can disagree, and the peer sees the disagreement as a protocol error.

---

## 2. Rules of protocol

### 2.1 The spec is the source of truth

Behavior comes from the libp2p specs, the multiformats specs, and the
captured vectors. When our code disagrees with the spec, the spec wins
and we record the discrepancy. When two upstream implementations
disagree with each other, the chosen side becomes a documented decision.

The spike keeps a decision record for exactly these cases: the peer-id
print form (Go prints base58, js prints CIDv1; we store the parsed form
and print it back), the percent codecs, the garlic padding rules. Each
entry names the two sides and the rule we picked. A future implementer
who hits the same fork reads the decision instead of re-deriving it.

Practice: a disagreement found in review is fixed or recorded the same
day. "We match go" is a hypothesis; "we match go, and the vector at
line N proves it" is a fact.

### 2.2 Half-close fidelity

Close ends the closer's write direction. The other direction keeps
working, and the spec says so in one sentence per muxer. The spike got
this wrong twice in mplex: a local close also killed local reads, and a
peer close silenced local writes. The e2e test asserted the wrong
behavior and passed for weeks.

Two lessons compound here. First, close semantics are one sentence in
the spec; implement the sentence, then write the test that would fail
if the sentence were violated. Second, a test that asserts the wrong
behavior hides the bug better than no test. When you fix a spec
violation, rewrite the test to assert the spec, and add the case the
old test missed (the response that arrives after our FIN).

### 2.3 Bounded inputs

Every length-prefixed read is capped before allocation. An over-long
varint is a protocol error, never "need more bytes". Flow control is
enforced on the sender, and a frame for an unknown stream invents no
state.

The review found the full failure set in one pass: yamux read a
declared length of up to 4 GiB into memory; the receive window went
unenforced; a Noise handshake payload of 64 KiB cost about 1.5 seconds
of CPU in a quadratic pre-authentication decoder; and a hostile varint
made two readers accumulate until EOF. Every one of these converts a
peer's length field into our resource commitment. The cap converts it
into a bounded, checkable cost.

Practice: at every `readExactly`-style call, the length argument comes
from a named constant or from a window we granted. A declared length
beyond the cap is a protocol error and closes the connection. The
multiaddr and mplex decoders show the pattern: a length that cannot
complete within its budget is `.bad`, and `.bad` tears the session
down.

### 2.4 Verify before trust

Anything decoded before the peer is authenticated is size-capped, and
its failure closes the connection. Authentication failure is distinct
from EOF at every layer: the Noise read path returns `none` for both
only after it has torn the connection down, so a downstream layer can
treat EOF as an orderly event.

Verification is strict at the boundary: a verifier accepts only the key
type it claims (an EC key never verifies under the RSA entry point),
only key sizes in the libp2p range (RSA 2048 to 8192 bits), only
low-S secp256k1 signatures, and certificates that are valid now and
carry no unknown critical extensions. Each of these rules closes an
accept-set divergence from go-libp2p, and each is one line of C. The
cheapness is the point: boundary checks are the cheapest security there
is, and the easiest to skip.

---

## 3. Rules of concurrency

### 3.1 Never cancel; wake by close

The runtime's cancellation drops the promise a task is parked on. A
cancelled task's waiter never wakes. So we never cancel; we close what
the task parks on, and the close wakes it.

Every park in the stack has a named close that reaches it: a TCP read
parks on a promise that `Connection.close` resolves; a yamux writer
parks on a credit channel that the stream reset closes; an accept loop
parks on a queue that the listener close closes; an upgrade parks on a
connection that the host close closes. The deadline machinery
(`withinDeadline`) follows the same rule from the other side: on expiry
it closes the connection, and the parked read ends on its own.

The silent-peer incident earned this rule. A raw TCP client that sent
nothing parked the upgrade responder forever, and `Host.close` joined
tasks, so shutdown hung. The fix added no cancellation; it added a
close that reaches the park, plus a deadline as the backstop.

Practice: when you add a park, name the close that wakes it, in a
comment, at the park. If you cannot name it, the park is a hang.

### 3.2 Every task has an owner that joins it

Lean's RTS waits for tasks at process exit. A spawned task with no
owner is a process that cannot exit. `TaskSet` makes ownership explicit:
one set per subsystem, spawned tasks tracked, the owner joins them on
close in a fixed order (listeners, then pending connections, then
sessions, then session pumps, then host tasks).

Ownership is also the review lens for shutdown: for every task, name
the close that ends it and the join that waits for it. The spike's
"mplex EOF teardown" note records the failure mode; the old pump marked
the session dead and left the pipes open, which hid until reads started
blocking.

### 3.3 Shared state changes atomically

Get-then-set on a bare `IO.Ref` loses updates under concurrency. The
peerstore lost addresses this way; the dedup table raced between a
probe and a commit. `OnceRef.update` makes the read-modify-write one
step, and the update function returns the decision, so probe and commit
share one critical section.

Practice: a comment that says "racy but fine" is a bug with a shrug.
Either the operation is atomic, or the code names the interleaving that
makes it safe and shows why the interleaving cannot happen. The dedup
logic does this: the entry that changed underneath the probe triggers a
full re-evaluation, bounded by retries.

### 3.4 Bounded queues, with wake hand-off

Unbounded queues convert a peer's send rate into our memory. The yamux
control queue is capped, and beyond the cap the frames dropped are
exactly the ones a peer can re-derive or re-request. Stream pipes stay
bounded by the receive window we granted, which is why the window is
enforced on inbound data and replenished only when credit returns.

The parked-writer stall teaches the subtler half: when a WindowUpdate
wakes one writer of several, and that writer uses only part of the
credit, the rest of the credit must be handed to the next parked
writer. A wake token that stops at the first waiter is a lost wakeup.
Count the parked writers, send tokens only while someone waits, and
hand the token on when credit remains.

---

## 4. Rules of dependency

### 4.1 FFI first, Lean later

A primitive with a mature native implementation gets a C shim behind a
Lean interface. A pure-Lean implementation follows only where it pays,
behind the same interface. Callers depend on the interface, never on
the FFI.

The strategy has a hard edge, learned in review: every `ByteArray`
argument to the shim is borrowed (`@&`). The bindings declared them
owned while the shim treated them as borrowed, so every Noise frame
leaked its key, nonce, plaintext, and ciphertext. Two hundred thousand
SHA-256 calls grew RSS from 14 MB to 526 MB; after the fix, 9.5 MB.
The lesson generalizes: the FFI boundary is a contract in both
directions, and the memory discipline is part of the contract. Write
the ownership down at the binding, and keep the shim small enough to
audit in one sitting.

### 4.2 Configure, don't integrate

Package metadata stays declarative (`lakefile.toml`). `lakefile.lean`
is permitted only for targets the declarative form cannot express, and
the C shim build is the standing example. A build step that feels like
shell script glued onto Lake goes into Lake's API or a Lean script run
through `lake env lean`.

### 4.3 The layering carries the guarantees

The group chain `cli → libp2p → net → crypto → codec → base` is
enforced by lint, and the lower layers never mention libp2p. This is
what makes the lower libraries usable by other projects, and what keeps
each contract auditable in one file. The per-package docs refine the
root docs and never contradict them; a contract change starts at the
root.

---

## 5. Rules of verification

### 5.1 The right proof for the right layer

The verified cores (varint, protobuf, framing, the yamux header) carry
theorems over the `List Nat` byte model, closed by `rfl`, `simp`, or
`omega`. The production `ByteArray` decoders are pinned to those models
by fuzz property tests, so the proof view and the wire view cannot
drift. FFI results are checked through the vector suites; the kernel stays
out of it.

A theorem about an FFI return value is almost always in the wrong
place. Pick the tool by the layer: proofs where the thing is pure,
property tests where it must match the model, vectors where it must
match the world.

### 5.2 Tests are contracts

The mplex half-close bug survived because its test asserted the wrong
behavior. A green suite proves the code matches the tests; only the
spec proves the tests match the protocol. When a review finds a
violated contract, the fix has two parts: the code, and the test
rewritten to assert the contract, plus the case the old test missed.

### 5.3 `-N1` is the starvation criterion

The full suite passes under `+RTS -N1`. A single capability leaves no
room for timing luck: anything that spins starves, anything that polls
starves, and only blocking-with-wake survives. Every concurrency rule
in §3 is policed by this one setting.

### 5.4 Regressions are permanent

Each hardening rule keeps its test for the life of the project: the
silent peer that once hung the shutdown, the hostile yamux frames that
once invented streams, the parked writer that once slept through a
credit grant, the over-long varint that once looped. These tests are
the contract record in executable form. Deleting one needs the same
justification as deleting the rule.

---

## 6. When the rules conflict

Order of authority, from the top: the specs, then `docs/ARCHITECTURE.md`
(substance), then this file and `CLAUDE.md` (form and discipline), then
the per-package docs. A conflict between a rule and a spec is a spec
compliance question, and the spec wins with the discrepancy recorded. A
conflict between two rules of this document is a judgment call; make it
on the principle behind the rules, and write down what you chose.

Clarity outranks every rule of style. Orwell's own exemption applies
here: break a rule when following it would obscure, and say why in one
line.

---

## 7. How the discipline is enforced

Mechanically: the import lint (§4.3), the vector suites, the fuzz
equivalence checks, the `-N1` run, and CI. In review: everything else.
The reviewer's checklist is short, and every line traces to a section
above:

- Does every park have a named close? (§3.1)
- Does every length-prefixed read have a cap? (§2.3)
- Is the new constant in its canonical home? (§1.5)
- Does the test assert the spec or the implementation? (§5.2)
- Are the FFI ownership annotations written? (§4.1)
- Does the new module teach the spec section it implements? (§1.1)

"Build failure in spirit" is the operating rule: a violation blocks a
merge even when no checker does, and fixing it is part of the change,
never a follow-up.
