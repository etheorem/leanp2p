# Security policy

leanp2p implements libp2p in Lean 4: the TCP transport, the Noise
handshake and transport, the yamux muxer, multistream-select, and the
peer identity. It binds OpenSSL and the etheorem hazmat packages for
its crypto primitives. A node that runs this code reads bytes from
peers before it authenticates them. A bug here can let a hostile peer
crash a node, exhaust its memory, or defeat its authentication. We take
security reports seriously.

## Supported versions

The project is pre-alpha and has no releases. We support only the head
of the `main` branch. Once we tag releases, this section will list the
release lines that receive security fixes.

## Reporting a vulnerability

**Do not file a public GitHub issue for a security bug.**

Use one of these channels:

1. **GitHub private vulnerability reporting** (preferred). Open the
   Security tab of the repository and choose "Report a vulnerability".
   Only the maintainers see the report.
2. **Email the maintainers directly** if the GitHub flow is not
   available to you. The public GitHub profiles of the maintainers give
   their contact details.

Include:

- a description of the issue and its impact;
- a minimal reproducer (a Lean snippet, a byte sequence that a peer can
  send, or a transcript) with the expected and the actual behavior, or
  a pointer to the affected files and lines;
- the commit SHA where you saw the issue;
- your view of the severity, and any constraints on the disclosure
  date.

## What's in scope

In scope:

- **Pre-authentication input**: any byte sequence from an
  unauthenticated peer that makes the node allocate past a cap, park a
  task forever, spin, or crash. ARCHITECTURE.md §5 lists the caps and
  the deadlines.
- **Authentication**: a Noise handshake that completes against the
  wrong peer id, a verifier that accepts a key or a signature against
  the rules of ARCHITECTURE.md §4.6, or an AEAD failure that the code
  does not treat as a protocol error.
- **Spec mismatches** in the wire codecs (varint, protobuf,
  multiformats, yamux, multistream-select, Noise) against the libp2p
  and multiformats specs or the captured go-libp2p vectors.
- **Muxer state**: an input that makes the muxer create, reuse, or leak
  streams against the rules of ARCHITECTURE.md §4.8.
- **Memory safety** in the C shims under `packages/crypto/backend/`:
  buffer overflows, use after free, leaked references.
- **Soundness** of the proofs: an axiom or a `sorry` accepted where it
  should not be, or a kernel bug that lets a false theorem typecheck.

Out of scope:

- Performance regressions. File a normal issue with the numbers.
- Usability issues, documentation gaps, missing features.
- Bugs in the libp2p or multiformats specs themselves. Report those to
  <https://github.com/libp2p/specs> or
  <https://github.com/multiformats/multiformats>.
- Bugs in the etheorem hazmat packages. Report those under the etheorem
  security policy.
- Bugs in upstream Lean, Lake, batteries, OpenSSL, or go-libp2p. Report
  those to the respective projects.

## Disclosure timeline

We aim to acknowledge a report within **5 business days**. For a
confirmed vulnerability, we aim to ship a fix within **30 days**, and
sooner for a high-severity issue. We agree a disclosure date with you,
so that downstream consumers can update before the details go public.

If you work on an Ethereum consensus client or a libp2p implementation
and want to escalate a finding directly, say so in the report.

## Recognition

The release notes credit each reporter, unless the reporter asks to
stay anonymous.
