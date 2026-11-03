# leanp2p libp2p core: plan

This package implements root PLAN unit W5.2. Root ARCHITECTURE §3
and §4.9 govern its contracts.

## Units

| Unit | Dependencies | Deliverable | Status |
|---|---|---|---|
| 0 | None | Package architecture and plan | Written |
| 1 (W5.2) | W4.1, W5.1 | Core types, interfaces, and tests | Implemented against mocks; integration pending |

W5.2 can be reviewed with mocks under `RULES.md`. Merge requires both
blocking dependencies and integration with their real interfaces.
The package architecture lists the replacement steps.

## Consumers

| Unit | Consumer | Use of core |
|---|---|---|
| W5.3 | Security | Noise and fixed-key `SecurityProtocol` values |
| W5.4 | Mux | Yamux and test `Muxer` values; mplex is P2 |
| W5.5 | Negotiate | Upgrader over security and muxer interfaces |
| W5.6 | Host | Session and handler registries, policies, `Host.Error` |
| W5.7 | Protocols | Handler registration by `ProtocolId` |
| W5.8 | CLI | Configuration of implementation lists |

## Test milestones

`Tests/Libp2pCore.lean` checks:

- Required instances for `Role`, `ProtocolId`, and error types.
- Construction of security, muxer, handler, and policy values.
- Construction, rendering, and mapping of all four error variants.
- Registry lookup using independently constructed equal ids.
- Toy session shutdown: pending accept ends, join completes, opening
  after close fails, and repeated close is harmless.
- Per-connection stream limits, slot release, and idempotent release.
- Address-ranker permutation, length, and membership properties.

Examples requiring dependency values take them as parameters because
the mocks expose no constructors. Sim-based assembly awaits W4.1
integration. W5.3 and W5.4 must compile their production and test values
against this interface. The toy accept test permits either scheduling
order; it does not establish that accept parked before close.

Required checks:

```sh
lake build
lake test
lake test -- +RTS -N1 -RTS
scripts/lint-imports.sh
```

Core defines no wire format. Protocol vectors and transcripts belong
to the security, mux, and negotiate suites.
