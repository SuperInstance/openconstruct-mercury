# OpenConstruct Mercury — Formal Verification Suite

Prove OpenConstruct's core invariants using [Mercury](https://mercurylang.org/) — a logic/functional language with compile-time determinism checking and total function guarantees. Where Rust gives memory safety, Mercury gives mathematical correctness.

**Part of [SuperInstance OpenConstruct](https://github.com/SuperInstance/OpenConstruct).**

## What This Gives You

- **Policy consistency** — prove no conflicting allow/deny rules exist
- **Conservation ratio correctness** — prove CR ∈ [0.0, 1.0] for all graphs
- **Typed sensory pipelines** — compile-time enforcement: vision shadows can't reach sonar processors
- **Fleet topology proofs** — star topology, mesh connectivity, resource satisfaction
- **Total functions** — every predicate declares determinism; the compiler proves termination

## Quick Start

```bash
mmc --make openconstruct
./openconstruct
```

## Modules

| Module | What It Proves |
|--------|---------------|
| `policy_verify.m` | No conflicting policies, no shadowed rules, deny-by-default termination |
| `cr_verify.m` | CR ∈ [0, 1], empty graph → CR = 0, suggests next tile to verify |
| `sense_typecheck.m` | Vision ≠ sonar at compile time, fused events are well-typed |
| `fleet_prove.m` | Star topology, mesh connectivity, resource satisfaction |
| `openconstruct.m` | Verification runner — executes all proofs |

## How It Fits

Mercury is the formal methods layer. The [Rust SDK](https://github.com/SuperInstance/openconstruct-rust) handles runtime; Mercury proves the runtime can't enter invalid states. If Mercury says a property holds, no amount of runtime testing can violate it.

## License

MIT
