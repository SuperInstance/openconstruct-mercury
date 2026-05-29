# OpenConstruct Mercury Verification Suite

Formal verification of OpenConstruct's core invariants using Mercury — a logic/functional language with compile-time determinism checking and total function guarantees.

## Why Mercury?

Rust gives us memory safety and runtime performance. Mercury gives us **mathematical correctness**:

- **Total functions**: Every predicate declares its determinism. The compiler proves termination.
- **No runtime panics**: No `unwrap()`, no `undefined behavior`, no exceptions.
- **Constructive proofs**: Properties are proven by construction, not by testing.
- **Mode system**: Input/output modes are checked at compile time.

This is the formal methods layer. Rust handles the real-time sensor processing; Mercury proves the system can't enter invalid states.

## Modules

### `policy_verify.m` — Policy Consistency Checking
- Verifies policy sets have no conflicting allow/deny rules
- Detects shadowed and redundant policies
- Finds orphan wildcard denies
- Proves evaluation always terminates (deny-by-default)

### `cr_verify.m` — Conservation Ratio Correctness
- Proves CR is always in [0.0, 1.0]
- Proves CR of empty graph = 0.0
- Plato Room CR: verified tiles / total tiles
- Suggests next tile to verify (unverified with satisfied deps)
- Finds missing bridges (tiles blocking verification)

### `sense_typecheck.m` — Typed Sensory Pipelines
- Each sense has its own typed shadow format
- Vision shadows can't be fed to sonar processors (compile-time)
- Fused events are well-typed combinations
- Severity classification is type-safe

### `fleet_prove.m` — Fleet Topology Proofs
- Proves star topology (Jetson hub + ESP32 spokes)
- Proves mesh connectivity (all nodes reachable)
- Resource satisfaction (every task finds a capable node)
- ESP32-as-room conversion is correct by construction

### `openconstruct.m` — Verification Runner
- Runs all verification modules
- Reports results with proofs

## Building

```bash
mmc --make openconstruct
./openconstruct
```

## Architecture

```
┌─────────────────────────────────────────────────┐
│                OpenConstruct                     │
├────────────────────┬────────────────────────────┤
│   Runtime (Rust)   │   Verification (Mercury)   │
│   • Senses         │   • Policy proofs           │
│   • Fleet          │   • CR correctness          │
│   • Shell          │   • Type safety             │
│   • Mesh           │   • Topology proofs         │
│   • Fast paths     │   • Total functions         │
└────────────────────┴────────────────────────────┘
```

Rust is the engine. Mercury is the proof.

Part of the [SuperInstance OpenConstruct](https://github.com/SuperInstance/OpenConstruct) ecosystem.
