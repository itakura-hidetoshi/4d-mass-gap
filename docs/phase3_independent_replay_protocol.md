# Phase 3: Independent Replay Protocol

This document records the independent replay protocol checkpoint after the independent replay gate preparation was observed green through CI.

## Source state

```text
independent replay gate preparation: CI green
final theorem release gate preparation refresh: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Protocol meaning

This checkpoint turns replay preparation into an ordered independent replay protocol for the full R1--R7 route surface.

It is carried by the global Phase3ReleaseGate root and by the top-level MGAP4D root.

It does not claim theorem completion for R1, R2, R3, R4, R5, R6, or R7.

It does not unlock the final gap theorem release.

It does not introduce Mathlib on main.

## Global replay scope

```text
R1 replay surface included
R2 replay surface included
R3 replay surface included
R4 replay surface included
R5 replay surface included
R6 replay surface included
R7 replay surface included
R1--R7 replay surface included
protocol is global
Phase3ReleaseGate carries the protocol
top-level MGAP4D root carries the protocol
```

## Ordered replay protocol

```text
1. clean checkout the pinned commit
2. verify lean-toolchain is present and pinned
3. run python3 scripts/verify_manifest.py
4. run python3 scripts/audit_lean_forbidden_tokens.py
5. run python3 scripts/replay_summary.py
6. run lake update
7. run lake build
8. pin CI run ID, build job ID, and commit hash
9. record replay result without upgrading it to theorem completion
```

## Required replay surfaces

```text
clean checkout step fixed
manifest audit step fixed
forbidden-token audit step fixed
replay summary step fixed
lake update step fixed
lake build step fixed
CI log pin step fixed
commit hash pin step fixed
non-theorem-completion boundary fixed
external audit still required
```

## Non-release invariant

```text
final gap theorem release is not unlocked
public theorem boundary remains held
main remains pre-Mathlib
```

## Next action

Keep the Lean-side independent replay protocol as a global R1--R7 checkpoint routed through the global Phase3ReleaseGate root.
