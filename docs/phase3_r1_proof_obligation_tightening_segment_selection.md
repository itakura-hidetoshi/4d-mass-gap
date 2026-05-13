# Phase 3: R1 Proof-Obligation Tightening Segment Selection

This document records the selection of the R1 Hilbert proof-obligation tightening segment after the R1--R2 proof-obligation tightening bridge was observed green through CI.

## Source state

```text
R1--R2 proof-obligation tightening bridge: CI green
R1 theorem candidate / checklist / proof-obligation map / skeleton / bundle / milestone exist
R2 remains queued after R1
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Selected segment

```text
Segment: R1 Hilbert proof-obligation tightening
Reason: R1 is the foundational Hilbert route and should be reviewed before R2 restriction tightening.
Scope: Hilbert route obligation visibility and dependency-boundary tightening only.
```

## Non-claim boundary

This selection does not claim R1 theorem completion.

It does not claim R2 theorem completion.

It does not unlock final gap theorem release or Mathlib adoption on main.

## Next action

Create a Lean-side R1 proof-obligation tightening segment selection checkpoint and wire it through the R1 theorem root and existing top-level import path.
