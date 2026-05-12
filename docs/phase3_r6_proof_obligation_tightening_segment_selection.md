# Phase 3: R6 Proof-Obligation Tightening Segment Selection

This document records the selection of the next proof-obligation tightening segment after R5 proof-obligation tightening closure.

## Source state

```text
R5 proof-obligation tightening closure: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Selected segment

```text
Segment: R6 interval-exclusion proof-obligation tightening
Reason: R6 is the next route after R5 in the R3--R7 theorem-route queue.
Scope: interval-exclusion obligation visibility and dependency-boundary tightening only.
```

## Non-claim boundary

This selection does not claim that the R6 interval-exclusion theorem is complete.

It does not unlock R7 theorem completion, final gap theorem release, or Mathlib adoption on main.

## Next action

Create a Lean-side R6 proof-obligation tightening segment selection checkpoint and wire it through the R6 theorem root and top-level root.
