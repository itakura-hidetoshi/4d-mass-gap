# Phase 3: R4 Proof-Obligation Tightening Segment Selection

This document records the selection of the next proof-obligation tightening segment after R3 proof-obligation tightening closure.

## Source state

```text
R3 proof-obligation tightening closure: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Selected segment

```text
Segment: R4 lower-bound proof-obligation tightening
Reason: R4 is the next route after R3 in the R3--R7 theorem-route queue.
Scope: lower-bound obligation visibility and dependency-boundary tightening only.
```

## Non-claim boundary

This selection does not claim that the R4 lower-bound theorem is complete.

It does not unlock R5--R7 theorem completion, final gap theorem release, or Mathlib adoption on main.

## Next action

Create a Lean-side R4 proof-obligation tightening segment selection checkpoint and wire it through the R4 theorem root and top-level root.
