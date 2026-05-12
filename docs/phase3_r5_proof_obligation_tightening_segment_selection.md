# Phase 3: R5 Proof-Obligation Tightening Segment Selection

This document records the selection of the next proof-obligation tightening segment after R4 proof-obligation tightening closure.

## Source state

```text
R4 proof-obligation tightening closure: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Selected segment

```text
Segment: R5 spectrum / infimum proof-obligation tightening
Reason: R5 is the next route after R4 in the R3--R7 theorem-route queue.
Scope: spectrum / infimum obligation visibility and dependency-boundary tightening only.
```

## Non-claim boundary

This selection does not claim that the R5 spectrum / infimum theorem is complete.

It does not unlock R6--R7 theorem completion, final gap theorem release, or Mathlib adoption on main.

## Next action

Create a Lean-side R5 proof-obligation tightening segment selection checkpoint and wire it through the R5 theorem root and top-level root.
