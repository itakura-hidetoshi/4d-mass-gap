# Phase 3: R7 Proof-Obligation Tightening Segment Selection

This document records the selection of the next proof-obligation tightening segment after R6 proof-obligation tightening closure.

## Source state

```text
R6 proof-obligation tightening closure: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Selected segment

```text
Segment: R7 atom / exact-gap proof-obligation tightening
Reason: R7 is the next route after R6 in the R3--R7 theorem-route queue.
Scope: atom / exact-gap obligation visibility and dependency-boundary tightening only.
```

## Non-claim boundary

This selection does not claim that the R7 atom / exact-gap theorem is complete.

It does not unlock final gap theorem release or Mathlib adoption on main.

## Next action

Create a Lean-side R7 proof-obligation tightening segment selection checkpoint and wire it through the R7 theorem root and top-level root.
