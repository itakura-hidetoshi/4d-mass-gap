# Phase 3: R2 Proof-Obligation Tightening Segment Selection

This document records the selection of the R2 self-adjoint restriction proof-obligation tightening segment after the R1 Hilbert proof-obligation tightening closure was observed green through CI.

## Source state

```text
R1 proof-obligation tightening closure: CI green
R1/R2 proof-obligation tightening bridge: CI green
R2 theorem candidate / checklist / proof-obligation map / skeleton / bundle / milestone exist
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Selected segment

```text
Segment: R2 self-adjoint restriction proof-obligation tightening
Reason: R2 is the foundational restriction route following R1 Hilbert closure.
Scope: restriction route obligation visibility and dependency-boundary tightening only.
```

## Non-claim boundary

This selection does not claim R2 theorem completion.

It does not reopen or change R1 closure.

It does not unlock final gap theorem release or Mathlib adoption on main.

## Next action

Create a Lean-side R2 proof-obligation tightening segment selection checkpoint and wire it through the R2 theorem root.
