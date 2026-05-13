# Phase 3: R2 Proof-Obligation Tightening Pass 2

This document records the second tightening pass for the R2 self-adjoint restriction proof-obligation surface.

## Source state

```text
R2 proof-obligation tightening segment selection: CI green
R2 proof-obligation tightening pass 1: CI green
R1 proof-obligation tightening closure: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Tightening pass 2 scope

This pass binds the R2 restriction surface split from pass 1 to three existing layers:

```text
R2 restriction theorem checklist
R2 restriction proof-obligation map
R2 restriction theorem skeleton
```

## Required three-layer links

```text
reducing subspace: checklist -> obligation map -> theorem skeleton
full Hamiltonian self-adjoint target: checklist -> obligation map -> theorem skeleton
restriction domain: checklist -> obligation map -> theorem skeleton
restriction operator: checklist -> obligation map -> theorem skeleton
restriction self-adjoint target: checklist -> obligation map -> theorem skeleton
OperatorAPI bridge: checklist -> obligation map -> theorem skeleton
Mathlib request boundary: checklist -> obligation map -> theorem skeleton
status compatibility boundary: checklist -> obligation map -> theorem skeleton
public-boundary: checklist -> obligation map -> theorem skeleton
```

## Non-claim boundary

This pass does not claim R2 theorem completion.

It does not reopen or change R1 closure.

It does not unlock final gap theorem release or Mathlib adoption on main.
