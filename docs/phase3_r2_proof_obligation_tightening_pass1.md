# Phase 3: R2 Proof-Obligation Tightening Pass 1

This document records the first tightening pass for the R2 self-adjoint restriction proof-obligation surface.

## Source state

```text
R1 proof-obligation tightening closure: CI green
R2 proof-obligation tightening segment selection: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Tightening pass 1 scope

This pass separates the R2 restriction route surface into:

```text
reducing-subspace obligation
full-Hamiltonian self-adjoint target obligation
restriction-domain obligation
restriction-operator obligation
restriction-self-adjoint theorem target obligation
OperatorAPI bridge obligation
Mathlib request boundary
status compatibility boundary
public-boundary obligation
```

## Non-claim boundary

This pass does not claim R2 theorem completion.

It does not reopen or change R1 closure.

It does not unlock final gap theorem release or Mathlib adoption on main.
