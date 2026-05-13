# Phase 3: R2 Proof-Obligation Tightening Closure

This document records the closure checkpoint after the R2 restriction proof-obligation tightening series review was observed green through CI.

## Source state

```text
R2 proof-obligation tightening pass 1: CI green
R2 proof-obligation tightening pass 2: CI green
R2 proof-obligation tightening pass 3: CI green
R2 proof-obligation tightening series review: CI green
R1 proof-obligation tightening closure: CI green
```

## Closure meaning

This checkpoint closes the R2 self-adjoint restriction proof-obligation tightening sequence at the review-surface level.

It does not close the R2 theorem route.

It does not claim R2 theorem completion.

It does not reopen or change R1 closure.

It does not unlock the final gap theorem release.

## Closed surfaces

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
R1 closure preservation surface
final release non-inference surface
checklist -> proof-obligation map -> theorem skeleton links
```

## Invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
public theorem boundary remains held
```
