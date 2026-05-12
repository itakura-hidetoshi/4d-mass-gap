# Phase 3: R3--R7 Theorem-Route Queue

This document records the next work queue after the R3--R7 closure-candidate series review.

## Source state

```text
R3 closure-candidate: CI green
R4 closure-candidate: CI green
R5 closure-candidate: CI green
R6 closure-candidate: CI green
R7 closure-candidate: CI green
R3--R7 closure-candidate series review: CI green
```

## Invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
closure-candidate does not mean theorem completion
public theorem boundary remains held
```

## Queue order

```text
1. R3 shifted / zero-form route
2. R4 lower-bound route
3. R5 spectrum / infimum route
4. R6 interval-exclusion route
5. R7 atom / exact-gap route
```

## Next action

Create a Lean-side queue checkpoint and wire it through the top-level root.
