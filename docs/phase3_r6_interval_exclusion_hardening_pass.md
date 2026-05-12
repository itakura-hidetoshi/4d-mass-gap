# Phase 3: R6 Interval-Exclusion Theorem-Route Hardening Pass

This document records the theorem-route hardening pass for R6 after the R5 hardening pass and R3--R7 theorem-route queue checkpoint.

## Current invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R6 closure-candidate checkpoint is CI green
R6 theorem completion is not claimed
```

## Purpose

This pass hardens the R6 interval-exclusion route by separating five surfaces:

```text
interval surface
exclusion boundary surface
interval-exclusion obligation surface
upstream R5 spectrum / infimum surface
downstream R7 atom / exact-gap review-gate surface
```

## Pass requirements

```text
R6 closure candidate remains visible
R6 interval-exclusion obligations remain visible
R6 upstream dependency on R5 remains visible
R6 downstream dependency on R7 remains review-gated
R6 route does not infer completion from Mathlib dry-run success
public theorem boundary remains held
```

## Non-claim boundary

This pass does not claim that the R6 interval-exclusion theorem is complete.

It only records that R6 has entered a route-hardening pass after the closure-candidate checkpoint.
