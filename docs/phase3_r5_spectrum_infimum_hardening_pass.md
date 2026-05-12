# Phase 3: R5 Spectrum / Infimum Theorem-Route Hardening Pass

This document records the theorem-route hardening pass for R5 after the R4 hardening pass and R3--R7 theorem-route queue checkpoint.

## Current invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R5 closure-candidate checkpoint is CI green
R5 theorem completion is not claimed
```

## Purpose

This pass hardens the R5 spectrum / infimum route by separating five surfaces:

```text
spectrum surface
infimum bridge surface
spectrum-to-infimum obligation surface
upstream R4 lower-bound surface
downstream R6--R7 review-gate surface
```

## Pass requirements

```text
R5 closure candidate remains visible
R5 spectrum / infimum obligations remain visible
R5 upstream dependency on R4 remains visible
R5 downstream dependency on R6--R7 remains review-gated
R5 route does not infer completion from Mathlib dry-run success
public theorem boundary remains held
```

## Non-claim boundary

This pass does not claim that the R5 spectrum / infimum theorem is complete.

It only records that R5 has entered a route-hardening pass after the closure-candidate checkpoint.
