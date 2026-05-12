# Phase 3: R4 Lower-Bound Theorem-Route Hardening Pass

This document records the theorem-route hardening pass for R4 after the R3 hardening pass and R3--R7 theorem-route queue checkpoint.

## Current invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R4 closure-candidate checkpoint is CI green
R4 theorem completion is not claimed
```

## Purpose

This pass hardens the R4 lower-bound route by separating four surfaces:

```text
lower-bound route surface
lower-bound obligation surface
upstream dependency surface
downstream review-gate surface
```

## Pass requirements

```text
R4 closure candidate remains visible
R4 lower-bound obligations remain visible
R4 upstream dependency remains visible
R4 downstream dependency on R5--R7 remains review-gated
R4 route does not infer completion from Mathlib dry-run success
public theorem boundary remains held
```

## Non-claim boundary

This pass does not claim that the R4 lower-bound theorem is complete.

It only records that R4 has entered a route-hardening pass after the closure-candidate checkpoint.
