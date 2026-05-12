# Phase 3: R3--R7 Route-Specific Hardening

This document records the route-specific hardening checkpoint after the Mathlib main-adoption hold decision.

## Current invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
R1--R7 scoped Mathlib dry-runs succeeded
main adoption decision remains hold_main_adoption
```

## Route-specific hardening targets

```text
R3 shifted / zero-form route: harden deferred route visibility
R4 lower-bound route: harden lower-bound obligation surface
R5 spectrum / infimum route: harden spectrum-to-infimum bridge surface
R6 interval-exclusion route: harden interval exclusion boundary surface
R7 atom / exact-gap route: harden atom and exact-value boundary surface
```

## Non-claim boundary

This checkpoint does not claim completion of R3--R7 theorem routes. It only records that each route now has an explicit hardening surface after the Mathlib hold decision.

## Next action

Create Lean-side route-specific hardening objects and wire them through the top-level root while preserving the pre-Mathlib invariant.
