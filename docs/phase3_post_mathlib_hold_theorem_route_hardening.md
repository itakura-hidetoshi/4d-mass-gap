# Phase 3: Post-Mathlib-Hold Theorem-Route Hardening

This document records the next proof-hardening step after the R1--R7 scoped Mathlib dry-run series and the `hold_main_adoption` decision.

## Status entering this checkpoint

```text
R1--R7 scoped Mathlib dry-run series: success
R1--R7 dry-run series review: complete
Mathlib main-adoption review gate: complete
Mathlib main-adoption decision: hold_main_adoption
main: pre-Mathlib
Mathlib on main: not introduced
```

## Purpose

The purpose of this checkpoint is to return from dependency-surface testing to theorem-route hardening.

The dry-run series established that the Mathlib contact surface is buildable on scoped branches. It did not close the theorem routes.

## Theorem routes still requiring hardening

```text
R3 shifted / zero-form route
R4 lower-bound route
R5 spectrum / infimum route
R6 interval-exclusion route
R7 atom / exact-gap route
```

## Hardening objective

The next hardening work should reduce the gap between status surfaces and theorem surfaces without changing the `main` dependency model.

The immediate objective is:

```text
preserve main pre-Mathlib
preserve theorem-route deferral visibility
preserve public theorem review boundary
create route-specific hardening checkpoints
avoid converting dry-run buildability into theorem completion
```

## Allowed next steps

```text
add R3--R7 theorem-route hardening checkpoints
add proof-obligation refinements
add theorem-surface linkage checks
add deferred-route closure candidates
continue local replay checks
prepare separate adoption proposal only if explicitly reviewed later
```

## Forbidden inference

```text
R1--R7 dry-run success => R3--R7 theorem routes are complete
R1--R7 dry-run success => Mathlib is allowed on main
R1--R7 dry-run success => public final theorem release is unlocked
```

## Current decision

```text
continue_theorem_route_hardening_while_main_remains_pre_mathlib
```
