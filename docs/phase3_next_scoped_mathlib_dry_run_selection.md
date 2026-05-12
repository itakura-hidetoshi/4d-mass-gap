# Phase 3 Next Scoped Mathlib Dry-Run Selection

This note records the next scoped Mathlib dry-run candidate after the R1--R7 candidate closure and CI confirmation.

## Current state

```text
R1 dry-run: recorded
R1--R7 candidate closure: recorded
R3 omission: corrected
Phase3CIConfirmationClosure: recorded
Main: still pre-Mathlib
```

## Selection

The next scoped dry-run candidate is:

```text
R2 self-adjoint restriction path
```

## Reason

R2 is selected before R3 because R3's shifted / zero-form route depends on the R2 restriction surface and interacts with the R2/R4/R3 route bundle.

R3 remains important, but it should follow R2 and not bypass it.

## Branch name

```text
feature/mathlib-r2-restriction-dry-run
```

## Boundary

This selection does not add Mathlib to main and does not modify `lakefile.lean` on main.
