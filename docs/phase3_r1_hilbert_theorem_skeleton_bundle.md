# Phase 3: R1 Hilbert Theorem Skeleton Bundle

This step connects the R1 Concrete Hilbert candidate bundle to the R1 Theorem Hilbert skeleton.

## Target modules

```text
MGAP4D/R1/Concrete/HilbertCandidateBundle.lean
MGAP4D/R1/Theorem/HilbertSkeleton.lean
MGAP4D/R1/Theorem/HilbertSkeletonBundle.lean
```

## Purpose

The Concrete layer records the pre-Mathlib candidate and status-preservation side. The Theorem layer records the theorem-facing skeleton obligations.

This bundle connects both sides before introducing Mathlib.

## Scope

This does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, prepare an R1 Hilbert theorem milestone checkpoint and then decide whether the first scoped Mathlib adoption should be attempted.
