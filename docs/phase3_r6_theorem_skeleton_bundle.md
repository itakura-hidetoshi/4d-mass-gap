# Phase 3: R6 Theorem Skeleton Bundle

This step connects the R6 Concrete interval candidate bundle to the R6 Theorem interval skeleton.

## Target modules

```text
MGAP4D/R6/Concrete/IntervalCandidateBundle.lean
MGAP4D/R6/Theorem/IntervalSkeleton.lean
MGAP4D/R6/Theorem/IntervalSkeletonBundle.lean
```

## Purpose

The Concrete layer records the pre-Mathlib interval-exclusion candidate and status-preservation side. The Theorem layer records the theorem-facing skeleton obligations.

This bundle connects both sides before introducing Mathlib.

## Scope

This does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, prepare an R6 theorem milestone checkpoint.
