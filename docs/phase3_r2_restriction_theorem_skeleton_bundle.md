# Phase 3: R2 Restriction Theorem Skeleton Bundle

This step connects the R2 Concrete restriction candidate bundle to the R2 Theorem restriction skeleton.

## Target modules

```text
MGAP4D/R2/Concrete/RestrictionCandidateBundle.lean
MGAP4D/R2/Theorem/RestrictionSkeleton.lean
MGAP4D/R2/Theorem/RestrictionSkeletonBundle.lean
```

## Purpose

The Concrete layer records the pre-Mathlib self-adjoint restriction candidate and status-preservation side. The Theorem layer records the theorem-facing skeleton obligations.

This bundle connects both sides before introducing Mathlib.

## Scope

This does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, prepare an R2 restriction theorem milestone checkpoint.
