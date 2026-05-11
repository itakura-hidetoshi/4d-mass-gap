# Phase 3: R2 Restriction Candidate Bundle

This step connects the R2 self-adjoint restriction theorem candidate to the R2/R4/R3 route pass 2 bundle.

## Target modules

```text
MGAP4D/R2/Concrete/RestrictionTheoremCandidate.lean
MGAP4D/ReplacementPass2/R2R4R3RouteBundle.lean
MGAP4D/R2/Concrete/RestrictionCandidateBundle.lean
```

## Purpose

The R2 restriction theorem candidate records the pre-Mathlib self-adjoint restriction obligations. The R2/R4/R3 route pass 2 bundle records the theorem-facing route readiness.

This candidate bundle connects both surfaces while still preserving status records and deferring Mathlib.

## Scope

This does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, prepare the R2 restriction theorem checklist.
