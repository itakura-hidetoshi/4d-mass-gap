# Phase 3: R4 Candidate Bundle

This step connects the R4 theorem candidate to the R2/R4/R3 route pass 2 bundle.

## Target modules

```text
MGAP4D/R4/Concrete/LowerBoundTheoremCandidate.lean
MGAP4D/ReplacementPass2/R2R4R3RouteBundle.lean
MGAP4D/R4/Concrete/LowerBoundCandidateBundle.lean
```

## Purpose

The R4 theorem candidate records the pre-Mathlib estimate obligations. The route pass 2 bundle records the theorem-facing route readiness.

This candidate bundle connects both surfaces while preserving status records and deferring Mathlib.

## Scope

This does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, prepare the R4 theorem checklist.
