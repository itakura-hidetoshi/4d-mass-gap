# Phase 3: R6 Interval Candidate Bundle

This step connects the R6 interval-exclusion theorem candidate to the R5/R6/R7 route pass 2 bundle.

## Target modules

```text
MGAP4D/R6/Concrete/IntervalTheoremCandidate.lean
MGAP4D/ReplacementPass2/R5R6R7RouteBundle.lean
MGAP4D/R6/Concrete/IntervalCandidateBundle.lean
```

## Purpose

The R6 interval theorem candidate records the pre-Mathlib interval-exclusion obligations. The R5/R6/R7 route pass 2 bundle records the theorem-facing route readiness.

This candidate bundle connects both surfaces while still preserving status records and deferring Mathlib.

## Scope

This does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, prepare the R6 interval theorem checklist.
