# Phase 3: R7 Atom / Exact Candidate Bundle

This step connects the R7 atom / exact-gap theorem candidate to the R5/R6/R7 route pass 2 bundle.

## Target modules

```text
MGAP4D/R7/Concrete/AtomExactTheoremCandidate.lean
MGAP4D/ReplacementPass2/R5R6R7RouteBundle.lean
MGAP4D/R7/Concrete/AtomExactCandidateBundle.lean
```

## Purpose

The R7 atom / exact-gap theorem candidate records the pre-Mathlib exact-gap obligations. The R5/R6/R7 route pass 2 bundle records the theorem-facing route readiness.

This candidate bundle connects both surfaces while still preserving status records and deferring Mathlib.

## Scope

This does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, prepare the R7 atom / exact theorem checklist.
