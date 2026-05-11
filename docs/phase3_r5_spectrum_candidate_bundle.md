# Phase 3: R5 Spectrum Candidate Bundle

This step connects the R5 spectrum / infimum theorem candidate to the R5/R6/R7 route pass 2 bundle.

## Target modules

```text
MGAP4D/R5/Concrete/SpectrumTheoremCandidate.lean
MGAP4D/ReplacementPass2/R5R6R7RouteBundle.lean
MGAP4D/R5/Concrete/SpectrumCandidateBundle.lean
```

## Purpose

The R5 spectrum theorem candidate records the pre-Mathlib spectrum / infimum obligations. The R5/R6/R7 route pass 2 bundle records the theorem-facing route readiness.

This candidate bundle connects both surfaces while still preserving status records and deferring Mathlib.

## Scope

This does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, prepare the R5 spectrum theorem checklist.
