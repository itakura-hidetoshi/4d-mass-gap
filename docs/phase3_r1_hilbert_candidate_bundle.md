# Phase 3: R1 Hilbert Candidate Bundle

This step connects the R1 Hilbert theorem candidate to the R1 closure pass 2 bundle.

## Target modules

```text
MGAP4D/R1/Concrete/HilbertTheoremCandidate.lean
MGAP4D/R1/Concrete/Pass2Bundle.lean
```

## Goal

The R1 Hilbert theorem candidate records the pre-Mathlib Hilbert scaffold obligations. The R1 closure pass 2 bundle records the theorem-facing R1 closure route.

This candidate bundle connects both surfaces while still preserving status records and deferring Mathlib.

## Added Lean module

```text
MGAP4D/R1/Concrete/HilbertCandidateBundle.lean
```

## Scope

This does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, prepare the first concrete theorem-candidate checklist for R1 Hilbert obligations.
