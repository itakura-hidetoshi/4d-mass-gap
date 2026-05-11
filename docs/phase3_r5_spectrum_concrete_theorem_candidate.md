# Phase 3: R5 Spectrum / Infimum Concrete Theorem Candidate

This document records the pre-Mathlib theorem candidate for the R5 spectrum / infimum layer.

## Candidate layer

```text
MGAP4D/R5/Concrete/SpectrumTheoremCandidate.lean
```

## Current status

This is still a pre-Mathlib candidate. It does not import Mathlib and does not change `lakefile.lean`.

## Purpose

The candidate records theorem-facing obligations for the R5 spectrum / infimum scaffold:

- spectrum set readiness;
- spectral bottom target;
- membership witness target;
- comparison surface target;
- proof binding still deferred;
- scoped R5 Mathlib request recorded;
- status surfaces preserved.

## Future Mathlib request

The relevant request is:

```text
MGAP4D.MathlibAdoptionGate.r5SpectrumRequest
```

Candidate import group remains deferred:

```text
Set.Basic
Order.Bounds.Basic
ConditionallyCompleteLattice.Basic
Real.Basic
Topology.Basic
```

## Next step

After CI is green, add a candidate bundle that links this R5 spectrum theorem candidate to the R5/R6/R7 route pass 2 bundle.
