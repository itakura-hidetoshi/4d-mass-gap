# Phase 3: R6 Interval-Exclusion Concrete Theorem Candidate

This document records the pre-Mathlib theorem candidate for the R6 interval-exclusion layer.

## Candidate layer

```text
MGAP4D/R6/Concrete/IntervalTheoremCandidate.lean
```

## Current status

This is still a pre-Mathlib candidate. It does not import Mathlib and does not change `lakefile.lean`.

## Purpose

The candidate records theorem-facing obligations for the R6 gap interval scaffold:

- R5 readiness;
- vacuum-side boundary;
- excited-side boundary;
- interval-exclusion target;
- proof binding still deferred;
- scoped R6 Mathlib request recorded;
- status surfaces preserved.

## Future Mathlib request

The relevant request is:

```text
MGAP4D.MathlibAdoptionGate.r6IntervalRequest
```

Candidate import group remains deferred:

```text
Real.Basic
Order.Interval.Set.Basic
Set.Basic
Order.Bounds.Basic
Topology.Basic
```

## Next step

After CI is green, add a candidate bundle that links this R6 interval theorem candidate to the R5/R6/R7 route pass 2 bundle.
