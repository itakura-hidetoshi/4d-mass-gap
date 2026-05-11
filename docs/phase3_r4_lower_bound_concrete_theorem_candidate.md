# Phase 3: R4 Lower-Bound Concrete Theorem Candidate

This document records the pre-Mathlib theorem candidate for the R4 lower-bound layer.

## Candidate layer

```text
MGAP4D/R4/Concrete/LowerBoundTheoremCandidate.lean
```

## Current status

This is still a pre-Mathlib candidate. It does not import Mathlib and does not change `lakefile.lean`.

## Purpose

The candidate records theorem-facing obligations for the R4 lower-bound scaffold:

- R2 excited Hamiltonian readiness;
- decomposition ledger readiness;
- rational constant target;
- lower-bound theorem target;
- analytic estimates still deferred;
- scoped R4 Mathlib request recorded;
- status surfaces preserved.

## Future Mathlib request

The relevant request is:

```text
MGAP4D.MathlibAdoptionGate.r4LowerBoundRequest
```

Candidate import group remains deferred:

```text
Rat.Basic
Real.Basic
Order.Basic
InnerProductSpace.Basic
NormedSpace.Basic
```

## Next step

After CI is green, add a candidate bundle that links this R4 lower-bound theorem candidate to the R2/R4/R3 route pass 2 bundle.
