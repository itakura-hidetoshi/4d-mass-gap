# Phase 3: R2 Self-Adjoint Restriction Concrete Theorem Candidate

This document records the pre-Mathlib theorem candidate for the R2 self-adjoint restriction layer.

## Candidate layer

```text
MGAP4D/R2/Concrete/RestrictionTheoremCandidate.lean
```

## Current status

This is still a pre-Mathlib candidate. It does not import Mathlib and does not change `lakefile.lean`.

## Purpose

The candidate records theorem-facing obligations for the R2 restriction scaffold:

- reducing subspace readiness;
- full Hamiltonian self-adjoint target;
- restriction domain target;
- restriction self-adjoint target;
- operator/API binding still deferred;
- scoped R2 Mathlib request recorded;
- status surfaces preserved.

## Future Mathlib request

The relevant request is:

```text
MGAP4D.MathlibAdoptionGate.r2RestrictionRequest
```

Candidate import group remains deferred:

```text
InnerProductSpace.Basic
NormedSpace.OperatorNorm
LinearAlgebra.LinearPMap
InnerProductSpace.Projection
```

## Next step

After CI is green, add a candidate bundle that links this R2 restriction theorem candidate to the R2/R4/R3 route pass 2 bundle.
