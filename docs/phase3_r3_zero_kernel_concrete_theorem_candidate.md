# Phase 3: R3 Zero-Kernel Concrete Theorem Candidate

This document records the pre-Mathlib theorem candidate for the R3 shifted-operator / zero-form-kernel layer.

## Candidate layer

```text
MGAP4D/R3/Concrete/ZeroKernelTheoremCandidate.lean
```

## Current status

This is still a pre-Mathlib candidate. It does not import Mathlib and does not change `lakefile.lean`.

## Purpose

The candidate records theorem-facing obligations for the R3 shifted-operator and zero-form-kernel scaffold:

- R2 excited Hamiltonian readiness;
- lower-bound input still deferred to R4;
- shifted operator target;
- nonnegative target;
- zero-form condition target;
- sqrt-kernel route target;
- domain bridge still deferred;
- export to R7 still deferred;
- scoped R3 Mathlib request recorded;
- status surfaces preserved.

## Future Mathlib request

The relevant request is:

```text
MGAP4D.MathlibAdoptionGate.r3ZeroKernelRequest
```

Candidate import group remains deferred:

```text
InnerProductSpace.Basic
Analysis.InnerProductSpace.Projection
LinearAlgebra.QuadraticForm
Order.Basic
Real.Basic
```

## Next step

After CI is green, add a candidate bundle that links this R3 zero-kernel theorem candidate to the R2/R4/R3 route pass 2 bundle.
