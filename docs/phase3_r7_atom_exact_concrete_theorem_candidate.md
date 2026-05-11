# Phase 3: R7 Atom / Exact-Gap Concrete Theorem Candidate

This document records the pre-Mathlib theorem candidate for the R7 atom / exact-gap layer.

## Candidate layer

```text
MGAP4D/R7/Concrete/AtomExactTheoremCandidate.lean
```

## Current status

This is still a pre-Mathlib candidate. It does not import Mathlib and does not change `lakefile.lean`.

## Purpose

The candidate records theorem-facing obligations for the R7 atom / exact-gap scaffold:

- atom persistence readiness;
- eigenstate surface target;
- exact gap target;
- global export target;
- review gate active;
- scoped R7 Mathlib request recorded;
- status surfaces preserved.

## Future Mathlib request

The relevant request is:

```text
MGAP4D.MathlibAdoptionGate.r7AtomExactRequest
```

Candidate import group remains deferred:

```text
LinearAlgebra.Eigenspace.Basic
InnerProductSpace.Basic
Real.Basic
Set.Basic
Order.Basic
```

## Next step

After CI is green, add a candidate bundle that links this R7 atom / exact-gap theorem candidate to the R5/R6/R7 route pass 2 bundle.
