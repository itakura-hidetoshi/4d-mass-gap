# Phase 3: R1 Hilbert Concrete Theorem Candidate

This document records the first concrete theorem candidate that may eventually consume a scoped Mathlib request.

## Candidate layer

```text
MGAP4D/R1/Concrete/HilbertTheoremCandidate.lean
```

## Current status

This is still a pre-Mathlib candidate. It does not import Mathlib and does not change `lakefile.lean`.

## Purpose

The candidate records the theorem-facing obligations for the R1 Hilbert scaffold:

- a state-space layer exists;
- an inner-product layer exists;
- a vacuum vector layer exists;
- an orthogonal-complement layer is planned;
- a future Mathlib binding is scoped through the R1 Hilbert request;
- status surfaces remain preserved.

## Future Mathlib request

The relevant request is:

```text
MGAP4D.MathlibAdoptionGate.r1HilbertRequest
```

Candidate import group remains deferred:

```text
InnerProductSpace.Basic
InnerProductSpace.Projection
Topology.Algebra.Module.Basic
```

## Next step

After CI is green, add a candidate bundle that links this R1 Hilbert theorem candidate to the R1 closure pass 2 bundle.
