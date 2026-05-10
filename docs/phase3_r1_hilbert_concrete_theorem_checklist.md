# Phase 3: R1 Hilbert Concrete Theorem Checklist

This document records the pre-Mathlib checklist for the R1 Hilbert concrete theorem candidate.

## Target modules

```text
MGAP4D/R1/Concrete/HilbertTheoremCandidate.lean
MGAP4D/R1/Concrete/HilbertCandidateBundle.lean
```

## Purpose

Before introducing Mathlib or replacing the Prop-level scaffold, the R1 Hilbert layer must record which concrete theorem obligations will need mathematical infrastructure.

## Checklist items

The first checklist contains these obligations:

```text
state space carrier identified
inner product interface identified
vacuum vector interface identified
orthogonal complement target identified
closed subspace target identified
projection/decomposition target identified
R1 Hilbert scoped Mathlib request recorded
status surfaces preserved
public boundary held
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create a pre-Mathlib proof-obligation map for R1 Hilbert so each checklist item can point to a future theorem module.
