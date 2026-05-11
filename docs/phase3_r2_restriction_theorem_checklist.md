# Phase 3: R2 Restriction Theorem Checklist

This document records the pre-Mathlib checklist for the R2 self-adjoint restriction theorem candidate.

## Target modules

```text
MGAP4D/R2/Concrete/RestrictionTheoremCandidate.lean
MGAP4D/R2/Concrete/RestrictionCandidateBundle.lean
MGAP4D/R2/Concrete/RestrictionTheoremChecklist.lean
```

## Purpose

Before introducing Mathlib or replacing the Prop-level scaffold, the R2 restriction layer must record which concrete theorem obligations will need mathematical infrastructure.

## Checklist items

The first checklist contains these obligations:

```text
reducing subspace identified
full Hamiltonian self-adjoint target identified
restriction domain identified
restriction operator target identified
restriction self-adjoint theorem target identified
operator/API bridge target identified
R2 restriction scoped Mathlib request recorded
status surfaces preserved
public boundary held
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create a pre-Mathlib proof-obligation map for R2 restriction so each checklist item can point to a future theorem module.
