# Phase 3: R4 Theorem Checklist

This document records the pre-Mathlib checklist for the R4 theorem candidate.

## Target modules

```text
MGAP4D/R4/Concrete/LowerBoundTheoremCandidate.lean
MGAP4D/R4/Concrete/LowerBoundCandidateBundle.lean
MGAP4D/R4/Concrete/LowerBoundTheoremChecklist.lean
```

## Purpose

Before introducing Mathlib or replacing the Prop-level scaffold, the R4 layer must record which concrete theorem obligations will need mathematical infrastructure.

## Checklist items

The first checklist contains these obligations:

```text
R2 excited Hamiltonian target identified
decomposition ledger identified
rational constant identified
lower-bound theorem target identified
operator bridge target identified
analytic estimate target identified
R4 scoped Mathlib request recorded
status surfaces preserved
public boundary held
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create a pre-Mathlib proof-obligation map for R4 so each checklist item can point to a future theorem module.
