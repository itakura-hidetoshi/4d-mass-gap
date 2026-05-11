# Phase 3: R3 Theorem Checklist

This document records the pre-Mathlib checklist for the R3 shifted-operator / zero-form route theorem candidate.

## Target modules

```text
MGAP4D/R3/Concrete/R3TheoremCandidate.lean
MGAP4D/R3/Concrete/R3CandidateBundle.lean
MGAP4D/R3/Concrete/R3TheoremChecklist.lean
```

## Purpose

Before introducing Mathlib or replacing the Prop-level scaffold, the R3 layer must record which concrete theorem obligations will need mathematical infrastructure.

## Checklist items

The first checklist contains these obligations:

```text
shifted operator identified
nonnegative target identified
zero-form condition identified
sqrt route identified
domain bridge deferred/export target identified
R3 scoped Mathlib request recorded
status surfaces preserved
public boundary held
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create a pre-Mathlib proof-obligation map for R3 so each checklist item can point to a future theorem module.
