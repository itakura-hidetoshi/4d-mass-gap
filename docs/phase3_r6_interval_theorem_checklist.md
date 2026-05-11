# Phase 3: R6 Interval Theorem Checklist

This document records the pre-Mathlib checklist for the R6 interval-exclusion theorem candidate.

## Target modules

```text
MGAP4D/R6/Concrete/IntervalTheoremCandidate.lean
MGAP4D/R6/Concrete/IntervalCandidateBundle.lean
MGAP4D/R6/Concrete/IntervalTheoremChecklist.lean
```

## Purpose

Before introducing Mathlib or replacing the Prop-level scaffold, the R6 layer must record which concrete theorem obligations will need mathematical infrastructure.

## Checklist items

The first checklist contains these obligations:

```text
R5 spectrum side identified
vacuum side identified
excited side identified
interval boundary identified
interval exclusion target identified
R6 scoped Mathlib request recorded
status surfaces preserved
public boundary held
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create a pre-Mathlib proof-obligation map for R6 so each checklist item can point to a future theorem module.
