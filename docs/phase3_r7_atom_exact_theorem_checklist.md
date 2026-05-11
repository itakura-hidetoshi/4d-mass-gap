# Phase 3: R7 Atom / Exact Theorem Checklist

This document records the pre-Mathlib checklist for the R7 atom / exact-gap theorem candidate.

## Target modules

```text
MGAP4D/R7/Concrete/AtomExactTheoremCandidate.lean
MGAP4D/R7/Concrete/AtomExactCandidateBundle.lean
MGAP4D/R7/Concrete/AtomExactTheoremChecklist.lean
```

## Purpose

Before introducing Mathlib or replacing the Prop-level scaffold, the R7 layer must record which concrete theorem obligations will need mathematical infrastructure.

## Checklist items

The first checklist contains these obligations:

```text
atom persistence identified
eigenstate surface identified
exact gap value identified
global export target identified
review gate identified
R7 scoped Mathlib request recorded
status surfaces preserved
public boundary held
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create a pre-Mathlib proof-obligation map for R7 so each checklist item can point to a future theorem module.
