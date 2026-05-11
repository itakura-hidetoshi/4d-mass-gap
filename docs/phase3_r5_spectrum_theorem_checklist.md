# Phase 3: R5 Spectrum Theorem Checklist

This document records the pre-Mathlib checklist for the R5 spectrum / infimum theorem candidate.

## Target modules

```text
MGAP4D/R5/Concrete/SpectrumTheoremCandidate.lean
MGAP4D/R5/Concrete/SpectrumCandidateBundle.lean
MGAP4D/R5/Concrete/SpectrumTheoremChecklist.lean
```

## Purpose

Before introducing Mathlib or replacing the Prop-level scaffold, the R5 layer must record which concrete theorem obligations will need mathematical infrastructure.

## Checklist items

The first checklist contains these obligations:

```text
spectrum set identified
spectral bottom identified
membership witness identified
comparison surface identified
infimum theorem target identified
R5 scoped Mathlib request recorded
status surfaces preserved
public boundary held
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create a pre-Mathlib proof-obligation map for R5 so each checklist item can point to a future theorem module.
