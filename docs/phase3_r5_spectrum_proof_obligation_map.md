# Phase 3: R5 Spectrum Proof-Obligation Map

This document records the pre-Mathlib proof-obligation map for the R5 spectrum / infimum theorem candidate.

## Target modules

```text
MGAP4D/R5/Concrete/SpectrumTheoremChecklist.lean
MGAP4D/R5/Concrete/SpectrumProofObligationMap.lean
```

## Purpose

The R5 checklist identifies concrete theorem obligations. This map assigns each obligation to a future theorem-facing module or proof target.

## Obligations

```text
spectrum set identified          -> future SpectrumSet theorem module
spectral bottom identified       -> future SpectralBottom theorem module
membership witness identified    -> future MembershipWitness theorem module
comparison surface identified    -> future ComparisonSurface theorem module
infimum theorem target identified -> future Infimum theorem module
R5 scoped request recorded       -> MathlibAdoptionGate R5 request
status surfaces preserved        -> R5 Concrete status compatibility
public boundary held             -> Global public claim boundary
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create the R5 theorem-module skeleton that consumes this obligation map without importing Mathlib yet.
