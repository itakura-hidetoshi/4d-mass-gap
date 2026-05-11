# Phase 3: R4 Proof-Obligation Map

This document records the pre-Mathlib proof-obligation map for the R4 theorem candidate.

## Target modules

```text
MGAP4D/R4/Concrete/LowerBoundTheoremChecklist.lean
MGAP4D/R4/Concrete/LowerBoundProofObligationMap.lean
```

## Purpose

The R4 checklist identifies concrete theorem obligations. This map assigns each obligation to a future theorem-facing module or proof target.

## Obligations

```text
R2 excited Hamiltonian target identified  -> future R2ExcitedHamiltonianBridge theorem module
decomposition ledger identified           -> future DecompositionLedger theorem module
rational constant identified              -> future RationalConstant theorem module
lower-bound theorem target identified     -> future LowerBound theorem module
operator bridge target identified         -> future OperatorBridge theorem module
analytic estimate target identified       -> future AnalyticEstimate theorem module
R4 scoped request recorded                -> MathlibAdoptionGate R4 request
status surfaces preserved                 -> R4 Concrete status compatibility
public boundary held                      -> Global public claim boundary
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create the R4 theorem-module skeleton that consumes this obligation map without importing Mathlib yet.
