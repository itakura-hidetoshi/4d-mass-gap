# Phase 3: R2 Restriction Proof-Obligation Map

This document records the pre-Mathlib proof-obligation map for the R2 self-adjoint restriction theorem candidate.

## Target modules

```text
MGAP4D/R2/Concrete/RestrictionTheoremChecklist.lean
MGAP4D/R2/Concrete/RestrictionProofObligationMap.lean
```

## Purpose

The R2 restriction checklist identifies concrete theorem obligations. This map assigns each obligation to a future theorem-facing module or proof target.

## Obligations

```text
reducing subspace identified                 -> future ReducingSubspace theorem module
full Hamiltonian self-adjoint target         -> future FullHamiltonianSelfAdjoint theorem module
restriction domain identified                -> future RestrictionDomain theorem module
restriction operator target identified       -> future RestrictionOperator theorem module
restriction self-adjoint theorem target      -> future RestrictionSelfAdjoint theorem module
operator/API bridge target identified        -> future OperatorAPIBridge theorem module
R2 restriction scoped request recorded       -> MathlibAdoptionGate R2 request
status surfaces preserved                    -> R2 Concrete status compatibility
public boundary held                         -> Global public claim boundary
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create a first R2 restriction theorem-module skeleton that consumes this obligation map without importing Mathlib yet.
