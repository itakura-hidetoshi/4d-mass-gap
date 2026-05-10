# Phase 3: R1 Hilbert Proof-Obligation Map

This document records the pre-Mathlib proof-obligation map for the R1 Hilbert theorem candidate.

## Target modules

```text
MGAP4D/R1/Concrete/HilbertTheoremChecklist.lean
MGAP4D/R1/Concrete/HilbertProofObligationMap.lean
```

## Purpose

The R1 Hilbert checklist identifies the concrete theorem obligations. This map assigns each obligation to a future theorem-facing module or proof target.

## Obligations

```text
state space carrier identified       -> future StateSpace theorem module
inner product interface identified   -> future InnerProduct theorem module
vacuum vector interface identified   -> future VacuumVector theorem module
orthogonal complement target         -> future OrthogonalComplement theorem module
closed subspace target               -> future ClosedSubspace theorem module
projection/decomposition target      -> future ProjectionDecomposition theorem module
R1 Hilbert scoped request recorded   -> MathlibAdoptionGate R1 request
status surfaces preserved            -> R1 Concrete status compatibility
public boundary held                 -> Global public claim boundary
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create a first R1 Hilbert theorem-module skeleton that consumes this obligation map without importing Mathlib yet.
