# Phase 3: R2 Restriction Theorem-Module Skeleton

This document records the first pre-Mathlib theorem-module skeleton for the R2 self-adjoint restriction layer.

## Target modules

```text
MGAP4D/R2/Concrete/RestrictionProofObligationMap.lean
MGAP4D/R2/Theorem/RestrictionSkeleton.lean
```

## Purpose

The proof-obligation map identifies which R2 restriction obligations must eventually become concrete theorem modules. This skeleton creates a theorem-facing module that consumes the map without importing Mathlib yet.

## Skeleton obligations

```text
reducing-subspace theorem target
full-Hamiltonian self-adjoint theorem target
restriction-domain theorem target
restriction-operator theorem target
restriction self-adjoint theorem target
operator/API bridge theorem target
Mathlib request linkage
status compatibility
public boundary
```

## Current status

This remains pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create an R2 theorem root that imports the restriction skeleton and future R2 theorem modules.
