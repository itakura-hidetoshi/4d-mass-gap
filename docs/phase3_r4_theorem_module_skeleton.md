# Phase 3: R4 Theorem-Module Skeleton

This document records the first pre-Mathlib theorem-module skeleton for the R4 lower-bound layer.

## Target modules

```text
MGAP4D/R4/Concrete/LowerBoundProofObligationMap.lean
MGAP4D/R4/Theorem/LowerBoundSkeleton.lean
```

## Purpose

The proof-obligation map identifies which R4 obligations must eventually become concrete theorem modules. This skeleton creates a theorem-facing module that consumes the map without importing Mathlib yet.

## Skeleton obligations

```text
R2 bridge theorem target
ledger theorem target
constant theorem target
lower-bound theorem target
operator bridge theorem target
estimate theorem target
Mathlib request linkage
status compatibility
public boundary
```

## Current status

This remains pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create an R4 theorem root that imports the lower-bound skeleton and future R4 theorem modules.
