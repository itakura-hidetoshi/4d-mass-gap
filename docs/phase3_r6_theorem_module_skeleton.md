# Phase 3: R6 Theorem-Module Skeleton

This document records the first pre-Mathlib theorem-module skeleton for the R6 interval-exclusion layer.

## Target modules

```text
MGAP4D/R6/Concrete/IntervalProofObligationMap.lean
MGAP4D/R6/Theorem/IntervalSkeleton.lean
```

## Purpose

The proof-obligation map identifies which R6 obligations must eventually become concrete theorem modules. This skeleton creates a theorem-facing module that consumes the map without importing Mathlib yet.

## Skeleton obligations

```text
R5 bridge theorem target
vacuum-side theorem target
excited-side theorem target
interval-boundary theorem target
interval-exclusion theorem target
Mathlib request linkage
status compatibility
public boundary
```

## Current status

This remains pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create an R6 theorem root that imports the interval skeleton and future R6 theorem modules.
