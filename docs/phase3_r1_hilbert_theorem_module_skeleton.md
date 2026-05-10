# Phase 3: R1 Hilbert Theorem-Module Skeleton

This document records the first pre-Mathlib theorem-module skeleton for the R1 Hilbert layer.

## Target modules

```text
MGAP4D/R1/Concrete/HilbertProofObligationMap.lean
MGAP4D/R1/Theorem/HilbertSkeleton.lean
```

## Purpose

The proof-obligation map identifies which R1 Hilbert obligations must eventually become concrete theorem modules. This skeleton creates a theorem-facing module that consumes the map without importing Mathlib yet.

## Skeleton obligations

```text
state-space theorem target
inner-product theorem target
vacuum-vector theorem target
orthogonal-complement theorem target
closed-subspace theorem target
projection/decomposition theorem target
Mathlib request linkage
status compatibility
public boundary
```

## Current status

This remains pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create an R1 theorem root that imports the Hilbert skeleton and future R1 theorem modules.
