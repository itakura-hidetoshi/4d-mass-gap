# Phase 3: R6 Interval Proof-Obligation Map

This document records the pre-Mathlib proof-obligation map for the R6 interval-exclusion theorem candidate.

## Target modules

```text
MGAP4D/R6/Concrete/IntervalTheoremChecklist.lean
MGAP4D/R6/Concrete/IntervalProofObligationMap.lean
```

## Purpose

The R6 checklist identifies concrete theorem obligations. This map assigns each obligation to a future theorem-facing module or proof target.

## Obligations

```text
R5 spectrum side identified       -> future R5SpectrumBridge theorem module
vacuum side identified            -> future VacuumSide theorem module
excited side identified           -> future ExcitedSide theorem module
interval boundary identified      -> future IntervalBoundary theorem module
interval exclusion target         -> future IntervalExclusion theorem module
R6 scoped request recorded        -> MathlibAdoptionGate R6 request
status surfaces preserved         -> R6 Concrete status compatibility
public boundary held              -> Global public claim boundary
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create the R6 theorem-module skeleton that consumes this obligation map without importing Mathlib yet.
