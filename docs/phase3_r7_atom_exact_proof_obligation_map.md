# Phase 3: R7 Atom / Exact Proof-Obligation Map

This document records the pre-Mathlib proof-obligation map for the R7 atom / exact-gap theorem candidate.

## Target modules

```text
MGAP4D/R7/Concrete/AtomExactTheoremChecklist.lean
MGAP4D/R7/Concrete/AtomExactProofObligationMap.lean
```

## Purpose

The R7 checklist identifies concrete theorem obligations. This map assigns each obligation to a future theorem-facing module or proof target.

## Obligations

```text
atom persistence identified       -> future AtomPersistence theorem module
eigenstate surface identified     -> future EigenstateSurface theorem module
exact gap value identified        -> future ExactGapValue theorem module
global export target identified   -> future GlobalExport theorem module
review gate identified            -> future ReviewGate theorem module
R7 scoped request recorded        -> MathlibAdoptionGate R7 request
status surfaces preserved         -> R7 Concrete status compatibility
public boundary held              -> Global public claim boundary
```

## Current status

This is still pre-Mathlib. It does not import Mathlib and does not modify `lakefile.lean`.

## Next step

After CI is green, create the R7 theorem-module skeleton that consumes this obligation map without importing Mathlib yet.
