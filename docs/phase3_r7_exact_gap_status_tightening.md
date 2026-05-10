# Phase 3: R7 Exact Gap Status Tightening

This step connects `MGAP4D/R7/Concrete/ExactGapStatus.lean` to the R7 theorem-surface layer.

## Goal

R7 exact-gap status should depend on both the status fields and the R7 theorem-surface chain:

```text
AtomSurface
ExactGapSurface
ExportSurface
```

## Scope

This remains a minimal Lean step. It does not add Mathlib and does not claim final point-spectrum closure.

## Next step

After CI is green, start the Global theorem-surface layer that consumes R6 and R7 surfaces.
