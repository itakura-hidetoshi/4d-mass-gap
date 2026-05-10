# Phase 3: R6 Export Status Tightening

This step connects `MGAP4D/R6/Concrete/ExportStatus.lean` to the R6 theorem-surface layer.

## Goal

R6 export should depend on both the status fields and the R6 theorem-surface chain:

```text
GapIntervalSurface
ExportSurface
```

## Scope

This remains a minimal Lean step. It does not add Mathlib and does not claim final spectral-interval closure.

## Next step

After CI is green, start the R7 theorem-surface layer.
