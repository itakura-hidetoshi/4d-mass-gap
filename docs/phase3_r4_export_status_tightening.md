# Phase 3: R4 Export Status Tightening

This step connects `MGAP4D/R4/Concrete/ExportStatus.lean` to the R4 theorem-surface layer.

## Goal

R4 export should depend on both the status fields and the R4 theorem-surface chain:

```text
LowerBoundSurface
BridgeSurface
ExportSurface
```

## Scope

This remains a minimal Lean step. It does not add Mathlib and does not claim final analytic lower-bound closure.

## Next step

After CI is green, start the R5 theorem-surface layer.
