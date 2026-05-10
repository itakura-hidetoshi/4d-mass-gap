# Phase 3: R3 Export Status Tightening

This step connects `MGAP4D/R3/Concrete/ExportStatus.lean` to the R3 theorem-surface layer.

## Goal

R3 export should depend on both the status fields and the theorem-surface chain:

```text
ShiftedSurface
KernelRouteSurface
ExportSurface
```

## Scope

This remains a minimal Lean step. It does not add Mathlib and does not claim final unbounded-operator closure.

## Next step

After CI is green, start the R4 theorem-surface layer.
