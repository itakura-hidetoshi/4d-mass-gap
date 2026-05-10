# Phase 3: R5 Export Status Tightening

This step connects `MGAP4D/R5/Concrete/ExportStatus.lean` to the R5 theorem-surface layer.

## Goal

R5 export should depend on both the status fields and the R5 theorem-surface chain:

```text
SpectrumSetSurface
InfimumSurface
ExportSurface
```

## Scope

This remains a minimal Lean step. It does not add Mathlib and does not claim final spectral closure.

## Next step

After CI is green, start the R6 theorem-surface layer.
