# Phase 3: R2 Export Status Tightening

This step connects `MGAP4D/R2/Concrete/ExportStatus.lean` to the R2 theorem-surface layer.

## Goal

R2 export should depend not only on status fields, but also on the R2 theorem-surface chain:

```text
ReducingSurface
RestrictionSurface
ExcitedHamiltonianSurface
SpectrumSurface
ExportSurface
```

## Scope

This remains a minimal Lean step. It does not add Mathlib and does not claim final operator-theoretic closure.

## Next step

After CI is green, start the R3 theorem-surface layer.
