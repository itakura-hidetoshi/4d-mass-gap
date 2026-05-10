# Phase 3: R5 Theorem Surface

This step adds theorem-surface modules for the R5 layer.

R5 records the spectrum-set route: excited spectrum, total spectrum surface, spectral bottom surface, and exports to R6 and Global.

## Added Lean modules

```text
MGAP4D/R5/TheoremSurface.lean
MGAP4D/R5/TheoremSurface/SpectrumSetSurface.lean
MGAP4D/R5/TheoremSurface/InfimumSurface.lean
MGAP4D/R5/TheoremSurface/ExportSurface.lean
```

## Scope

This remains a minimal Lean step. It does not add Mathlib and does not claim final spectral-theoretic closure.

## Next step

After CI is green, tighten `MGAP4D/R5/Concrete/ExportStatus.lean` against the new R5 surface.
