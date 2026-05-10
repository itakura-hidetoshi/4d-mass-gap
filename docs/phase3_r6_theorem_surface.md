# Phase 3: R6 Theorem Surface

This step adds theorem-surface modules for the R6 layer.

R6 records the gap-interval route: it receives the R5 spectrum surface, records the interval-exclusion surface, and exports the result to Global.

## Added Lean modules

```text
MGAP4D/R6/TheoremSurface.lean
MGAP4D/R6/TheoremSurface/GapIntervalSurface.lean
MGAP4D/R6/TheoremSurface/ExportSurface.lean
```

## Scope

This remains a minimal Lean step. It does not add Mathlib and does not claim final spectral-interval closure.

## Next step

After CI is green, tighten `MGAP4D/R6/Concrete/ExportStatus.lean` against the new R6 surface.
