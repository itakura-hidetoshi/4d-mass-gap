# Phase 3: R4 Theorem Surface

This step adds theorem-surface modules for the R4 layer.

R4 records the lower-bound route: decomposition receipts, rational constant surface, bridge surface, and exports to R3 and R5.

## Added Lean modules

```text
MGAP4D/R4/TheoremSurface.lean
MGAP4D/R4/TheoremSurface/LowerBoundSurface.lean
MGAP4D/R4/TheoremSurface/BridgeSurface.lean
MGAP4D/R4/TheoremSurface/ExportSurface.lean
```

## Scope

This is still a minimal Lean step. It does not add Mathlib and does not claim final analytic estimate closure.

## Next step

After CI is green, tighten `MGAP4D/R4/Concrete/ExportStatus.lean` against the new R4 surface.
