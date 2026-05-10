# Phase 3: R1 Theorem Surface

This step adds theorem-surface modules for the R1 layer.

R1 is the input and projection layer. It records the path from Hilbert scaffold to excited subspace, inner functional, projection pair, and export to R2.

## Added Lean modules

```text
MGAP4D/R1/TheoremSurface.lean
MGAP4D/R1/TheoremSurface/HilbertSurface.lean
MGAP4D/R1/TheoremSurface/ExcitedSurface.lean
MGAP4D/R1/TheoremSurface/InnerFunctionalSurface.lean
MGAP4D/R1/TheoremSurface/ProjectionSurface.lean
MGAP4D/R1/TheoremSurface/ExportSurface.lean
```

## Scope

This is still a minimal Lean step. It does not introduce Mathlib. It provides Prop-level theorem surfaces that later concrete modules can inhabit.

## Next step

After CI is green, use these R1 theorem surfaces to tighten `MGAP4D/R1/Concrete/ClosureTargetsStatus.lean`, then proceed to R2 theorem surfaces.
