# Phase 3: R2 Theorem Surface

This step adds theorem-surface modules for the R2 layer.

R2 receives the R1 projection/export surface and records the route through reducing subspace, self-adjoint restriction, excited Hamiltonian, spectrum union, and exports to R3/R4/R5.

## Added Lean modules

```text
MGAP4D/R2/TheoremSurface.lean
MGAP4D/R2/TheoremSurface/ReducingSurface.lean
MGAP4D/R2/TheoremSurface/RestrictionSurface.lean
MGAP4D/R2/TheoremSurface/ExcitedHamiltonianSurface.lean
MGAP4D/R2/TheoremSurface/SpectrumSurface.lean
MGAP4D/R2/TheoremSurface/ExportSurface.lean
```

## Scope

This is a minimal Lean step. It does not introduce Mathlib. It provides Prop-level surfaces for later theorem-level concrete modules.

## Next step

After CI is green, tighten `MGAP4D/R2/Concrete/ExportStatus.lean` against the new R2 surface.
