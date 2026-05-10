# Phase 3: R3 Theorem Surface

This step adds theorem-surface modules for the R3 layer.

R3 receives the R2 excited-Hamiltonian surface and the R4 lower-bound surface, then records the shifted-operator route and zero-form route that later feed R7.

## Added Lean modules

```text
MGAP4D/R3/TheoremSurface.lean
MGAP4D/R3/TheoremSurface/ShiftedSurface.lean
MGAP4D/R3/TheoremSurface/ZeroFormSurface.lean
MGAP4D/R3/TheoremSurface/ExportSurface.lean
```

## Scope

This is a minimal Lean step. It does not introduce Mathlib. It provides Prop-level surfaces for later theorem-level concrete modules.

## Next step

After CI is green, tighten `MGAP4D/R3/Concrete/ExportStatus.lean` against the new R3 surface.
