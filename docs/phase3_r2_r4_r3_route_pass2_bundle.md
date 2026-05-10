# Phase 3: R2/R4/R3 Route Pass 2 Bundle

This step adds the R2/R4/R3 route theorem-facing bundle for replacement pass 2.

## Target route

```text
R2 export
  -> R4 lower-bound / bridge route
  -> R3 shifted / kernel route
```

## Goal

Pass 1 connected each route exit to `ReplacementCheckpoint`.

Pass 2 bundles the route-level readiness across:

```text
MGAP4D/R2/Concrete/ExportStatus.lean
MGAP4D/R4/Concrete/ExportStatus.lean
MGAP4D/R3/Concrete/ExportStatus.lean
MGAP4D/R2/TheoremSurface.lean
MGAP4D/R4/TheoremSurface.lean
MGAP4D/R3/TheoremSurface.lean
MGAP4D/ReplacementPass2.lean
```

## Scope

This pass does not remove existing status surfaces. It does not add Mathlib. It prepares a theorem-facing route bundle that can later be strengthened by concrete theorem modules.

## Added Lean module

```text
MGAP4D/ReplacementPass2/R2R4R3RouteBundle.lean
```

## Next step

After CI is green, proceed to the R5/R6/R7 route pass 2 bundle.
