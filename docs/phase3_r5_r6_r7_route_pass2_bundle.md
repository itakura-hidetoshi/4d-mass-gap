# Phase 3: R5/R6/R7 Route Pass 2 Bundle

This step adds the R5/R6/R7 route theorem-facing bundle for replacement pass 2.

## Target route

```text
R5 spectrum / infimum route
  -> R6 gap interval route
  -> R7 atom / exact-gap route
```

## Goal

Pass 1 connected each route exit to `ReplacementCheckpoint`.

Pass 2 bundles the route-level readiness across:

```text
MGAP4D/R5/Concrete/ExportStatus.lean
MGAP4D/R6/Concrete/ExportStatus.lean
MGAP4D/R7/Concrete/ExactGapStatus.lean
MGAP4D/R5/TheoremSurface.lean
MGAP4D/R6/TheoremSurface.lean
MGAP4D/R7/TheoremSurface.lean
MGAP4D/ReplacementPass2.lean
```

## Scope

This pass does not remove existing status surfaces. It does not add Mathlib. It prepares a theorem-facing route bundle that can later be strengthened by concrete theorem modules.

## Added Lean module

```text
MGAP4D/ReplacementPass2/R5R6R7RouteBundle.lean
```

## Next step

After CI is green, proceed to the Global/Concrete pass 2 bundle.
