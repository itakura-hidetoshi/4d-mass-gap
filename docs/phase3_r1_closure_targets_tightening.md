# Phase 3: R1 Closure Targets Tightening

This step connects `MGAP4D/R1/Concrete/ClosureTargetsStatus.lean` to the R1 theorem-surface layer.

## Goal

R1 closure should no longer be only a list of recorded targets. It should also be able to depend on the theorem-surface chain:

```text
HilbertSurface
ExcitedSurface
InnerFunctionalSurface
ProjectionSurface
ExportSurface
```

## Scope

This remains minimal Lean. It does not introduce Mathlib and does not claim final analytic closure.

## Next step

After CI is green, proceed to the R2 theorem-surface layer.
