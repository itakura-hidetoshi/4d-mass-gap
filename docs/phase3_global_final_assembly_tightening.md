# Phase 3: Global Final Assembly Tightening

This step connects `MGAP4D/Global/FinalAssembly.lean` to the Global theorem-surface layer.

## Goal

The final assembly should depend not only on the original Global input ledger, but also on the Global theorem-surface chain:

```text
AssemblySurface
ReviewSurface
FinalSurface
```

## Scope

This remains a minimal Lean step. It does not add Mathlib and does not claim external review completion.

## Next step

After CI is green, add a theorem dependency map as checked Lean structures.
