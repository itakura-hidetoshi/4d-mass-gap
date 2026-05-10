# Phase 3: Final Assembly and Global/Concrete Connection

This step connects `MGAP4D/Global/FinalAssembly.lean` to the Global/Concrete summary surface.

## Goal

The final assembly should be able to depend on:

```text
GlobalInputLedger
Global.TheoremSurface
Global.Concrete.SummarySurface
PublicClaimBoundary
```

## Scope

This remains a minimal Lean step. It does not add Mathlib and does not assert external review completion.

## Next step

After CI is green, add a project-level Phase 3 checkpoint document and update the roadmap.
