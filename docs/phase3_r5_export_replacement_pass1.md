# Phase 3: R5 Export Replacement Pass 1

This step applies the first status-to-theorem replacement checkpoint to the R5 export layer.

## Target

```text
MGAP4D/R5/Concrete/ExportStatus.lean
```

## Goal

R5 export already connects status readiness to the R5 theorem surface. This pass connects that readiness to the general replacement checkpoint:

```text
MGAP4D.ReplacementCheckpoint
```

## Scope

This pass does not remove the status surface. It preserves the existing status record and adds a replacement-ready wrapper.

## Next step

After CI is green, proceed to R6 export replacement pass 1.
