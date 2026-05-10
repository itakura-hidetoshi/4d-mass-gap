# Phase 3: R6 Export Replacement Pass 1

This step applies the first status-to-theorem replacement checkpoint to the R6 export layer.

## Target

```text
MGAP4D/R6/Concrete/ExportStatus.lean
```

## Goal

R6 export already connects status readiness to the R6 theorem surface. This pass connects that readiness to the general replacement checkpoint:

```text
MGAP4D.ReplacementCheckpoint
```

## Scope

This pass does not remove the status surface. It preserves the existing status record and adds a replacement-ready wrapper.

## Next step

After CI is green, proceed to R7 exact replacement pass 1.
