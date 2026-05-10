# Phase 3: R7 Exact Replacement Pass 1

This step applies the first status-to-theorem replacement checkpoint to the R7 exact-gap layer.

## Target

```text
MGAP4D/R7/Concrete/ExactGapStatus.lean
```

## Goal

R7 exact-gap status already connects status readiness to the R7 theorem surface. This pass connects that readiness to the general replacement checkpoint:

```text
MGAP4D.ReplacementCheckpoint
```

## Scope

This pass does not remove the status surface. It preserves the existing status record and adds a replacement-ready wrapper.

## Next step

After CI is green, proceed to Global/Concrete summary replacement pass 1.
