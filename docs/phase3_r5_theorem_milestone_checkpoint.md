# Phase 3: R5 Theorem Milestone Checkpoint

This checkpoint records the current R5 spectrum / infimum theorem-facing milestone.

## Completed R5 path

```text
SpectrumSetStatus / InfimumStatus
  -> SpectrumTheoremCandidate
  -> SpectrumCandidateBundle
  -> SpectrumTheoremChecklist
  -> SpectrumProofObligationMap
  -> R5/Theorem/SpectrumSkeleton
  -> R5/Theorem/SpectrumSkeletonBundle
```

## Purpose

The R5 layer now has a pre-Mathlib theorem-facing path that connects the Concrete status/candidate side to the Theorem skeleton side.

## Still deferred

This checkpoint does not:

- import Mathlib;
- modify `lakefile.lean`;
- replace Prop-level status surfaces with set/order/topology proofs;
- claim spectrum / infimum theorem completion;
- expand public theorem claims beyond review gates.

## Current invariant

The relevant Mathlib request remains scoped:

```text
MGAP4D.MathlibAdoptionGate.r5SpectrumRequest
```

The R5 milestone may advance to actual Mathlib adoption only through a future dry-run/review path.

## Added Lean module

```text
MGAP4D/R5/Theorem/SpectrumMilestone.lean
```

## Next step

After CI is green, continue theorem-candidate preparation for R6 interval exclusion.
