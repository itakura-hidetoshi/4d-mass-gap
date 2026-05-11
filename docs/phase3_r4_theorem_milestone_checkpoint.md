# Phase 3: R4 Theorem Milestone Checkpoint

This checkpoint records the current R4 lower-bound theorem-facing milestone.

## Completed R4 path

```text
LowerBoundReceiptStatus
  -> LowerBoundTheoremCandidate
  -> LowerBoundCandidateBundle
  -> LowerBoundTheoremChecklist
  -> LowerBoundProofObligationMap
  -> R4/Theorem/LowerBoundSkeleton
  -> R4/Theorem/LowerBoundSkeletonBundle
```

## Purpose

The R4 layer now has a pre-Mathlib theorem-facing path that connects the Concrete status/candidate side to the Theorem skeleton side.

## Still deferred

This checkpoint does not:

- import Mathlib;
- modify `lakefile.lean`;
- replace Prop-level status surfaces with analytic estimate proofs;
- claim lower-bound theorem completion;
- expand public theorem claims beyond review gates.

## Current invariant

The relevant Mathlib request remains scoped:

```text
MGAP4D.MathlibAdoptionGate.r4LowerBoundRequest
```

The R4 milestone may advance to actual Mathlib adoption only through a future dry-run/review path.

## Added Lean module

```text
MGAP4D/R4/Theorem/LowerBoundMilestone.lean
```

## Next step

After CI is green, continue theorem-candidate preparation for R5 spectrum / infimum.
