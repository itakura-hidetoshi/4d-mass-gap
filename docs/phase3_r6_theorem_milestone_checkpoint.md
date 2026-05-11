# Phase 3: R6 Theorem Milestone Checkpoint

This checkpoint records the current R6 interval-exclusion theorem-facing milestone.

## Completed R6 path

```text
GapIntervalStatus
  -> IntervalTheoremCandidate
  -> IntervalCandidateBundle
  -> IntervalTheoremChecklist
  -> IntervalProofObligationMap
  -> R6/Theorem/IntervalSkeleton
  -> R6/Theorem/IntervalSkeletonBundle
```

## Purpose

The R6 layer now has a pre-Mathlib theorem-facing path that connects the Concrete status/candidate side to the Theorem skeleton side.

## Still deferred

This checkpoint does not:

- import Mathlib;
- modify `lakefile.lean`;
- replace Prop-level status surfaces with interval/order proofs;
- claim interval-exclusion theorem completion;
- expand public theorem claims beyond review gates.

## Current invariant

The relevant Mathlib request remains scoped:

```text
MGAP4D.MathlibAdoptionGate.r6IntervalRequest
```

The R6 milestone may advance to actual Mathlib adoption only through a future dry-run/review path.

## Added Lean module

```text
MGAP4D/R6/Theorem/IntervalMilestone.lean
```

## Next step

After CI is green, continue theorem-candidate preparation for R7 atom / exact-gap.
