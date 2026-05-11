# Phase 3: R2 Restriction Theorem Milestone Checkpoint

This checkpoint records the current R2 self-adjoint restriction theorem-facing milestone.

## Completed R2 restriction path

```text
SelfAdjointRestrictionStatus
  -> RestrictionTheoremCandidate
  -> RestrictionCandidateBundle
  -> RestrictionTheoremChecklist
  -> RestrictionProofObligationMap
  -> R2/Theorem/RestrictionSkeleton
  -> R2/Theorem/RestrictionSkeletonBundle
```

## Purpose

The R2 restriction layer now has a pre-Mathlib theorem-facing path that connects the Concrete status/candidate side to the Theorem skeleton side.

## Still deferred

This checkpoint does not:

- import Mathlib;
- modify `lakefile.lean`;
- replace Prop-level status surfaces with analytic operator proofs;
- claim self-adjoint restriction theorem completion;
- expand public theorem claims beyond review gates.

## Current invariant

The relevant Mathlib request remains scoped:

```text
MGAP4D.MathlibAdoptionGate.r2RestrictionRequest
```

The R2 restriction milestone may advance to actual Mathlib adoption only through a future dry-run/review path.

## Added Lean module

```text
MGAP4D/R2/Theorem/RestrictionMilestone.lean
```

## Next step

After CI is green, continue theorem-candidate preparation for R4 lower-bound or add a dry-run request plan for R2 only after R2 review gates are recorded.
