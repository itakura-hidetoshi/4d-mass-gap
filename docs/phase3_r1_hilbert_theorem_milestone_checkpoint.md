# Phase 3: R1 Hilbert Theorem Milestone Checkpoint

This checkpoint records the current R1 Hilbert theorem-facing milestone.

## Completed R1 Hilbert path

```text
HilbertScaffoldStatus
  -> HilbertTheoremCandidate
  -> HilbertCandidateBundle
  -> HilbertTheoremChecklist
  -> HilbertProofObligationMap
  -> R1/Theorem/HilbertSkeleton
  -> R1/Theorem/HilbertSkeletonBundle
```

## Purpose

The R1 Hilbert layer now has a pre-Mathlib theorem-facing path that connects the Concrete status/candidate side to the Theorem skeleton side.

## Still deferred

This checkpoint does not:

- import Mathlib;
- modify `lakefile.lean`;
- replace Prop-level status surfaces;
- claim analytic Hilbert-space theorem completion;
- expand public theorem claims beyond review gates.

## Current invariant

The relevant Mathlib request remains scoped:

```text
MGAP4D.MathlibAdoptionGate.r1HilbertRequest
```

The R1 Hilbert milestone may advance to actual Mathlib adoption only through:

```text
MGAP4D.MathlibAdoptionGate.MathlibGate.ready
```

## Added Lean module

```text
MGAP4D/R1/Theorem/HilbertMilestone.lean
```

## Next step

After CI is green, prepare the first optional Mathlib adoption dry-run branch plan without changing `lakefile.lean` on main.
