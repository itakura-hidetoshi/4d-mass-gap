# Batch 010: Prior Kernels Archive Layout

This batch defines a GitHub-native archive layout for prior MGAP4D Lean kernels.

The goal is to preserve lineage without mixing unreviewed historical material directly into the active `MGAP4D.lean` proof root.

## Active source root

```text
MGAP4D.lean
MGAP4D/
```

Active imports should remain CI-checked and reviewable.

## Archive root

```text
docs/archive/prior_kernels/
maps/PRIOR_KERNELS_ARCHIVE_PLAN.json
MGAP4D/Archive.lean
MGAP4D/Archive/PriorKernels.lean
```

## Policy

Prior kernels should be treated as historical source material until reviewed.

They should not be imported into the active theorem spine until:

1. their dependency closure is known;
2. they compile under the current Lean toolchain;
3. they pass the forbidden-token audit;
4. their theorem surface is mapped to the active R1--R7/Global layout;
5. the migration is small enough for review.

## Recommended archive structure

```text
docs/archive/prior_kernels/
  README.md
  inventory.md
  reviewed/
  pending/
  superseded/
```

## Restore flow

1. Add prior kernel inventory only.
2. Classify kernels as `pending`, `reviewed`, or `superseded`.
3. Move small reviewed kernels into active source only when CI stays green.
4. Record the movement in `maps/` and `ROADMAP.md`.

## Current decision

Batch 010 creates the archive layout and Lean-side archive status. It does not import prior kernels into the active theorem spine.
