# Phase 3: Mathlib Dry-Run Result PR #2

This document records the result surface for the second scoped Mathlib dry-run branch.

## Pull request

```text
PR: pending
branch: feature/mathlib-r2-restriction-dry-run
base: main
```

## Requester

```text
MathlibRequester.r2Restriction
```

## Planned import group

```text
Mathlib.Analysis.InnerProductSpace.Basic
Mathlib.Analysis.InnerProductSpace.Projection.Basic
Mathlib.Topology.Algebra.Module.Basic
```

## Actual import group used

```text
Mathlib.Analysis.InnerProductSpace.Basic
Mathlib.Analysis.InnerProductSpace.Projection.Basic
Mathlib.Topology.Algebra.Module.Basic
```

## CI result

```text
pending
```

## Interpretation

This branch is a scoped dry-run for the R2 self-adjoint restriction path.

The dry-run does not imply automatic merge. It only tests whether the scoped Mathlib dependency and R2 restriction sibling module can build on the dry-run branch.

## Main branch invariant

```text
main remains pre-Mathlib
lakefile.lean on main remains unchanged for Mathlib
no active main-branch Lean module imports Mathlib
status surfaces remain preserved
public theorem claims remain review-gated
```

## Next step

Open the draft PR, observe CI, then update this ledger with the CI result before any merge decision.
