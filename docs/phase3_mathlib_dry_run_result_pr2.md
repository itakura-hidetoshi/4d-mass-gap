# Phase 3: Mathlib Dry-Run Result PR #3

This document records the result of the second scoped Mathlib dry-run branch.

## Pull request

```text
PR #3: Dry run Mathlib adoption for R2 self-adjoint restriction path
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
Lean Direct Elan CI #564
Run ID: 25716432314
Audit metadata and Lean source: success
Build Lean project via direct elan: success
Generate Lake manifest: success
lake build: success
```

## Interpretation

The dry-run succeeded for the R2 self-adjoint restriction Mathlib sibling module.

This result does not imply automatic merge. It means the scoped Mathlib dependency and R2 restriction sibling module are buildable on the dry-run branch.

## Main branch invariant

```text
main remains pre-Mathlib
lakefile.lean on main remains unchanged for Mathlib
no active main-branch Lean module imports Mathlib
status surfaces remain preserved
public theorem claims remain review-gated
```

## Next step

Create a review note and decide whether to keep the PR as draft, close it as a successful dry-run, or prepare a gated merge proposal.
