# Phase 3: R1--R7 Scoped Mathlib Dry-Run Series Review

This document records the complete scoped Mathlib dry-run series for the Phase 3 theorem path.

## Scope

The reviewed series covers:

```text
R1 Hilbert path
R2 self-adjoint restriction path
R3 shifted / zero-form path
R4 lower-bound path
R5 spectrum / infimum path
R6 interval-exclusion path
R7 atom / exact-gap path
```

Each path was tested through a scoped dry-run branch and a draft pull request. The dry-runs added Mathlib only on their respective branches and did not introduce Mathlib into `main`.

## Dry-run PRs

```text
PR #1: R1 Hilbert path dry-run: success, draft/unmerged
PR #3: R2 self-adjoint restriction path dry-run: success, draft/unmerged
PR #4: R3 shifted / zero-form path dry-run: success, draft/unmerged
PR #5: R4 lower-bound path dry-run: success, draft/unmerged
PR #6: R5 spectrum / infimum path dry-run: success, draft/unmerged
PR #7: R6 interval-exclusion path dry-run: success, draft/unmerged
PR #8: R7 atom / exact-gap path dry-run: success, draft/unmerged
```

## CI summary

```text
R1 dry-run: success
R2 dry-run: success
R3 dry-run: success
R4 dry-run: success
R5 dry-run: success
R6 dry-run: success
R7 dry-run: success
```

## Common import group

The scoped dry-run branches used the same minimal import group:

```text
Mathlib.Analysis.InnerProductSpace.Basic
Mathlib.Analysis.InnerProductSpace.Projection.Basic
Mathlib.Topology.Algebra.Module.Basic
```

## Interpretation

The complete R1--R7 dry-run series shows that the current theorem-path sibling modules can build under a scoped Mathlib dependency on dry-run branches.

This does not imply that the theorem targets are complete. In particular:

```text
R3 shifted / zero-form theorem route remains deferred
R4 lower-bound theorem route remains deferred
R5 spectrum / infimum theorem route remains deferred
R6 interval-exclusion theorem route remains deferred
R7 atom / exact-gap / final value theorem route remains deferred
```

The dry-run series establishes buildability of the Mathlib contact surface, not final theorem discharge.

## Main branch invariant

```text
main remains pre-Mathlib
lakefile.lean on main remains unchanged for Mathlib
no active main-branch Lean module imports Mathlib
all dry-run PRs remain draft/unmerged unless separately reviewed
dry-run success does not imply automatic merge
public theorem claims remain review-gated
```

## Next review question

The next question is not whether the dry-run branches build; they do. The next question is whether to prepare a separate reviewed adoption proposal for Mathlib on `main`, including:

```text
lakefile scope review
lake-manifest behavior review
import-group minimality review
main-branch theorem route review
public-claim boundary review
rollback / close-dry-run decision review
```

Until that review is complete, `main` remains pre-Mathlib.
