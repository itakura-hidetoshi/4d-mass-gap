# Phase 3: Pre-Mathlib Closure Checkpoint

This checkpoint records the current `main` branch state before any Mathlib adoption.

## Completed surfaces

The project now has the following pre-Mathlib chain:

```text
TheoremSurface
  -> Replacement pass 1
  -> Replacement pass 2
  -> Pass2Closure
  -> MathlibAdoptionGate
  -> MathlibRequestRegistry
  -> R1 Hilbert theorem milestone
  -> DryRunBranchPlan
  -> DryRunChecklist
  -> DryRunResultLedger
```

## Main branch invariant

At this checkpoint, `main` remains pre-Mathlib:

```text
lakefile.lean unchanged for Mathlib
no active Mathlib imports
status surfaces preserved
public boundary held
```

## Completed Mathlib request records

```text
R1 Hilbert
R2 self-adjoint restriction
R4 lower bound
R5 spectrum / infimum
R6 interval exclusion
R7 atom / exact gap
```

## Completed R1 Hilbert theorem-facing path

```text
HilbertScaffoldStatus
  -> HilbertTheoremCandidate
  -> HilbertCandidateBundle
  -> HilbertTheoremChecklist
  -> HilbertProofObligationMap
  -> R1/Theorem/HilbertSkeleton
  -> R1/Theorem/HilbertSkeletonBundle
  -> R1/Theorem/HilbertMilestone
```

## Dry-run path

A future Mathlib adoption may be tested only through a branch-level dry-run path:

```text
DryRunBranchPlan
  -> DryRunGate
  -> DryRunChecklist
  -> DryRunResultLedger
```

Failure is a valid recorded outcome. Success still does not imply merge.

## Still deferred

This checkpoint does not:

- introduce Mathlib;
- modify `lakefile.lean` for Mathlib;
- replace Prop-level theorem skeletons with analytic Mathlib proofs;
- expand public theorem claims beyond review gates.

## Next step

After CI is green, create the Lean-side `PreMathlibClosure` module and then decide whether to create the dry-run branch outside `main`.
