# Phase 3: Mathlib Dry-Run Branch Checklist

This document records the checklist for creating a Mathlib dry-run branch.

## Purpose

The main branch remains pre-Mathlib. Before changing `lakefile.lean` or importing Mathlib, a separate dry-run branch should be used.

Recommended branch:

```text
feature/mathlib-r1-hilbert-dry-run
```

## Checklist before creating the branch

```text
Pass2Closure recorded
PreMathlibGate recorded
MathlibGate recorded
DryRunBranchPlan recorded
DryRunGate recorded
R1 Hilbert request scoped
R1 Hilbert milestone ready
main branch clean
current CI green or last known failure recorded
public boundary held
```

## Checklist on the dry-run branch

```text
modify lakefile.lean only on branch
run lake update
commit lake-manifest.json only if generated successfully
add a Mathlib-specific R1 Hilbert module instead of weakening existing status modules
run scripts/check.sh
record build result
record import group actually used
preserve status surfaces
avoid public theorem claim expansion
```

## Failure rule

If the dry-run fails, the failure must be recorded explicitly. Main remains unchanged. Do not silently patch over the failed import group.

## Success rule

If the dry-run succeeds, create a review note before any merge to main. The merge decision remains gated by `MathlibGate.ready` and public-boundary preservation.

## Added Lean module

```text
MGAP4D/MathlibAdoptionGate/DryRunChecklist.lean
```

## Current status

This checklist still does not import Mathlib and does not modify `lakefile.lean` on main.
