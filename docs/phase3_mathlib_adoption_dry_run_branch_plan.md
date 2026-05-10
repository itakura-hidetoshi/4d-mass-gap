# Phase 3: Mathlib Adoption Dry-Run Branch Plan

This document defines a dry-run branch plan for Mathlib adoption.

## Purpose

The main branch currently records scoped Mathlib requests and a pre-Mathlib R1 Hilbert theorem milestone, but still does not import Mathlib and does not modify `lakefile.lean`.

The next safe step is not immediate Mathlib adoption on `main`. The next safe step is a dry-run branch plan.

## Dry-run branch rule

Mathlib adoption may be tested only on a separate branch, for example:

```text
feature/mathlib-r1-hilbert-dry-run
```

The branch may modify:

```text
lakefile.lean
lake-manifest.json
lean-toolchain if needed
MGAP4D/R1/Theorem/HilbertSkeleton.lean or a new Mathlib-specific sibling module
```

The main branch should remain pre-Mathlib until the dry-run passes.

## Required gates

A dry-run branch is admissible only if:

- Pass 2 closure is recorded;
- PreMathlibGate is ready;
- MathlibGate is ready;
- R1 Hilbert request is scoped;
- R1 Hilbert milestone is ready;
- status surfaces remain preserved;
- public boundary remains held.

## Failure handling

If the dry-run fails, main remains unchanged. The failure should be recorded as a dry-run result, not patched silently.

## Added Lean modules

```text
MGAP4D/MathlibAdoptionGate/DryRunBranchPlan.lean
MGAP4D/MathlibAdoptionGate/DryRunGate.lean
```

## Current status

This plan still does not import Mathlib and does not modify `lakefile.lean` on main.
