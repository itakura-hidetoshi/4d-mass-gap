# Phase 3: Replacement Pass 2 Plan

This document defines the second status-to-theorem replacement pass.

## Purpose

Pass 1 connected each major status/export surface to `MGAP4D.ReplacementCheckpoint` while preserving the original status records.

Pass 2 should move one step closer to theorem-facing bundles, still without removing status surfaces and still without adding Mathlib.

## Pass 2 target order

```text
1. OperatorAPI theorem-ready bundle
2. R1 closure theorem-ready bundle
3. R2/R4/R3 route theorem-ready bundle
4. R5/R6/R7 route theorem-ready bundle
5. Global/Concrete theorem-ready bundle
6. FinalAssembly theorem-ready bundle
```

## Rules

Pass 2 must:

- keep status surfaces available;
- keep CI green;
- keep Mathlib deferred unless a real theorem-level module requires it;
- avoid broad public-claim expansion;
- preserve the public review boundary;
- update Lean-side tracking modules before replacing any active root import.

## Added Lean modules

```text
MGAP4D/ReplacementPass2.lean
MGAP4D/ReplacementPass2/Plan.lean
MGAP4D/ReplacementPass2/Gate.lean
MGAP4D/ReplacementPass2/BundleTargets.lean
```

## Current interpretation

Pass 2 is a consolidation pass. It prepares theorem-facing bundles. It is not yet the full analytic theorem replacement pass.
