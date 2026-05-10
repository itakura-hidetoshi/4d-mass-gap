# Phase 3: First Deferred Import Restoration

This step starts restoring deferred imports in a dependency-closed group.

## Scope

The first restoration group is deliberately small and does not introduce Mathlib.

It restores already-available internal imports into Global concrete status files:

```text
MGAP4D.Global.TheoremSurface
MGAP4D.DependencyMap
```

## Updated files

```text
MGAP4D/Global/Concrete/WorkUnitGlobalFinalAuditStatus.lean
MGAP4D/Global/Concrete/ReviewPacketStatus.lean
```

## Purpose

This connects Global concrete status records to:

- the Global theorem-surface layer;
- the Lean-side theorem dependency map;
- review-gate and route readiness surfaces.

## Invariant

This is still minimal Lean. It should keep CI green and does not add Mathlib.
