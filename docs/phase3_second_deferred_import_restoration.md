# Phase 3: Second Deferred Import Restoration

This step restores internal imports for closure-priority status files.

## Scope

This is a dependency-closed internal restoration. It does not add Mathlib.

Updated files:

```text
MGAP4D/Global/Concrete/ClosurePriorityGlobal.lean
MGAP4D/Global/Concrete/ClosurePriorityDecision.lean
```

Connected internal modules:

```text
MGAP4D.DependencyMap
MGAP4D.ProofHardening
```

## Purpose

Closure priority should be connected to:

- the theorem-surface dependency route;
- the proof-hardening plan;
- the CI/review gate discipline.

## Next step

After CI is green, continue restoring deferred imports for remaining Global/Concrete audit status files.
