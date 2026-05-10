# Phase 3: Fourth Deferred Import Restoration

This step restores internal imports for root manifest and package-status surfaces.

## Scope

This is a dependency-closed internal restoration. It does not add Mathlib.

Updated file:

```text
MGAP4D/Global/Concrete/ArtifactHashManifestStatus.lean
```

Connected internal modules:

```text
MGAP4D.DependencyMap
MGAP4D.ProofHardening
MGAP4D.Global.TheoremSurface
```

## Purpose

The root manifest status should be connected to:

- the theorem dependency route;
- the proof-hardening gate;
- the Global theorem-surface final boundary.

## Next step

After CI is green, review all Global/Concrete imports and prepare the first status-to-theorem replacement checkpoint.
