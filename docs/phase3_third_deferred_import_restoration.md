# Phase 3: Third Deferred Import Restoration

This step restores internal imports for the remaining Global/Concrete work-unit audit status files.

## Scope

This is a dependency-closed internal restoration. It does not add Mathlib.

Updated work-unit audit status files:

```text
MGAP4D/Global/Concrete/WorkUnitR1EllCLMAuditStatus.lean
MGAP4D/Global/Concrete/WorkUnitR1ProjectionAuditStatus.lean
MGAP4D/Global/Concrete/WorkUnitR2ReducingSpectrumAuditStatus.lean
MGAP4D/Global/Concrete/WorkUnitR3UnboundedKernelAuditStatus.lean
MGAP4D/Global/Concrete/WorkUnitR4LowerBoundAuditStatus.lean
MGAP4D/Global/Concrete/WorkUnitR7AtomExactGapAuditStatus.lean
```

Connected internal modules:

```text
MGAP4D.DependencyMap
MGAP4D.ProofHardening
```

## Purpose

Each work-unit audit status should have an explicit connection to:

- the theorem-surface dependency route;
- the proof-hardening gate;
- the active CI/review discipline.

## Next step

After CI is green, restore internal imports for root manifest and review metadata status files.
