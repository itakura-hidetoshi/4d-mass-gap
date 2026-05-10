# Batch 005: OperatorAPI Status Interface

This batch starts the GitHub-native migration of `MGAP4D/OperatorAPI`.

The original snapshot OperatorAPI files depend on not-yet-migrated modules under:

```text
MGAP4D.R1.Concrete
MGAP4D.R2.Concrete
MGAP4D.R3.Concrete
MGAP4D.R4.Concrete
MGAP4D.R5.Concrete
MGAP4D.R6.Concrete
MGAP4D.R7.Concrete
MGAP4D.Global.Concrete
```

Some files also depend on Mathlib, while the current GitHub project intentionally remains a minimal Lean project.

## Strategy

Batch 005 introduces CI-safe status interfaces under `MGAP4D/OperatorAPI/`.

These files encode the routing and execution surfaces without importing unresolved dependencies. Original imports can be restored after the corresponding Concrete modules are migrated.

## Initial targets

- `Candidate.lean`
- `BindingObligations.lean`
- `AdoptionPlan.lean`
- `PhasePlan.lean`
- `Phase1Targets.lean`
- `PhaseSelectionStatus.lean`
- `ClosureWorkUnitExecutionStatus.lean`
- `WorkUnitChainExecutionReady.lean`

## Invariant

Each batch must keep:

```bash
bash scripts/check.sh
```

or the equivalent GitHub Actions workflow green.
