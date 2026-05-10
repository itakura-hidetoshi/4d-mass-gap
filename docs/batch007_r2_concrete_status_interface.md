# Batch 007: R2/Concrete Status Interface

This batch starts the GitHub-native migration of `MGAP4D/R2/Concrete`.

The original R2 concrete files depend on operator-theoretic and Mathlib APIs for self-adjoint restrictions, reducing subspaces, and spectrum of direct sums. The current repository keeps this as a CI-safe status interface until those dependencies are fully migrated.

## Initial targets

- `MGAP4D/R2/Concrete.lean`
- `MGAP4D/R2/Concrete/ReducingSubspaceStatus.lean`
- `MGAP4D/R2/Concrete/SelfAdjointRestrictionStatus.lean`
- `MGAP4D/R2/Concrete/ExcitedHamiltonianStatus.lean`
- `MGAP4D/R2/Concrete/SpectrumUnionStatus.lean`
- `MGAP4D/R2/Concrete/ExportStatus.lean`

## Restore rule

After the required Mathlib and concrete operator APIs are present, these files can be tightened into theorem-level concrete modules.

## CI rule

Each migration step must keep:

```bash
bash scripts/check.sh
```

green.
