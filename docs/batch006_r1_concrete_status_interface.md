# Batch 006: R1/Concrete Status Interface

This batch starts the GitHub-native migration of `MGAP4D/R1/Concrete`.

The original R1 concrete files depend on Mathlib inner product and projection APIs. The current repository remains a minimal Lean project while source migration is in progress, so Batch 006 introduces CI-safe R1 concrete status interfaces first.

## Initial targets

- `MGAP4D/R1/Concrete.lean`
- `MGAP4D/R1/Concrete/HilbertScaffoldStatus.lean`
- `MGAP4D/R1/Concrete/ExcitedSubspaceStatus.lean`
- `MGAP4D/R1/Concrete/InnerFunctionalStatus.lean`
- `MGAP4D/R1/Concrete/ProjectionStatus.lean`
- `MGAP4D/R1/Concrete/ClosureTargetsStatus.lean`

## Restore rule

After Mathlib and the concrete dependency closure are ready, these status interfaces can be replaced or refined by the original concrete files.

## CI rule

Each migration step must keep:

```bash
bash scripts/check.sh
```

or the GitHub Actions equivalent green.
