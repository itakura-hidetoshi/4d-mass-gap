# Batch 008: R3--R7 Concrete Status Interfaces

This batch adds CI-safe status interfaces for the remaining concrete layers:

```text
MGAP4D/R3/Concrete
MGAP4D/R4/Concrete
MGAP4D/R5/Concrete
MGAP4D/R6/Concrete
MGAP4D/R7/Concrete
```

## Why status interfaces first

The original concrete files depend on analytic/operator APIs and Mathlib objects that are not yet fully migrated into the active GitHub project. To keep `main` buildable, this batch records the theorem-routing surfaces and deferred import boundaries first.

## Layer roles

- R3: shifted nonnegative operator and zero-form-to-kernel route
- R4: exact lower-bound receipt and operator lower-bound bridge
- R5: spectrum set construction and spectral-bottom surface
- R6: gap interval exclusion surface
- R7: atom persistence and exact gap attainment surface

## Restore rule

After the required concrete and OperatorAPI dependency closure exists, these status modules can be refined into theorem-level concrete modules while preserving the same root paths.

## CI rule

Every migration step should keep:

```bash
bash scripts/check.sh
```

green.
