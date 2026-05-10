# Batch 009: Deferred Import Restoration Plan

Batch 004--008 introduced CI-safe status interfaces for modules whose original snapshot versions depended on not-yet-migrated concrete layers or Mathlib APIs.

This document defines how those deferred imports should be restored without breaking `main`.

## Current status

The active root now imports:

```text
MGAP4D.R1.Concrete
MGAP4D.R2.Concrete
MGAP4D.R3.Concrete
MGAP4D.R4.Concrete
MGAP4D.R5.Concrete
MGAP4D.R6.Concrete
MGAP4D.R7.Concrete
MGAP4D.OperatorAPI
```

These are currently status interfaces. They preserve routing and proof-obligation surfaces while keeping CI green.

## Restoration order

1. Restore OperatorAPI definitions that do not require Mathlib.
2. Restore R1 concrete files that only need basic Lean objects.
3. Add Mathlib dependency only when the first actual theorem layer requires it.
4. Restore R1 projection and closed-subspace APIs.
5. Restore R2 reducing-subspace and self-adjoint restriction APIs.
6. Restore R4 lower-bound and form-to-operator bridge APIs.
7. Restore R3 zero-form-to-kernel route.
8. Restore R5/R6 spectrum surfaces.
9. Restore R7 atom persistence and exact-gap surfaces.
10. Restore Global/Concrete imports after all dependent layers compile.

## File replacement rule

For each status file:

1. create a side-by-side theorem-level module when possible;
2. run `bash scripts/check.sh`;
3. replace the status import only after the theorem-level module builds;
4. keep the status file as a migration note if it remains useful.

## CI rule

Each restoration step must pass:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake update
lake build
```

## Review gate

Restoring imports changes the proof surface. Each restoration should be small enough to review independently.
