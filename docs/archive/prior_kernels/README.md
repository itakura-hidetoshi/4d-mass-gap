# Prior Kernels Archive

This directory is for historical MGAP4D Lean kernels that should be preserved but not automatically imported into the active theorem spine.

## Status classes

- `pending`: preserved but not yet reviewed under the current GitHub project layout
- `reviewed`: checked and eligible for small-batch migration into active source
- `superseded`: retained for lineage, but not intended for active import

## Active source boundary

The active Lean root is:

```text
MGAP4D.lean
```

Prior kernels in this archive do not affect the active build unless deliberately migrated into `MGAP4D/` and imported by `MGAP4D.lean`.

## Review rule

A prior kernel should move into active source only after:

```bash
bash scripts/check.sh
```

passes with the migrated file included.
