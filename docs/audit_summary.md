# Archived Audit Summary

This document records historical audit counts from the MGAP4D v1.6 package lineage.

The active GitHub repository is checked by:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake update
lake build
```

## Historical package record

- Package: `MGAP4D_v1_6_Zenodo_release_package.zip`
- SHA256: `afc2c81f3f9b20a2bf92e93fb9417ab53f0a7e46a6769eb68be8d14407c69ab0`
- Version: `v1.6`

## Historical Lean audit counts

| Metric | Count |
|---|---:|
| Lean files | 12,308 |
| Declarations | 52,137 |
| `sorry` | 0 |
| `admit` | 0 |
| `axiom` | 0 |
| `constant` | 0 |

## GitHub-native interpretation

The active GitHub repository may contain fewer files during migration. The current source of truth for buildability is GitHub Actions, not the historical package count.

## Invariant

The migration should preserve:

1. buildable Lean batches;
2. no active `sorry`, `admit`, `axiom`, or `constant` tokens;
3. explicit documentation of any deferred import;
4. review-gated public theorem claims.
