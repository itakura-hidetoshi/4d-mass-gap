# MGAP4D v1.6 Audit Summary

This document records the public audit summary for the MGAP4D v1.6 Zenodo release package.

## Release package

- Package: `MGAP4D_v1_6_Zenodo_release_package.zip`
- SHA256: `afc2c81f3f9b20a2bf92e93fb9417ab53f0a7e46a6769eb68be8d14407c69ab0`
- Version: `v1.6`
- Upload type: `Software`
- License: `CC-BY-4.0`

## Lean audit counts

| Metric | Count |
|---|---:|
| Lean files | 12,308 |
| Declarations | 52,137 |
| `sorry` | 0 |
| `admit` | 0 |
| `axiom` | 0 |
| `constant` | 0 |

## Interpretation

The above counts are the release-level audit values for the Zenodo package. The GitHub mirror is being populated incrementally, so this repository will temporarily contain fewer Lean files than the full v1.6 release package until source migration is complete.

## Migration invariant

The migration should preserve:

1. append-only release metadata;
2. explicit package hash recording;
3. CI-checkable Lean batches;
4. no hidden replacement of release claims;
5. reproducible audit scripts before final tagging.
