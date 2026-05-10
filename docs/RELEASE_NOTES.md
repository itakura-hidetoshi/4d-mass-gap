# Development Notes

This file records GitHub-native development notes for the MGAP4D Lean 4 repository.

## Current repository status

- Lean 4 Lake project initialized
- GitHub Actions uses direct `elan`
- Active root: `MGAP4D.lean`
- Active source tree: `MGAP4D/`
- Migration is batch-based and CI-checked

## Completed migration batches

- Batch 001: active R1--R7 root files, `Global.FinalAssembly`, and `Map`
- Batch 002: lightweight docs and maps
- Batch 003: snapshot root manifests and merge notes
- Batch 004: `Global/Concrete` status-only files with deferred imports

## Current checks

The CI workflow runs:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake update
lake build
```

## Current theorem spine

The active theorem spine connects:

```text
Foundation
Certificates
Spectral
Hamiltonian
OSPositivity
Plaquette
Constructive
Audit
Release
Global.FinalAssembly
FinalSpine
```

## Remaining development work

- Migrate `OperatorAPI` interfaces
- Migrate `R1/Concrete` and `R2/Concrete`
- Restore deferred imports in `Global/Concrete`
- Migrate remaining R3--R7 concrete files
- Add reviewed source maps for larger archive material
- Keep CI green after each batch

## Review boundary

Public theorem-level claims remain review-gated pending independent replay and external audit.
