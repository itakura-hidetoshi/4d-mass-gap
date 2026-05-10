# 4D Mass Gap

This repository contains the Lean formalization and proof architecture for the MGAP4D project.

## MGAP4D v1.6 Zenodo migration

This repository is being populated incrementally from the MGAP4D v1.6 Zenodo release package.

Canonical package hash:

```text
MGAP4D_v1_6_Zenodo_release_package.zip
SHA256 afc2c81f3f9b20a2bf92e93fb9417ab53f0a7e46a6769eb68be8d14407c69ab0
```

Release audit summary:

```text
Lean files: 12,308
Declarations: 52,137
sorry: 0
admit: 0
axiom: 0
constant: 0
```

## GitHub CI status

The repository uses the workflow:

```text
Lean CI Direct Elan
```

The workflow runs:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake update
lake build
```

The first migration checkpoint with Lean CI green is recorded in:

```text
docs/migration_checkpoint_lean_ci_green.md
```

## Current Lean root

The top-level Lean root is:

```text
MGAP4D.lean
```

The current scaffold includes:

```text
MGAP4D/Foundation
MGAP4D/Certificates
MGAP4D/Spectral
MGAP4D/Hamiltonian
MGAP4D/OSPositivity
MGAP4D/Plaquette
MGAP4D/Constructive
MGAP4D/Audit
MGAP4D/Release
MGAP4D/FinalSpine.lean
```

## Next source migration step

Move files from `MGAP4D_v1_6_expanded_source_snapshot.zip` in small CI-checkable batches. Each batch should keep `lake build` green before the next batch is added.
