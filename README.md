# MGAP4D

MGAP4D is a Lean 4 repository for developing and checking the proof architecture of a normalized 4D mass gap theorem.

The repository is now organized as a GitHub-native Lean project: the active source tree, CI, documentation, and migration checkpoints live directly in the repository rather than being presented primarily as a Zenodo package mirror.

## Current theorem spine

The current active Lean root is:

```text
MGAP4D.lean
```

It imports the current proof architecture:

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
MGAP4D/Global/FinalAssembly.lean
MGAP4D/Map.lean
MGAP4D/FinalSpine.lean
```

The GitHub migration has started importing the expanded source snapshot in CI-checkable batches. The first active root batch includes:

```text
MGAP4D/R1/Basic.lean
MGAP4D/R2/Basic.lean
MGAP4D/R3/Basic.lean
MGAP4D/R4/Basic.lean
MGAP4D/R5/Basic.lean
MGAP4D/R6/Basic.lean
MGAP4D/R7/Basic.lean
MGAP4D/Global/FinalAssembly.lean
MGAP4D/Map.lean
```

## Build

Install Lean through `elan`, then run:

```bash
lake update
lake build
```

GitHub Actions uses the workflow:

```text
Lean Direct Elan CI
```

The workflow runs:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake update
lake build
```

## Repository layout

```text
MGAP4D/                  Active Lean source tree
MGAP4D.lean              Top-level Lean import root
docs/                    GitHub-native project documentation and migration notes
maps/                    Lightweight source maps and dependency maps
scripts/                 Local and CI audit scripts
.github/workflows/       GitHub Actions CI
```

## Migration policy

The repository is being populated in small, reviewable batches.

Each batch should satisfy:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake update
lake build
```

The GitHub branch should remain buildable after each source migration batch.

## Archived release metadata

Earlier Zenodo-oriented metadata is retained as archival/release provenance. It should not drive the GitHub source layout. The active development source of truth is the GitHub Lean project and its CI status.

## Status

- GitHub-native Lean project: active
- CI: direct `elan` workflow
- Source migration: in progress, batch-based
- Public final theorem claim: review-gated pending independent replay and external audit
