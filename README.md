# MGAP4D

MGAP4D is a Lean 4 repository for developing and checking the proof architecture of a normalized 4D mass gap theorem.

The repository is organized as a GitHub-native Lean project: the active source tree, CI, documentation, theorem-surface checkpoints, and migration history live directly in the repository.

## Current active Lean root

The current active Lean root is:

```text
MGAP4D.lean
```

It imports the current proof-hardening architecture, including:

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
MGAP4D/ProofHardening
MGAP4D/DependencyMap
MGAP4D/ReplacementCheckpoint
MGAP4D/ReplacementClosure
MGAP4D/ReplacementPass2
MGAP4D/ReplacementPass2Closure
MGAP4D/MathlibAdoptionGate
MGAP4D/PreMathlibClosure
MGAP4D/R1--R7
MGAP4D/Global
MGAP4D/FinalSpine
```

## Phase 3 status

The current `main` branch is closed at a **pre-Mathlib Phase 3 checkpoint**.

The active proof-hardening route is:

```text
TheoremSurface
  -> Replacement pass 1
  -> Replacement pass 2
  -> Pass2Closure
  -> MathlibAdoptionGate
  -> MathlibRequestRegistry
  -> R1 Hilbert theorem milestone
  -> DryRunBranchPlan
  -> DryRunChecklist
  -> DryRunResultLedger
  -> PreMathlibClosure
```

Important invariant:

```text
Mathlib is not yet introduced on main.
lakefile.lean is not modified for Mathlib.
No active Lean module imports Mathlib.
Public theorem claims remain review-gated.
```

## Mathlib dry-run policy

Mathlib adoption may be tested only through a dry-run branch, for example:

```text
feature/mathlib-r1-hilbert-dry-run
```

The dry-run branch may test scoped Mathlib imports for the R1 Hilbert path, but `main` remains pre-Mathlib unless the dry-run result is recorded, reviewed, and gated.

Relevant documents:

```text
docs/phase3_pre_mathlib_closure_checkpoint.md
docs/phase3_mathlib_adoption_gate.md
docs/phase3_mathlib_request_registry.md
docs/phase3_r1_hilbert_theorem_milestone_checkpoint.md
docs/phase3_mathlib_adoption_dry_run_branch_plan.md
docs/phase3_mathlib_dry_run_branch_checklist.md
docs/phase3_mathlib_dry_run_result_ledger.md
docs/phase3_mathlib_dry_run_execution_note.md
```

## Build

Install Lean through `elan`, then run:

```bash
lake update
lake build
```

For the full local audit sequence, run:

```bash
bash scripts/check.sh
```

The check script runs:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/replay_summary.py
lake update
lake build
```

GitHub Actions uses the workflow:

```text
Lean Direct Elan CI
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

## Migration and proof-hardening policy

The repository is populated and hardened in small, reviewable batches.

Each batch should satisfy:

```bash
bash scripts/check.sh
```

The GitHub branch should remain buildable after each source migration or proof-hardening batch.

## Archived release metadata

Earlier Zenodo-oriented metadata is retained as archival/release provenance. It should not drive the GitHub source layout. The active development source of truth is the GitHub Lean project and its CI status.

## Status

- GitHub-native Lean project: active
- CI: direct `elan` workflow
- Source migration: active, batch-based
- Phase 3: pre-Mathlib closure checkpoint reached
- Mathlib on main: not yet introduced
- Dry-run branch policy: recorded
- Public final theorem claim: review-gated pending independent replay and external audit
