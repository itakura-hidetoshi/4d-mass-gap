# MGAP4D Documentation

This directory contains project documentation for the GitHub-native MGAP4D Lean 4 repository.

The active source tree is:

```text
MGAP4D/
MGAP4D.lean
```

The documentation here is organized around development, migration, dependency review, and audit checkpoints.

## Main documents

- `../README.md` — project overview and build instructions
- `../ROADMAP.md` — GitHub-native migration roadmap
- `../CONTRIBUTING.md` — contribution and migration rules
- `source_tree_plan.md` — source-tree migration plan
- `expanded_source_snapshot_inventory.md` — imported snapshot inventory
- `batch004_global_concrete_status_only.md` — deferred-import strategy for Global/Concrete status files
- `migration_checkpoint_lean_ci_green.md` — first CI-green migration checkpoint

## Dependency and review docs

- `DEPENDENCY_SUMMARY.md` — work-unit dependency chain
- `FINAL_REVIEW_CHECKLIST.md` — review checklist
- `audit_summary.md` — archived audit summary
- `release_integrity.md` — archived package integrity notes

## Archive

Historical release provenance lives under:

```text
docs/archive/
```

Archive material is kept for traceability. It does not control the active GitHub source layout.

## Development rule

Every active source migration batch should keep these checks green:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake update
lake build
```

## Current focus

The next development focus is migrating `OperatorAPI` interfaces and then restoring deferred imports in `MGAP4D/Global/Concrete`.
