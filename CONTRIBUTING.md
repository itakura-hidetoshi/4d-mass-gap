# Contributing to MGAP4D

This repository is developed as a GitHub-native Lean 4 project.

## Development rules

1. Keep `main` buildable.
2. Add Lean files in small batches.
3. Wire new files into an import root only after they compile.
4. Do not introduce `sorry`, `admit`, `axiom`, or `constant` into active Lean source.
5. Keep release/provenance metadata separate from active proof code.

## Required local checks

Before committing a migration batch, run:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake update
lake build
```

## Source migration batches

When migrating files from an archive or snapshot:

- prefer small, import-closed groups;
- document any deferred imports;
- do not silently overwrite active source;
- preserve original semantics when adapting files for CI;
- record staging changes in `docs/`.

## Naming

Use the following layout for active proof files:

```text
MGAP4D/<Layer>.lean
MGAP4D/<Layer>/<Module>.lean
```

Use `docs/` and `maps/` for project documentation, dependency maps, and migration notes.

## Review gate

Public theorem-level claims remain review-gated until independent replay and external audit are complete.
