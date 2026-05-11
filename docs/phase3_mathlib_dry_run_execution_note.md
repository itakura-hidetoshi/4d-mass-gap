# Phase 3: Mathlib Dry-Run Execution Note

This document records the execution note for a future Mathlib dry-run branch.

## Purpose

The main branch is now closed at the pre-Mathlib checkpoint. The next operational step, if chosen, is not to modify `main`, but to create a dry-run branch and test the R1 Hilbert Mathlib request there.

Recommended branch:

```text
feature/mathlib-r1-hilbert-dry-run
```

## Execution sequence

```bash
git checkout main
git pull
git checkout -b feature/mathlib-r1-hilbert-dry-run
```

Then, on the dry-run branch only:

```text
1. Modify lakefile.lean for a scoped Mathlib dependency.
2. Run lake update.
3. Commit lake-manifest.json only if generated successfully.
4. Add a Mathlib-specific sibling module for R1 Hilbert.
5. Run bash scripts/check.sh.
6. Record the result in the dry-run result ledger.
```

## Main branch rule

Do not modify `main` for Mathlib until the dry-run has a recorded success and a review note.

## Failure rule

If the dry-run fails, keep the failure record and return to `main` unchanged.

## Success rule

If the dry-run succeeds, open a review note or PR. Success does not imply merge.

## Added Lean module

```text
MGAP4D/MathlibAdoptionGate/DryRunExecutionNote.lean
```

## Current status

This note still does not import Mathlib and does not modify `lakefile.lean` on main.
