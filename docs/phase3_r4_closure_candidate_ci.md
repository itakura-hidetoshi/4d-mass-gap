# Phase 3: R4 Closure-Candidate CI

This document records the CI result after wiring the R4 lower-bound closure-candidate checkpoint through the R4 theorem root and top-level root.

## CI result

```text
Workflow: Lean Direct Elan CI
Run ID: 25728202304
Build job ID: 75546379402
Commit: 985c6c8341ab8d6348ae494e016a3e976ea7acef
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
Generate Lake manifest: success
lake build: success
```

## Interpretation

The R4 lower-bound closure-candidate checkpoint builds successfully on `main`.

## Invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R4 lower-bound route remains a closure candidate, not a closure claim
R4 theorem route remains deferred and review-gated
```
