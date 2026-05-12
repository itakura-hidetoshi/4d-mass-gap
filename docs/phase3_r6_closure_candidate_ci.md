# Phase 3: R6 Closure-Candidate CI

This document records the CI result after wiring the R6 interval-exclusion closure-candidate checkpoint through the R6 theorem root and top-level root.

## CI result

```text
Workflow: Lean Direct Elan CI
Run ID: 25728677950
Build job ID: 75547999771
Commit: d5291fb422e717fb288d3fc992dccf0966c6e261
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
Generate Lake manifest: success
lake build: success
```

## Interpretation

The R6 interval-exclusion closure-candidate checkpoint builds successfully on `main`.

## Invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R6 interval-exclusion route remains a closure candidate, not a closure claim
R6 theorem route remains deferred and review-gated
```
