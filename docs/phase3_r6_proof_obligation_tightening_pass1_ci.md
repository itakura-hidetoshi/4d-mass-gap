# Phase 3: R6 Proof-Obligation Tightening Pass 1 CI

## CI result

```text
Workflow: Lean Direct Elan CI
Run ID: 25764732488
Build job ID: 75674474180
Commit: 4d6bcd61d45b6cc1556399a3eb7754c381d1d70d
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
Generate Lake manifest: success
lake build: success
```

## Tightened surfaces

```text
R5 bridge obligation
vacuum-side obligation
excited-side obligation
interval-boundary obligation
interval-exclusion target obligation
Mathlib request boundary
status compatibility boundary
upstream R5 review dependency
downstream R7 review gate
public-boundary obligation
```

## Invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R6 theorem completion is not claimed
R7 theorem completion is not unlocked
public theorem boundary remains held
```
