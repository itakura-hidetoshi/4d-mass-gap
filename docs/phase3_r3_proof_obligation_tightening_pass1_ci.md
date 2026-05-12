# Phase 3: R3 Proof-Obligation Tightening Pass 1 CI

This document records the CI result after wiring the R3 proof-obligation tightening pass 1 checkpoint through the R3 theorem root and top-level root.

## CI result

```text
Workflow: Lean Direct Elan CI
Run ID: 25733674757
Build job ID: 75564973714
Commit: a3f1f801f2d46491d11574110e0ba37d4f89b8de
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
Generate Lake manifest: success
lake build: success
```

## Interpretation

The R3 proof-obligation tightening pass 1 checkpoint builds successfully on `main`.

## Tightened R3 surfaces

```text
shifted route obligation
zero-form route obligation
operator-boundary obligation
bridge obligation
downstream R4--R7 review-gate obligation
public-boundary obligation
```

## Invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R3 tightening pass 1 is not theorem completion
R4--R7 theorem completion is not unlocked
final gap theorem release is not unlocked
public theorem boundary remains held
```
