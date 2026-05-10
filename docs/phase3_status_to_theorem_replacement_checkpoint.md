# Phase 3: Status-to-Theorem Replacement Checkpoint

This checkpoint prepares the first replacement pass from status-only surfaces toward theorem surfaces.

## Purpose

The repository now has:

```text
R1--R7 theorem surfaces
Global theorem surface
Global/Concrete summary surface
DependencyMap
ProofHardening
```

The next step is not yet Mathlib adoption. The next step is to define a controlled replacement checkpoint that says which status modules can be tightened first.

## Replacement order

The first replacement pass should follow this order:

1. OperatorAPI readiness surfaces
2. R1 closure target surface
3. R2 export surface
4. R4 export surface
5. R3 export surface
6. R5 export surface
7. R6 export surface
8. R7 exact-gap surface
9. Global/Concrete summary surface
10. FinalAssembly concrete readiness surface

## Rules

Each replacement step must:

- preserve CI green status;
- avoid adding Mathlib unless strictly required;
- keep the older status surface available until the new theorem surface builds;
- record the replacement in docs;
- avoid expanding public theorem claims before review.

## Added Lean modules

```text
MGAP4D/ReplacementCheckpoint.lean
MGAP4D/ReplacementCheckpoint/Plan.lean
MGAP4D/ReplacementCheckpoint/Gate.lean
MGAP4D/ReplacementCheckpoint/FirstPass.lean
```

## Current interpretation

This checkpoint is a controlled transition plan. It is not a final replacement of analytic proof modules.
