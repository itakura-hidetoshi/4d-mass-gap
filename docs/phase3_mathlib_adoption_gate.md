# Phase 3: Mathlib Adoption Gate

This document defines when Mathlib may be introduced into the GitHub-native MGAP4D Lean project.

## Purpose

The project has completed two pre-Mathlib consolidation passes:

```text
TheoremSurface
Replacement pass 1
Replacement pass 2
Pass2Closure
PreMathlibGate
```

Mathlib should not be added merely for convenience. It should be introduced only when a concrete theorem-facing module requires actual mathematical infrastructure that cannot be responsibly represented by the current Prop-level surfaces.

## Adoption rule

Mathlib may be introduced only if all of the following hold:

- replacement pass 2 is closed;
- CI and audit checks are green;
- the requesting bundle is identified;
- the required Mathlib namespace/import group is recorded;
- status surfaces are preserved;
- public theorem claims remain review-gated;
- the introduction is incremental and dependency-scoped.

## First eligible requesters

The first likely Mathlib requesters are:

```text
R1 Hilbert / closed subspace theorem modules
R2 self-adjoint restriction theorem modules
R4 lower-bound theorem modules
R5 spectrum / infimum theorem modules
R6 interval-exclusion theorem modules
R7 atom / eigenstate theorem modules
```

## Added Lean modules

```text
MGAP4D/MathlibAdoptionGate.lean
MGAP4D/MathlibAdoptionGate/Policy.lean
MGAP4D/MathlibAdoptionGate/Requester.lean
MGAP4D/MathlibAdoptionGate/Gate.lean
```

## Current interpretation

This is only an adoption gate. It does not yet add Mathlib to `lakefile.lean` and does not import Mathlib into active modules.
