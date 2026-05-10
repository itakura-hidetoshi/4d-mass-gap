# Phase 3: R2 Self-Adjoint Restriction Scoped Mathlib Request

This document records the second scoped Mathlib request candidate.

## Requester

```text
MathlibRequester.r2Restriction
```

## Purpose

The R2 restriction layer is a plausible place where real Mathlib infrastructure may become necessary, because future concrete theorem modules may need:

- linear operators;
- domains and restrictions;
- symmetric/self-adjoint operator interfaces;
- nonnegative operator or quadratic-form bridge structures;
- spectral-ready operator records.

## Requested import group

This request records a scoped candidate import group only. It does not modify `lakefile.lean` and does not import Mathlib in active Lean modules.

Candidate group:

```text
Mathlib.Analysis.InnerProductSpace.Basic
Mathlib.Analysis.NormedSpace.OperatorNorm
Mathlib.LinearAlgebra.LinearPMap
Mathlib.Analysis.InnerProductSpace.Projection
```

## Gate condition

This request may proceed only if:

```text
MathlibAdoptionGate.MathlibGate.ready
```

is satisfied with pass2 closed, CI green, audit green, scoped imports, preserved status surfaces, and public boundary held.

## Next step

After CI is green, add the Lean-side request record and keep Mathlib deferred until a concrete theorem module demands it.
