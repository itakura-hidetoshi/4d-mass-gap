# Phase 3: R7 Atom / Exact-Gap Scoped Mathlib Request

This document records the sixth scoped Mathlib request candidate.

## Requester

```text
MathlibRequester.r7AtomExact
```

## Purpose

The R7 atom / exact-gap layer is a plausible place where real Mathlib infrastructure may become necessary, because future concrete theorem modules may need:

- eigenvalue / eigenspace style records;
- point-spectrum or atom-style witnesses;
- nonzero vector and normalized vector records;
- spectral membership links;
- exact value comparison for the gap value.

## Requested import group

This request records a scoped candidate import group only. It does not modify `lakefile.lean` and does not import Mathlib in active Lean modules.

Candidate group:

```text
Mathlib.LinearAlgebra.Eigenspace.Basic
Mathlib.Analysis.InnerProductSpace.Basic
Mathlib.Data.Real.Basic
Mathlib.Data.Set.Basic
Mathlib.Order.Basic
```

## Gate condition

This request may proceed only if:

```text
MathlibAdoptionGate.MathlibGate.ready
```

is satisfied with pass2 closed, CI green, audit green, scoped imports, preserved status surfaces, and public boundary held.

## Next step

After CI is green, add the Lean-side request record and keep Mathlib deferred until a concrete theorem module demands it.
