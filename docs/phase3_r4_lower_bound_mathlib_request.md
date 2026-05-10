# Phase 3: R4 Lower-Bound Scoped Mathlib Request

This document records the third scoped Mathlib request candidate.

## Requester

```text
MathlibRequester.r4LowerBound
```

## Purpose

The R4 lower-bound layer is a plausible place where real Mathlib infrastructure may become necessary, because future concrete theorem modules may need:

- ordered algebraic structures;
- inequalities over rational or real constants;
- norm and inner-product estimates;
- nonnegative quadratic-form style bounds;
- bridge lemmas from form estimates to operator lower bounds.

## Requested import group

This request records a scoped candidate import group only. It does not modify `lakefile.lean` and does not import Mathlib in active Lean modules.

Candidate group:

```text
Mathlib.Data.Rat.Basic
Mathlib.Data.Real.Basic
Mathlib.Order.Basic
Mathlib.Analysis.InnerProductSpace.Basic
Mathlib.Analysis.NormedSpace.Basic
```

## Gate condition

This request may proceed only if:

```text
MathlibAdoptionGate.MathlibGate.ready
```

is satisfied with pass2 closed, CI green, audit green, scoped imports, preserved status surfaces, and public boundary held.

## Next step

After CI is green, add the Lean-side request record and keep Mathlib deferred until a concrete theorem module demands it.
