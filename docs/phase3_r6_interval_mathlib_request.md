# Phase 3: R6 Interval-Exclusion Scoped Mathlib Request

This document records the fifth scoped Mathlib request candidate.

## Requester

```text
MathlibRequester.r6Interval
```

## Purpose

The R6 interval-exclusion layer is a plausible place where real Mathlib infrastructure may become necessary, because future concrete theorem modules may need:

- intervals over real numbers;
- set intersections and emptiness lemmas;
- ordered field comparisons;
- spectral-gap interval statements;
- bridge lemmas from spectral-bottom data to interval exclusion.

## Requested import group

This request records a scoped candidate import group only. It does not modify `lakefile.lean` and does not import Mathlib in active Lean modules.

Candidate group:

```text
Mathlib.Data.Real.Basic
Mathlib.Order.Interval.Set.Basic
Mathlib.Data.Set.Basic
Mathlib.Order.Bounds.Basic
Mathlib.Topology.Basic
```

## Gate condition

This request may proceed only if:

```text
MathlibAdoptionGate.MathlibGate.ready
```

is satisfied with pass2 closed, CI green, audit green, scoped imports, preserved status surfaces, and public boundary held.

## Next step

After CI is green, add the Lean-side request record and keep Mathlib deferred until a concrete theorem module demands it.
