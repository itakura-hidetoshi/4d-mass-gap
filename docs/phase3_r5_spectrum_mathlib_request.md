# Phase 3: R5 Spectrum / Infimum Scoped Mathlib Request

This document records the fourth scoped Mathlib request candidate.

## Requester

```text
MathlibRequester.r5Spectrum
```

## Purpose

The R5 spectrum / infimum layer is a plausible place where real Mathlib infrastructure may become necessary, because future concrete theorem modules may need:

- sets and set-theoretic spectrum records;
- order-theoretic infimum / lower-bound constructions;
- real-valued comparison lemmas;
- nonempty spectrum-style witnesses;
- links from lower-bound data to spectral-bottom data.

## Requested import group

This request records a scoped candidate import group only. It does not modify `lakefile.lean` and does not import Mathlib in active Lean modules.

Candidate group:

```text
Mathlib.Data.Set.Basic
Mathlib.Order.Bounds.Basic
Mathlib.Order.ConditionallyCompleteLattice.Basic
Mathlib.Data.Real.Basic
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
