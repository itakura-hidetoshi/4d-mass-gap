# Phase 3: R1 Hilbert Scoped Mathlib Request

This document records the first scoped Mathlib request candidate.

## Requester

```text
MathlibRequester.r1Hilbert
```

## Purpose

The R1 Hilbert layer is the first plausible place where real Mathlib infrastructure may become necessary, because future concrete theorem modules may need:

- Hilbert space structures;
- inner product spaces;
- closed subspaces;
- orthogonal complements;
- projections or decomposition lemmas.

## Requested import group

This request records a scoped candidate import group only. It does not yet modify `lakefile.lean` and does not yet import Mathlib in active Lean modules.

Candidate group:

```text
Mathlib.Analysis.InnerProductSpace.Basic
Mathlib.Analysis.InnerProductSpace.Projection
Mathlib.Topology.Algebra.Module.Basic
```

## Gate condition

This request may proceed only if:

```text
MathlibAdoptionGate.MathlibGate.ready
```

is satisfied with pass2 closed, CI green, audit green, scoped imports, preserved status surfaces, and public boundary held.

## Next step

After CI is green, add the Lean-side request record and keep Mathlib deferred until a concrete theorem module demands it.
