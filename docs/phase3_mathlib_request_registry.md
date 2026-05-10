# Phase 3: Mathlib Request Registry

This document records the Mathlib request registry checkpoint.

## Purpose

The project has scoped Mathlib request records for the first eligible theorem-facing layers:

```text
R1 Hilbert
R2 self-adjoint restriction
R4 lower bound
R5 spectrum / infimum
R6 interval exclusion
R7 atom / exact gap
```

The registry gathers those requests into one checked Lean-side surface.

## Added Lean module

```text
MGAP4D/MathlibAdoptionGate/RequestRegistry.lean
```

## Registry role

The registry does not introduce Mathlib. It only records:

- which request records exist;
- whether the request set is complete for the first eligible requesters;
- whether scoped import discipline is preserved;
- whether the public boundary remains held.

## Still not done

This checkpoint does not modify `lakefile.lean` and does not import Mathlib into active Lean modules.

## Next step

After CI is green, define the first concrete theorem-module candidate that may consume the R1 Hilbert request.
