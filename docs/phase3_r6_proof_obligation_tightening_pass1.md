# Phase 3: R6 Proof-Obligation Tightening Pass 1

This document records the first tightening pass for the R6 interval-exclusion proof-obligation surface.

## Source state

```text
R5 proof-obligation tightening closure: CI green
R6 proof-obligation tightening segment selection: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Tightening pass 1 scope

This pass separates the R6 interval-exclusion obligation surface into:

```text
R5 bridge obligation
vacuum-side obligation
excited-side obligation
interval-boundary obligation
interval-exclusion target obligation
Mathlib request boundary
status compatibility boundary
upstream R5 review dependency
downstream R7 review gate
public-boundary obligation
```

## Non-claim boundary

This pass does not claim R6 theorem completion.

It does not unlock R7 theorem completion, final gap theorem release, or Mathlib adoption on main.

## Next action

Create a Lean-side R6 proof-obligation tightening pass 1 checkpoint and wire it through the R6 theorem root and top-level root.
