# Phase 3: R4 Proof-Obligation Tightening Pass 1

This document records the first tightening pass for the R4 lower-bound proof-obligation surface.

## Source state

```text
R3 proof-obligation tightening closure: CI green
R4 proof-obligation tightening segment selection: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Tightening pass 1 scope

This pass separates the R4 lower-bound obligation surface into:

```text
lower-bound core obligation
constant / normalization obligation
ledger / trace obligation
operator-bridge obligation
estimate obligation
upstream R3 review dependency
upstream R2 bridge dependency
downstream R5--R7 review gate
public-boundary obligation
```

## Non-claim boundary

This pass does not claim R4 theorem completion.

It does not unlock R5--R7 theorem completion, final gap theorem release, or Mathlib adoption on main.

## Next action

Create a Lean-side R4 proof-obligation tightening pass 1 checkpoint and wire it through the R4 theorem root and top-level root.
