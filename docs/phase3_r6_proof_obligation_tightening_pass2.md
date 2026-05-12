# Phase 3: R6 Proof-Obligation Tightening Pass 2

This document records the second tightening pass for the R6 interval-exclusion proof-obligation surface.

## Source state

```text
R6 proof-obligation tightening segment selection: CI green
R6 proof-obligation tightening pass 1: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Tightening pass 2 scope

This pass binds the R6 interval-exclusion surface split from pass 1 to three existing layers:

```text
R6 interval theorem checklist
R6 interval proof-obligation map
R6 interval theorem skeleton
```

## Required three-layer links

```text
R5 bridge: checklist -> obligation map -> theorem skeleton
vacuum-side: checklist -> obligation map -> theorem skeleton
excited-side: checklist -> obligation map -> theorem skeleton
interval-boundary: checklist -> obligation map -> theorem skeleton
interval-exclusion target: checklist -> obligation map -> theorem skeleton
Mathlib request boundary: checklist -> obligation map -> theorem skeleton
status compatibility boundary: checklist -> obligation map -> theorem skeleton
upstream R5 review dependency: tightening surface -> theorem skeleton
downstream R7 review gate: tightening surface -> theorem skeleton
public-boundary: checklist -> obligation map -> theorem skeleton
```

## Non-claim boundary

This pass does not claim R6 theorem completion.

It only records a stronger trace surface across checklist, proof-obligation map, and theorem skeleton.
