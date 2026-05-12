# Phase 3: R5 Proof-Obligation Tightening Pass 2

This document records the second tightening pass for the R5 spectrum / infimum proof-obligation surface.

## Source state

```text
R5 proof-obligation tightening segment selection: CI green
R5 proof-obligation tightening pass 1: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Tightening pass 2 scope

This pass binds the R5 spectrum / infimum surface split from pass 1 to three existing layers:

```text
R5 spectrum theorem checklist
R5 spectrum proof-obligation map
R5 spectrum theorem skeleton
```

## Required three-layer links

```text
spectrum set: checklist -> obligation map -> theorem skeleton
spectrum bottom: checklist -> obligation map -> theorem skeleton
witness: checklist -> obligation map -> theorem skeleton
comparison: checklist -> obligation map -> theorem skeleton
infimum: checklist -> obligation map -> theorem skeleton
upstream R4 lower-bound dependency: tightening surface -> theorem skeleton
upstream R3 zero-form dependency: tightening surface -> theorem skeleton
downstream R6--R7 review gate: tightening surface -> theorem skeleton
Mathlib request boundary: checklist -> obligation map -> theorem skeleton
public-boundary: checklist -> obligation map -> theorem skeleton
```

## Non-claim boundary

This pass does not claim R5 theorem completion.

It only records a stronger trace surface across checklist, proof-obligation map, and theorem skeleton.
