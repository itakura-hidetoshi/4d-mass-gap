# Phase 3: R4 Proof-Obligation Tightening Pass 2

This document records the second tightening pass for the R4 lower-bound proof-obligation surface.

## Source state

```text
R4 proof-obligation tightening segment selection: CI green
R4 proof-obligation tightening pass 1: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Tightening pass 2 scope

This pass binds the R4 lower-bound surface split from pass 1 to three existing layers:

```text
R4 lower-bound theorem checklist
R4 lower-bound proof-obligation map
R4 lower-bound theorem skeleton
```

## Required three-layer links

```text
lower-bound core: checklist -> obligation map -> theorem skeleton
constant / normalization: checklist -> obligation map -> theorem skeleton
ledger / trace: checklist -> obligation map -> theorem skeleton
operator bridge: checklist -> obligation map -> theorem skeleton
estimate: checklist -> obligation map -> theorem skeleton
upstream R3 review dependency: tightening surface -> theorem skeleton
upstream R2 bridge dependency: checklist -> obligation map -> theorem skeleton
downstream R5--R7 review gate: tightening surface -> theorem skeleton
public-boundary: checklist -> obligation map -> theorem skeleton
```

## Non-claim boundary

This pass does not claim R4 theorem completion.

It only records a stronger trace surface across checklist, proof-obligation map, and theorem skeleton.
