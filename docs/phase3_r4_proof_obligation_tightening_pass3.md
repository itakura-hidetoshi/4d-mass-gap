# Phase 3: R4 Proof-Obligation Tightening Pass 3

This document records the third tightening pass for the R4 lower-bound proof-obligation surface.

## Source state

```text
R4 proof-obligation tightening pass 1: CI green
R4 proof-obligation tightening pass 2: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Tightening pass 3 scope

This pass extracts three review-gated dependency surfaces from the pass 2 links:

```text
upstream R3 review dependency surface
upstream R2 bridge dependency surface
downstream R5--R7 review gate surface
```

## Required boundaries

```text
upstream R3 surface is review-gated
upstream R2 bridge surface is review-gated
downstream R5--R7 surface is review-gated
R4 completion is not inferred from upstream dependency visibility
R5--R7 completion is not inferred from R4 dependency visibility
public theorem boundary remains held
```

## Next action

Create a Lean-side R4 proof-obligation tightening pass 3 checkpoint and wire it through the R4 theorem root and top-level root.
