# Phase 3: R6 Proof-Obligation Tightening Pass 3

This document records the third tightening pass for the R6 interval-exclusion proof-obligation surface.

## Source state

```text
R6 proof-obligation tightening pass 1: CI green
R6 proof-obligation tightening pass 2: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Tightening pass 3 scope

This pass extracts two review-gated dependency surfaces from the pass 2 links:

```text
upstream R5 review dependency surface
downstream R7 review gate surface
```

## Required boundaries

```text
upstream R5 review surface is review-gated
downstream R7 review surface is review-gated
R6 completion is not inferred from upstream R5 dependency visibility
R7 completion is not inferred from R6 dependency visibility
public theorem boundary remains held
```

## Next action

Create a Lean-side R6 proof-obligation tightening pass 3 checkpoint and wire it through the R6 theorem root and top-level root.
