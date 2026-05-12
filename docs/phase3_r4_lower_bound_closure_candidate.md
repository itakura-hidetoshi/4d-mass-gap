# Phase 3: R4 Lower-Bound Closure-Candidate Checkpoint

This document records the route-specific hardening checkpoint for R4 after the Mathlib main-adoption hold decision.

## Current invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R4 dry-run succeeded on a scoped branch
R4 lower-bound theorem route remains review-gated
```

## Purpose

The purpose of this checkpoint is to make the R4 lower-bound route enter a closure-candidate surface without claiming theorem completion.

## Closure-candidate requirements

```text
R4 lower-bound milestone is present
R4 lower-bound skeleton bundle is present
lower-bound obligation surface remains visible
R4 route does not infer completion from Mathlib dry-run success
R4 lower-bound route remains upstream of R5--R7 review-gated routes
public theorem boundary remains held
```

## Non-claim boundary

This checkpoint does not claim that the lower-bound theorem is complete.

It only records that R4 now has a specific closure-candidate checkpoint that can be hardened in later passes.

## Next action

Wire a Lean-side R4 lower-bound closure-candidate checkpoint through the R4 theorem root and top-level root while preserving the pre-Mathlib invariant.
