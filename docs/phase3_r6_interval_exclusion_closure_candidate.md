# Phase 3: R6 Interval-Exclusion Closure-Candidate Checkpoint

This document records the route-specific hardening checkpoint for R6 after the Mathlib main-adoption hold decision.

## Current invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R6 dry-run succeeded on a scoped branch
R6 interval-exclusion theorem route remains review-gated
```

## Purpose

The purpose of this checkpoint is to make the R6 interval-exclusion route enter a closure-candidate surface without claiming theorem completion.

## Closure-candidate requirements

```text
R6 interval milestone is present
R6 interval skeleton bundle is present
interval surface remains named
exclusion boundary remains named
interval-exclusion proof obligations remain visible
R6 route does not infer completion from Mathlib dry-run success
R6 remains downstream of R5 spectrum / infimum and upstream of R7 atom / exact-gap
public theorem boundary remains held
```

## Non-claim boundary

This checkpoint does not claim that the interval-exclusion theorem is complete.

It only records that R6 now has a specific closure-candidate checkpoint that can be hardened in later passes.

## Next action

Wire a Lean-side R6 interval-exclusion closure-candidate checkpoint through the R6 theorem root and top-level root while preserving the pre-Mathlib invariant.
