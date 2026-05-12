# Phase 3: R7 Atom / Exact-Gap Closure-Candidate Checkpoint

This document records the route-specific hardening checkpoint for R7 after the Mathlib main-adoption hold decision.

## Current invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R7 dry-run succeeded on a scoped branch
R7 atom / exact-gap theorem route remains review-gated
```

## Purpose

The purpose of this checkpoint is to make the R7 atom / exact-gap route enter a closure-candidate surface without claiming theorem completion or final value release.

## Closure-candidate requirements

```text
R7 atom / exact milestone is present
R7 atom / exact skeleton bundle is present
atom surface remains named
exact-gap surface remains named
final-value boundary remains review-gated
atom / exact-gap proof obligations remain visible
R7 route does not infer completion from Mathlib dry-run success
R7 remains downstream of R5 spectrum / infimum and R6 interval-exclusion
public theorem boundary remains held
```

## Non-claim boundary

This checkpoint does not claim that the atom / exact-gap theorem or final value theorem is complete.

It only records that R7 now has a specific closure-candidate checkpoint that can be hardened in later passes.

## Next action

Wire a Lean-side R7 atom / exact-gap closure-candidate checkpoint through the R7 theorem root and top-level root while preserving the pre-Mathlib invariant.
