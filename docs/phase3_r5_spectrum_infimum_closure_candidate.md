# Phase 3: R5 Spectrum / Infimum Closure-Candidate Checkpoint

This document records the route-specific hardening checkpoint for R5 after the Mathlib main-adoption hold decision.

## Current invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R5 dry-run succeeded on a scoped branch
R5 spectrum / infimum theorem route remains review-gated
```

## Purpose

The purpose of this checkpoint is to make the R5 spectrum / infimum route enter a closure-candidate surface without claiming theorem completion.

## Closure-candidate requirements

```text
R5 spectrum milestone is present
R5 spectrum skeleton bundle is present
spectrum surface remains named
infimum bridge remains named
spectrum-to-infimum proof obligations remain visible
R5 route does not infer completion from Mathlib dry-run success
R5 remains upstream of R6--R7 review-gated routes
public theorem boundary remains held
```

## Non-claim boundary

This checkpoint does not claim that the spectrum / infimum theorem is complete.

It only records that R5 now has a specific closure-candidate checkpoint that can be hardened in later passes.

## Next action

Wire a Lean-side R5 spectrum / infimum closure-candidate checkpoint through the R5 theorem root and top-level root while preserving the pre-Mathlib invariant.
