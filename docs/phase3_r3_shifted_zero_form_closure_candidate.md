# Phase 3: R3 Shifted / Zero-Form Closure-Candidate Checkpoint

This document records the first route-specific hardening checkpoint for R3 after the Mathlib main-adoption hold decision.

## Current invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
R3 dry-run succeeded on a scoped branch
R3 theorem route remains review-gated
```

## Purpose

The purpose of this checkpoint is to separate a closure candidate from a closure claim.

R3 shifted / zero-form is allowed to enter a closure-candidate surface only if the following remain explicit:

```text
shifted route remains named
zero-form route remains named
operator interface boundary remains visible
proof obligations remain visible
downstream dependence on R4--R7 remains visible
public theorem boundary remains held
```

## Non-claim boundary

This checkpoint does not claim that the shifted / zero-form theorem is complete.

It only records that R3 now has a specific closure-candidate checkpoint that can be hardened in later passes.

## Closure-candidate requirements

```text
R3 milestone is present
R3 skeleton bundle is present
R3 proof-obligation surface is not hidden
R3 route does not infer completion from Mathlib dry-run success
R3 downstream dependencies remain review-gated
```

## Next action

Wire a Lean-side R3 closure-candidate checkpoint through the R3 theorem root and top-level root while preserving the pre-Mathlib invariant.
