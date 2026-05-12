# Phase 3: Mathlib Main-Adoption Review Gate

This document defines the review gate that must be satisfied before any Mathlib dependency is introduced into `main`.

## Background

The R1--R7 scoped Mathlib dry-run series has succeeded on separate dry-run branches:

```text
R1 Hilbert path: success
R2 self-adjoint restriction path: success
R3 shifted / zero-form path: success
R4 lower-bound path: success
R5 spectrum / infimum path: success
R6 interval-exclusion path: success
R7 atom / exact-gap path: success
```

Each dry-run PR remains draft/unmerged unless separately reviewed.

## Non-equivalence rule

Dry-run success is not equivalent to main adoption.

```text
dry-run buildability != theorem completion
dry-run buildability != Mathlib-on-main permission
dry-run success != merge permission
```

## Main-adoption review requirements

Before Mathlib can be introduced into `main`, the following review surfaces must be checked:

```text
lakefile scope review
lake-manifest behavior review
import-group minimality review
main-branch theorem route review
public-claim boundary review
rollback / close-dry-run decision review
CI rerun on final adoption branch
```

## Theorem-route status

The following routes remain review-gated and must not be represented as theorem-complete solely from dry-run success:

```text
R3 shifted / zero-form route
R4 lower-bound route
R5 spectrum / infimum route
R6 interval-exclusion route
R7 atom / exact-gap / final-value route
```

## Main invariant before adoption

Until a separate reviewed adoption proposal is created and accepted:

```text
main remains pre-Mathlib
lakefile.lean on main remains unchanged for Mathlib
no active main-branch Lean module imports Mathlib
public theorem claims remain review-gated
all dry-run PRs remain unmerged unless separately decided
```

## Allowed next actions

The allowed next actions are:

```text
keep all dry-run PRs as draft/unmerged
close successful dry-run PRs without merge
create a separate reviewed Mathlib adoption proposal branch
continue theorem-route hardening without Mathlib on main
```

## Forbidden inference

The following inference is forbidden:

```text
R1--R7 dry-run success => introduce Mathlib into main automatically
```

Any main adoption must be a separate, explicit, reviewed decision.
