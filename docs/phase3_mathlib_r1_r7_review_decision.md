# Phase 3: R1--R7 Mathlib Dry-Run Review Decision

This document records the review decision after the complete R1--R7 scoped Mathlib dry-run series.

## Reviewed inputs

```text
R1 Hilbert dry-run: success
R2 restriction dry-run: success
R3 shifted / zero-form dry-run: success
R4 lower-bound dry-run: success
R5 spectrum / infimum dry-run: success
R6 interval-exclusion dry-run: success
R7 atom / exact-gap dry-run: success
R1--R7 dry-run series review: recorded
Mathlib main-adoption review gate: recorded
main CI after review gates: green
```

## Decision

```text
hold_main_adoption
```

Mathlib must not be introduced into `main` automatically from the dry-run series.

## Reason

The dry-run series establishes that the scoped Mathlib contact surface is buildable on dry-run branches. It does not establish theorem completion, public theorem release, or permission to mutate `main` with a Mathlib dependency.

## Current state

```text
main remains pre-Mathlib
lakefile.lean on main remains unchanged for Mathlib
all dry-run PRs remain draft/unmerged unless separately decided
public theorem claims remain review-gated
R3--R7 theorem routes remain deferred/review-gated
```

## Allowed next branches

```text
continue theorem hardening on main without Mathlib
create a separate Mathlib adoption proposal branch
close successful dry-run PRs without merge
keep successful dry-run PRs as draft references
```

## Forbidden next step

```text
merge Mathlib into main solely because R1--R7 dry-runs succeeded
```

## Review conclusion

The correct current action is to hold main adoption, preserve the pre-Mathlib invariant, and continue proof hardening or prepare a separate explicit adoption proposal.
