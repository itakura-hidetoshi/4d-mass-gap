# Phase 3: Mathlib PR #1 Close-or-Promote Gate

This document defines the decision gate for PR #1 after the successful Mathlib dry-run.

## Pull request

```text
PR #1: Dry run Mathlib adoption for R1 Hilbert path
branch: feature/mathlib-r1-hilbert-dry-run
```

## Confirmed result

```text
CI #381: success
CI #382: success
R1 Hilbert Mathlib sibling module: buildable
Scoped Mathlib dependency: buildable on dry-run branch
```

## Decision options

There are two safe options:

### Option A: close as successful dry-run

Use this if the purpose was only to test feasibility.

Result:

```text
main remains pre-Mathlib
PR #1 is closed without merge
dry-run result remains recorded
future Mathlib adoption requires a new explicit proposal
```

### Option B: promote to merge proposal

Use this only if the project is ready to let Mathlib enter `main`.

Required before promotion:

```text
review lakefile.lean dependency scope
review lake-manifest.json generation behavior
review R1 Hilbert sibling module imports
confirm status surfaces are preserved
confirm public theorem boundary remains held
confirm CI remains green after final PR head
mark PR ready for review only after the above are satisfied
```

## Forbidden shortcut

The successful dry-run must not be treated as automatic merge authorization.

## Current recommendation

Keep PR #1 as draft until an explicit close-or-promote decision is made.

## Added Lean module

```text
MGAP4D/MathlibAdoptionGate/DryRunCloseOrPromoteGatePR1.lean
```
