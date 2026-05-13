# Phase 3: Independent Replay Gate Preparation

This document records the independent replay gate preparation checkpoint after the final theorem release gate preparation refresh was observed green through CI.

## Source state

```text
final theorem release gate preparation refresh: CI green
post-R1--R7 proof-obligation tightening closure: CI green
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
```

## Replay-gate meaning

This checkpoint prepares the independent replay gate. It separates replay readiness from theorem completion and from public final release.

It does not claim theorem completion for R1, R2, R3, R4, R5, R6, or R7.

It does not unlock the final gap theorem release.

It does not introduce Mathlib on main.

## Required independent replay surfaces

```text
clean checkout replay required
lean-toolchain pin required
lake update replay required
lake build replay required
audit scripts replay required
CI log pin required
commit hash pin required
source-tree review required
external audit still required
```

## Non-release invariant

```text
final gap theorem release is not unlocked
public theorem boundary remains held
main remains pre-Mathlib
```

## Next action

Create a Lean-side independent replay gate preparation checkpoint and wire it through the existing import path.
