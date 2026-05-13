# Phase 3: R1--R2 Proof-Obligation Tightening Bridge

This document records the R1--R2 gap discovered after the R3--R7 proof-obligation tightening closure sequence.

## Observation

```text
R1 Hilbert route: theorem candidate / checklist / proof-obligation map / skeleton / bundle / milestone exist.
R2 self-adjoint restriction route: theorem candidate / checklist / proof-obligation map / skeleton / bundle / milestone exist.
R1 and R2 were included in the R1--R7 scoped Mathlib dry-run series.
R1 and R2 were not included in the R3--R7 proof-obligation tightening closure series.
```

## Correction

R1 and R2 must be treated as foundational proof-obligation routes before any future final theorem release gate can open.

This bridge does not claim R1 theorem completion.

This bridge does not claim R2 theorem completion.

This bridge does not open the final gap theorem release.

## Required next surfaces

```text
R1 Hilbert proof-obligation tightening review required
R2 restriction proof-obligation tightening review required
R1--R2 bridge review required before final theorem release gate opening
R1--R7 closure series review required before any release tag proposal
```

## Invariant

```text
main remains pre-Mathlib
Mathlib on main remains not introduced
main-adoption decision remains hold_main_adoption
final gap theorem release is not unlocked
public theorem boundary remains held
```
