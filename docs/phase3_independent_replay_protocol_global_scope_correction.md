# Phase 3: Independent Replay Protocol Global Scope Correction

This document records the scope correction for the independent replay protocol.

## Corrected scope

```text
IndependentReplayProtocol is global across R1--R7.
IndependentReplayProtocol is carried by MGAP4D/Phase3ReleaseGate.lean.
IndependentReplayProtocol is carried by the top-level MGAP4D.lean root.
IndependentReplayProtocol is not R2-local.
MGAP4D/R2/Theorem.lean is the R2 restriction route entrypoint.
```

## Naming convention

```text
Use MGAP4D.lean for the global top-level Lean root.
Use MGAP4D/Phase3ReleaseGate.lean for the global Phase 3 gate root.
Use MGAP4D/R2/Theorem.lean for the R2 entrypoint, not for a global root.
```

## Invariant

```text
R1--R7 theorem completions are not claimed.
Final gap theorem release is not unlocked.
Mathlib on main remains not introduced.
main remains pre-Mathlib.
public theorem boundary remains held.
```
