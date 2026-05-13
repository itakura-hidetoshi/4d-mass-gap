# Phase 3: Entrypoint Naming Convention Final Sync

This document records the final sync for entrypoint naming after ambiguous R2 root wording was replaced.

## Canonical naming

```text
MGAP4D.lean: global top-level Lean root
MGAP4D/Phase3ReleaseGate.lean: global Phase 3 release/replay/source-tree/external-audit gate root
MGAP4D/R2/Theorem.lean: R2 restriction route entrypoint
```

## Global context rule

```text
In global-gate contexts, do not use R2 theorem root.
Use R2 entrypoint for MGAP4D/R2/Theorem.lean.
Use global top-level Lean root for MGAP4D.lean.
Use global Phase 3 gate root for MGAP4D/Phase3ReleaseGate.lean.
```

## Boundary invariant

```text
R2 entrypoint is route-local.
R1--R7 global release/replay/source-tree/external-audit gates are carried by Phase3ReleaseGate.
The full project import root is MGAP4D.lean.
R1--R7 theorem completions are not claimed.
Final gap theorem release is not unlocked.
main remains pre-Mathlib.
```
