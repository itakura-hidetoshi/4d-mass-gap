# Phase 3: Entrypoint Naming Convention

This document fixes the naming convention for route-local entrypoints and global roots.

## Canonical terms

```text
MGAP4D.lean: global top-level Lean root
MGAP4D/Phase3ReleaseGate.lean: global Phase 3 release/replay/source-tree/external-audit gate root
MGAP4D/R2/Theorem.lean: R2 restriction route entrypoint
```

## Avoided terms

```text
Do not call MGAP4D/R2/Theorem.lean the global root.
Avoid the ambiguous phrase R2 theorem root in global-gate contexts.
Use R2 entrypoint when referring to MGAP4D/R2/Theorem.lean.
Use global top-level Lean root when referring to MGAP4D.lean.
Use global Phase 3 gate root when referring to MGAP4D/Phase3ReleaseGate.lean.
```

## Boundary invariant

```text
R2 entrypoint is route-local.
Global release/replay/source-tree/external-audit gates are carried by Phase3ReleaseGate.
The full project import root is MGAP4D.lean.
R1--R7 theorem completions are not claimed.
Final gap theorem release is not unlocked.
main remains pre-Mathlib.
```
