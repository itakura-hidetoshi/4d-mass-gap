# Phase 3 Checkpoint: Theorem Surfaces and Global/Concrete Connection

This checkpoint records the current Phase 3 proof-hardening state.

## Completed in this checkpoint

The repository now has theorem-surface layers for:

```text
R1
R2
R3
R4
R5
R6
R7
Global
```

The repository also has a Lean-side dependency map:

```text
MGAP4D/DependencyMap.lean
MGAP4D/DependencyMap/TheoremChain.lean
MGAP4D/DependencyMap/SurfaceEdges.lean
MGAP4D/DependencyMap/GlobalRoute.lean
```

The Global/Concrete layer now has a root and summary surface:

```text
MGAP4D/Global/Concrete.lean
MGAP4D/Global/Concrete/SummarySurface.lean
```

Final assembly now imports:

```lean
import MGAP4D.Global.TheoremSurface
import MGAP4D.Global.Concrete.SummarySurface
```

## Current main route

```text
R1--R7 TheoremSurface
  -> DependencyMap
  -> Global/TheoremSurface
  -> Global/Concrete/SummarySurface
  -> Global/FinalAssembly
```

## Deferred-import restoration completed so far

- Global final audit status connected to Global theorem surface and dependency map
- Review packet status connected to Global theorem surface
- Closure priority status connected to DependencyMap and ProofHardening
- Work-unit audit status files connected to DependencyMap and ProofHardening
- Root manifest status connected to DependencyMap, ProofHardening, and Global theorem surface

## Still deferred

- Mathlib adoption
- theorem-level concrete analytic modules
- status-to-theorem replacement of R1--R7 concrete files
- independent replay beyond current CI
- external review notes

## CI invariant

The intended local replay command is:

```bash
bash scripts/check.sh
```

This runs:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/replay_summary.py
lake update
lake build
```

## Interpretation

This checkpoint is a proof-hardening checkpoint, not a final external-review release. Public theorem-level claims remain review-gated.
