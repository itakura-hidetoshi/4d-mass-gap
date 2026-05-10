# MGAP4D Migration Checkpoint: Lean CI Green

This checkpoint records the first GitHub migration stage where the repository has:

- release metadata mirrored from the MGAP4D v1.6 Zenodo package;
- manifest verification script;
- Lean forbidden-token audit script;
- direct `elan` GitHub Actions workflow;
- `lake update` and `lake build` running in CI;
- MGAP4D Lean scaffold connected through the top-level `MGAP4D.lean` import root.

## CI status

The workflow `Lean CI Direct Elan` reached a warning-only state after replacing `leanprover/lean-action@v1` with explicit `elan` installation.

The prior blocker:

```text
No lake-manifest.json found. Run lake update to generate manifest
```

was resolved by running:

```bash
lake update
lake build
```

explicitly inside the GitHub Actions workflow.

## Current Lean root imports

```lean
import MGAP4D.Basic
import MGAP4D.Foundation
import MGAP4D.Axioms
import MGAP4D.Certificates
import MGAP4D.Spectral
import MGAP4D.Hamiltonian
import MGAP4D.OSPositivity
import MGAP4D.Plaquette
import MGAP4D.Constructive
import MGAP4D.Audit
import MGAP4D.Release
import MGAP4D.Gap3320
import MGAP4D.FinalSpine
```

## Next migration stage

The next stage should begin moving source files from:

```text
MGAP4D_v1_6_expanded_source_snapshot.zip
```

in small batches, while preserving:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake update
lake build
```

as the required check sequence.
