# Exact gap Mathlib adoption bridge CI

Run ID: 25885928150
Audit job ID: 76077443128
Build job ID: 76077461221
Commit: 8dd25b4763c810856119144a6455ab140cf24299
Result: success

Status: CI green.

Confirmed jobs:

```text
Audit metadata and Lean source: success
Build Lean project via direct elan: success
```

Build job confirmed steps:

```text
Checkout repository: success
Show Lean and Lake versions: success
Generate Lake manifest: success
Build Lean project with lake build: success
```

Observed toolchain:

```text
Lean: 4.30.0-rc2
Lake: 5.0.0-src+3dc1a08
```

Artifacts checked by this CI:

```text
MGAP4D/ExactGapMathlibAdoptionBridge.lean
MGAP4D.lean
docs/exact_gap_mathlib_adoption_bridge.md
```

Boundary:

```text
pre-Mathlib Mathlib-adoption bridge only
seventh residual-resolution target visible
analytic theorem bodies require a separate adoption proposal
final theorem release not opened
Mathlib on main not introduced
public theorem boundary held
```
