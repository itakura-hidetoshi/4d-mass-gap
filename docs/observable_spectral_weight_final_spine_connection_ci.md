# Observable spectral weight final-spine connection CI

Run ID: 25856481980
Audit job ID: 75975488523
Build job ID: 75975517068
Commit: 93cfde3793c977e9779e472ecaa0bfdc50bdba26
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
MGAP4D/FinalSpine.lean
MGAP4D/Constructive/ObservableSpectralWeightClosure.lean
docs/observable_spectral_weight_final_spine_connection.md
```

Boundary:

```text
pre-Mathlib structural observable-weight final-spine connection only
R1--R7 theorem completions not claimed
Mathlib on main not introduced
public theorem boundary held
```
