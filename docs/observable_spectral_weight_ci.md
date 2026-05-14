# Observable spectral weight CI

Run ID: 25855156521
Audit job ID: 75971051521
Build job ID: 75971071421
Commit: 77beddef92d7b5629dd77d8273cfe49523f8af12
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
MGAP4D/Plaquette/ObservableSpectralWeight.lean
MGAP4D/Plaquette.lean
docs/observable_spectral_weight.md
```

Boundary:

```text
pre-Mathlib structural observable spectral weight only
R1--R7 theorem completions not claimed
Mathlib on main not introduced
public theorem boundary held
```
