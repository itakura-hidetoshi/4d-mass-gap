# Lower-bound proof body surface CI

Run ID: 25884804104
Audit job ID: 76073541399
Build job ID: 76073559827
Commit: 0e5e2d4700a6e87fe384c3e87580c47430b21212
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
MGAP4D/Spectral/LowerBoundProofBody.lean
MGAP4D/Spectral.lean
MGAP4D.lean
docs/lower_bound_proof_body_surface.md
```

Lower-bound proof-body targets tracked:

```text
normalizedOrthogonalStateCarrier
rayleighEnergyFunctional
positivityEstimate
coerciveEstimate
lowerBoundValueCompatibility
infimumLowerBoundCompatibility
sharpSandwichCompatibility
```

Boundary:

```text
pre-Mathlib lower-bound proof-body surface only
fourth residual-resolution target visible
analytic inequality theorem body not yet replaced
final theorem release not opened
Mathlib on main not introduced
public theorem boundary held
```
