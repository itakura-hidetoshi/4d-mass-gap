# Sharp gap sandwich CI

Run ID: 25861499799
Audit job ID: 75992301112
Build job ID: 75992323903
Commit: 8208409941d0c5cbbb499ede965638a0ae253c05
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
MGAP4D/Spectral/SharpGapSandwich.lean
MGAP4D/Spectral.lean
MGAP4D/SharpGapFinalSpineBridge.lean
MGAP4D.lean
docs/sharp_gap_sandwich.md
```

Boundary:

```text
pre-Mathlib structural sharp-gap sandwich only
exact-gap tracking surface visible
final theorem release not opened
Mathlib on main not introduced
public theorem boundary held
```
