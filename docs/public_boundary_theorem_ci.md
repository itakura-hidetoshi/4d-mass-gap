# Public boundary theorem CI

Run ID: 25862297398
Audit job ID: 75995063245
Build job ID: 75995105740
Commit: a760ab5a5f4375b3ab95a0783211d73b3660e57d
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
MGAP4D/Release/PublicBoundaryTheorem.lean
MGAP4D/Release.lean
MGAP4D.lean
docs/public_boundary_theorem.md
```

Boundary:

```text
pre-Mathlib structural public-boundary theorem only
exact-gap theorem surface visible
final theorem release not opened
Mathlib on main not introduced
public theorem boundary held
```
