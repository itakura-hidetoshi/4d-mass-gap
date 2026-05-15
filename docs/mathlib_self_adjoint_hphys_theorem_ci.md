# Mathlib self-adjoint H_phys theorem body CI

Run ID: 25901169205
Audit job ID: 76124608656
Build job ID: 76124616890
Commit checked out by CI: c3c7b915cdbefb7629cebb2ea332fa34bde3302b
Result: success

Status: CI green.

Confirmed jobs:

```text
Audit metadata and Lean source: success
Build Lean project via direct elan: success
```

Build job confirmed steps:

```text
Checkout origin/main: success
Cache elan and Lake build artifacts: success
Show Lean and Lake versions: success
Generate Lake manifest: success
Mathlib post-update cache download: success
lake exe cache get: success
lake build: success
```

Observed toolchain:

```text
Lean: 4.30.0-rc2
Lake: 5.0.0-src+3dc1a08
```

Mathlib evidence from log:

```text
mathlib: running post-update hooks
Using cache from leanprover-community/mathlib4
Downloaded 8297 file(s)
Decompressed 8297 file(s)
lake exe cache get: No files to download
Build completed successfully
```

Artifacts checked by this CI:

```text
MGAP4D/MathlibAnalytic/SelfAdjointHPhysTheorem.lean
MGAP4D/MathlibAnalytic/HilbertRayleighQuotientTheorem.lean
MGAP4D/MathlibAnalytic.lean
docs/mathlib_self_adjoint_hphys_theorem.md
```

Theorem body checked:

```text
SelfAdjointHPhysTheoremData
SelfAdjointHPhysTheoremData.ready
self_adjoint_hphys_symmetric_on_domain
self_adjoint_hphys_domain_closed
self_adjoint_hphys_certificate
self_adjoint_hphys_rayleigh_lower_bound
self_adjoint_hphys_witness_rayleigh_attains
singletonSelfAdjointHPhysTheoremData
singleton_self_adjoint_hphys_theorem_data_ready
singleton_self_adjoint_hphys_symmetric_on_domain
singleton_self_adjoint_hphys_rayleigh_lower_bound
SelfAdjointHPhysTheoremReviewSurface
selfAdjointHPhysTheoremReviewSurface
self_adjoint_hphys_theorem_review_surface_ready
```

Meaning:

```text
operator domain is explicit
H_phys is explicit
symmetry on domain is explicit
domain closure under H_phys is explicit
self-adjointness certificate surface is explicit
Rayleigh quotient compatibility is explicit
witness attains 33/20 through the Rayleigh quotient body
self-adjoint H_phys theorem body is closed at abstract theorem-body level
```

Boundary preserved:

```text
abstract self-adjoint H_phys theorem body only
not yet concrete unbounded operator realization
not yet full spectral theorem integration theorem body
not final theorem release
public theorem boundary held
```
