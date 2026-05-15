# Mathlib spectral theorem integration interface CI

Run ID: 25894607549
Audit job ID: 76104942558
Build job ID: 76104954517
Commit checked out by CI: 0bf756ffc72204e191b80522133d7a5c685ca923
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
MGAP4D/MathlibAnalytic/SpectralTheoremInterface.lean
MGAP4D/MathlibAnalytic/SelfAdjointHPhysInterface.lean
MGAP4D/MathlibAnalytic.lean
docs/mathlib_spectral_theorem_interface.md
```

Surface checked:

```text
SpectralTheoremInterface
SpectralTheoremInterface.ready
singletonSpectralTheoremInterface
singleton_spectral_theorem_interface_ready
singleton_spectral_theorem_interface_exact_in_support
singleton_spectral_theorem_interface_support_lower_bound
singleton_spectral_theorem_interface_positive_mass
singleton_spectral_theorem_interface_nonzero_mass
SpectralTheoremReviewSurface
spectralTheoremReviewSurface
spectral_theorem_review_surface_ready
```

Meaning:

```text
H_phys interface is linked to a spectral support surface
exact value 33/20 belongs to spectral support
all spectral support values are bounded below by 33/20
positive mass exists at 33/20
mass at 33/20 is nonzero
self-adjoint H_phys interface is linked to spectral theorem interface
main is Mathlib-backed
final release remains held
```

Boundary preserved:

```text
spectral-support/mass interface only
not yet full spectral theorem for an unbounded self-adjoint operator
not yet full projection-valued-measure theorem
final theorem release not opened
public theorem boundary held
```
