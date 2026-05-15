# Mathlib Hilbert Rayleigh quotient theorem body CI

Run ID: 25900716843
Audit job ID: 76123291722
Build job ID: 76123299235
Commit checked out by CI: dce72ed4832fd4fb33f4facd1fd32222dc164623
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
MGAP4D/MathlibAnalytic/HilbertRayleighQuotientTheorem.lean
MGAP4D/MathlibAnalytic/ExactGapPostInterfaceResidualMap.lean
MGAP4D/MathlibAnalytic.lean
docs/mathlib_hilbert_rayleigh_quotient_theorem.md
```

Theorem body checked:

```text
HilbertRayleighQuotientData
HilbertRayleighQuotientData.ready
HilbertRayleighQuotientData.rayleighQuotient
hilbert_rayleigh_quotient_eq
hilbert_rayleigh_quotient_lower_bound
hilbert_rayleigh_quotient_witness_attains
hilbert_rayleigh_quotient_normSq_pos
singletonHilbertRayleighQuotientData
singleton_hilbert_rayleigh_quotient_data_ready
singleton_hilbert_rayleigh_quotient_lower_bound
singleton_hilbert_rayleigh_quotient_witness_attains
HilbertRayleighQuotientReviewSurface
hilbertRayleighQuotientReviewSurface
hilbert_rayleigh_quotient_review_surface_ready
```

Meaning:

```text
Rayleigh quotient theorem body is explicit
numerator is explicit
norm squared denominator is explicit
positive denominator condition is explicit
quotient = numerator / normSq is explicit
witness quotient attains 33/20
all admissible states satisfy the Rayleigh quotient lower bound
quotient theorem body is closed at abstract theorem-body level
```

Boundary preserved:

```text
abstract Rayleigh quotient theorem body only
not yet concrete infinite-dimensional Hilbert-space realization
not yet full self-adjoint H_phys theorem
not final theorem release
public theorem boundary held
```
