# Mathlib spectral-mass real surface CI

PR: #10
Branch: mathlib-adoption/exact-gap-analytic
Run ID: 25889789769
Audit job ID: 76090175553
Build job ID: 76090191471
Head commit: a43157eda66cb3b95e63be8aad7e1d6c48e28024
PR merge commit checked out by CI: 5b24c41bf14c3245d7d14baee505b7118fa5748d
Result: success

Status: CI green.

Confirmed jobs:

```text
Audit metadata and Lean source: success
Build Lean project via direct elan: success
```

Build job confirmed steps:

```text
Checkout PR #10 merge ref: success
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
MGAP4D/MathlibAnalytic/SpectralMassReal.lean
MGAP4D/MathlibAnalytic/RayleighAttainmentReal.lean
MGAP4D/MathlibAnalytic/RayleighLowerBoundReal.lean
MGAP4D/MathlibAnalytic/GapInfimumReal.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D.lean
docs/mathlib_spectral_mass_real_surface.md
```

Surface checked:

```text
exactGapSpectralMassReal = 1
0 < exactGapSpectralMassReal
exactGapSpectralMassReal != 0
PositiveSpectralMassAtExactGap value mass := value = 33/20 and 0 < mass
there exists a positive real spectral mass at 33/20
positive mass is compatible with Rayleigh exact-gap attainment
```

Boundary:

```text
Mathlib-backed spectral-mass real surface is green on PR #10 / adoption branch
not yet full projection-valued-measure theorem
main remains pre-Mathlib
final theorem release not opened
public theorem boundary held
analytic replacement remains review-gated
```
