# Mathlib Rayleigh attainment real surface CI

PR: #10
Branch: mathlib-adoption/exact-gap-analytic
Run ID: 25889393176
Audit job ID: 76088931341
Build job ID: 76088943132
Head commit: 1dbdcdf6942a0eb5c29b25c4d5d3232f1ba75f5d
PR merge commit checked out by CI: e59427619f5d51b4291098e3743a02de91907026
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
MGAP4D/MathlibAnalytic/RayleighAttainmentReal.lean
MGAP4D/MathlibAnalytic/RayleighLowerBoundReal.lean
MGAP4D/MathlibAnalytic/GapInfimumReal.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D.lean
docs/mathlib_rayleigh_attainment_real_surface.md
```

Surface checked:

```text
RayleighAttainsExactGap energy := RayleighEnergyAdmissible energy and energy = 33/20
33/20 attains the Rayleigh lower-bound prototype
there exists an admissible Rayleigh energy attaining the exact gap
any attaining energy has value 33/20
```

Boundary:

```text
Mathlib-backed Rayleigh attainment real surface is green on PR #10 / adoption branch
not yet full Hilbert-space eigenvector/Rayleigh theorem
main remains pre-Mathlib
final theorem release not opened
public theorem boundary held
analytic replacement remains review-gated
```
