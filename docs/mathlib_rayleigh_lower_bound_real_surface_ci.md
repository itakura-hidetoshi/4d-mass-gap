# Mathlib Rayleigh lower-bound real surface CI

PR: #10
Branch: mathlib-adoption/exact-gap-analytic
Run ID: 25888646213
Audit job ID: 76086488965
Build job ID: 76086508413
Head commit: 4812292589f0666fa4c30d289d2404bfdb989be0
PR merge commit checked out by CI: 515a0de99469860581dab427d6dca4069c1d9b52
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
MGAP4D/MathlibAnalytic/RayleighLowerBoundReal.lean
MGAP4D/MathlibAnalytic/GapInfimumReal.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D.lean
docs/mathlib_rayleigh_lower_bound_real_surface.md
```

Surface checked:

```text
RayleighEnergyAdmissible energy := energy in Set.Ici (33/20 : Real)
any admissible Rayleigh energy is bounded below by 33/20
33/20 is an admissible Rayleigh energy prototype
33/20 is positive
```

Boundary:

```text
Mathlib-backed Rayleigh lower-bound real surface is green on PR #10 / adoption branch
not yet full Hilbert-space Rayleigh quotient theorem
main remains pre-Mathlib
final theorem release not opened
public theorem boundary held
analytic replacement remains review-gated
```
