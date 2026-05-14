# Mathlib gap-infimum real surface CI

PR: #10
Branch: mathlib-adoption/exact-gap-analytic
Run ID: 25887869731
Audit job ID: 76083940153
Build job ID: 76083951980
Head commit: 24e0d624c2bbf4263abe975577299f6841315e32
PR merge commit checked out by CI: e38b1bd4e5b81a64495e157ec112a397b3402cc5
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
MGAP4D/MathlibAnalytic/GapInfimumReal.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D.lean
docs/mathlib_gap_infimum_real_surface.md
```

Surface checked:

```text
carrier = Set.Ici (33/20 : Real)
33/20 belongs to the carrier
every carrier element is bounded below by 33/20
33/20 is attained
33/20 is positive
```

Boundary:

```text
Mathlib-backed gap-infimum real surface is green on PR #10 / adoption branch
not yet full Hilbert-space Rayleigh theorem
main remains pre-Mathlib
final theorem release not opened
public theorem boundary held
analytic replacement remains review-gated
```
