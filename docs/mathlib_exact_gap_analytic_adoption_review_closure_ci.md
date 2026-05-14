# Mathlib exact-gap analytic adoption review closure CI

PR: #10
Branch: mathlib-adoption/exact-gap-analytic
Run ID: 25891815740
Audit job ID: 76096456860
Build job ID: 76096464464
Head commit: faf0ac38cdedac889acb6cf7cb207ed29816f41c
PR merge commit checked out by CI: 648fc4ba73a2d6cfece43fd8833cac526a2e724a
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
MGAP4D/MathlibAnalytic/ExactGapAnalyticAdoptionReviewClosure.lean
MGAP4D/MathlibAnalytic/ExactGapAnalyticRealClosure.lean
MGAP4D/MathlibAnalytic.lean
lakefile.lean
docs/mathlib_exact_gap_analytic_adoption_review_closure.md
```

Closure checked:

```text
pre-Mathlib seven-residual closure is ready
Mathlib real analytic closure is ready
Mathlib real analytic closure is CI green
exact value = 33/20
exact value is positive
lower-bound prototype ready
attainment prototype ready
spectral-mass prototype ready
analytic replacement candidate ready
review gate required before main adoption
full Hilbert Rayleigh theorem still open
full projection-valued-measure theorem still open
main boundary preserved
final release held
public boundary held
```

Boundary:

```text
review-gated analytic adoption closure is green on PR #10 / adoption branch
not merged to main
not full Hilbert-space Rayleigh theorem
not full projection-valued-measure theorem
final theorem release not opened
public theorem boundary held
analytic replacement remains review-gated
```
