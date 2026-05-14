# Mathlib exact-gap analytic real closure CI

PR: #10
Branch: mathlib-adoption/exact-gap-analytic
Run ID: 25890889464
Audit job ID: 76093551182
Build job ID: 76093562357
Head commit: cd733535272bdbfc971c091765b983b348bb18dd
PR merge commit checked out by CI: c98720244403a87f85842c80be8c2de18d70dec8
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
MGAP4D/MathlibAnalytic/ExactGapAnalyticRealClosure.lean
MGAP4D/MathlibAnalytic/SpectralMassReal.lean
MGAP4D/MathlibAnalytic/RayleighAttainmentReal.lean
MGAP4D/MathlibAnalytic/RayleighLowerBoundReal.lean
MGAP4D/MathlibAnalytic/GapInfimumReal.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D.lean
docs/mathlib_exact_gap_analytic_real_closure.md
```

Closure checked:

```text
exact value = 33/20 as Real
0 < 33/20
1 < 33/20
Rayleigh admissible energies are bounded below by 33/20
33/20 attains the Rayleigh prototype
there is positive spectral mass at 33/20
that spectral mass is nonzero
all real analytic prototype surfaces are closed
```

Boundary:

```text
Mathlib-backed exact-gap analytic real closure is green on PR #10 / adoption branch
not yet full Hilbert-space Rayleigh theorem
not yet full projection-valued-measure theorem
main remains pre-Mathlib
final theorem release not opened
public theorem boundary held
analytic replacement remains review-gated
```
