# Mathlib Hilbert Rayleigh interface CI

Run ID: 25893618729
Audit job ID: 76101966310
Build job ID: 76101975776
Commit checked out by CI: ad68836cd623ce60d052f6366376fea69fe048ba
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
MGAP4D/MathlibAnalytic/HilbertRayleighInterface.lean
MGAP4D/MathlibAnalytic.lean
docs/mathlib_hilbert_rayleigh_interface.md
docs/mathlib_hilbert_rayleigh_interface_ci_target.md
```

Surface checked:

```text
HilbertRayleighInterface
HilbertRayleighInterface.attainsExactGap
HilbertRayleighInterface.ready
singletonHilbertRayleighInterface
singleton_hilbert_rayleigh_interface_ready
singleton_hilbert_rayleigh_interface_attains
singleton_hilbert_rayleigh_interface_lower_bound
HilbertRayleighInterfaceReviewSurface
hilbertRayleighInterfaceReviewSurface
hilbert_rayleigh_interface_review_surface_ready
```

Meaning:

```text
state carrier is explicit
Rayleigh-energy map into Real is explicit
admissibility predicate is explicit
witness state is explicit
witness attains 33/20
all admissible states satisfy the lower bound
real analytic closure is linked to the abstract Hilbert/Rayleigh interface
main is Mathlib-backed
final release remains held
```

Boundary preserved:

```text
interface-level Hilbert/Rayleigh surface only
not yet full Hilbert-space Rayleigh quotient theorem
not yet full self-adjoint H_phys theorem
not yet full spectral theorem integration
not yet full projection-valued-measure theorem
final theorem release not opened
public theorem boundary held
```
