# Mathlib self-adjoint H_phys interface CI

Run ID: 25893922301
Audit job ID: 76102883135
Build job ID: 76102889779
Commit checked out by CI: 1e6696c3bb44970838003d531cd04c013b66a842
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
MGAP4D/MathlibAnalytic/SelfAdjointHPhysInterface.lean
MGAP4D/MathlibAnalytic/HilbertRayleighInterface.lean
MGAP4D/MathlibAnalytic.lean
docs/mathlib_self_adjoint_hphys_interface.md
```

Surface checked:

```text
SelfAdjointHPhysInterface
SelfAdjointHPhysInterface.ready
singletonSelfAdjointHPhysInterface
singleton_self_adjoint_hphys_interface_ready
singleton_self_adjoint_hphys_interface_symmetric
singleton_self_adjoint_hphys_interface_witness_attains
singleton_self_adjoint_hphys_interface_lower_bound
SelfAdjointHPhysReviewSurface
selfAdjointHPhysReviewSurface
self_adjoint_hphys_review_surface_ready
```

Meaning:

```text
operator carrier is explicit
inner pairing is explicit
H_phys map is explicit
symmetry witness is explicit
Rayleigh interface compatibility is explicit
witness state attains 33/20
all admissible mapped states satisfy the Rayleigh lower bound
Hilbert/Rayleigh interface is linked to operator-shaped H_phys interface
main is Mathlib-backed
final release remains held
```

Boundary preserved:

```text
operator-shaped interface only
not yet full unbounded self-adjoint operator theorem
not yet full spectral theorem integration
not yet full projection-valued-measure theorem
final theorem release not opened
public theorem boundary held
```
