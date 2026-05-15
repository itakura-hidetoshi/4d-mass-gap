# Mathlib exact-gap main adoption CI

Run ID: 25892547010
Audit job ID: 76098658751
Build job ID: 76098665897
Commit checked out by CI: 9499cde64c6f43a737892b135cb956b502a6a5a3
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

Main adoption checked:

```text
Mathlib dependency in lakefile.lean
roots := #[`MGAP4D, `MGAP4D.MathlibAnalytic]
MGAP4D/MathlibAnalytic.lean root module
Mathlib exact-gap analytic real closure
Mathlib exact-gap analytic adoption review closure
```

Meaning:

```text
pre-Mathlib boundary is resolved on main for the real-order analytic prototype layer
main is now Mathlib-backed
exact value = 33/20 as Real
Rayleigh lower-bound prototype available
Rayleigh attainment prototype available
positive spectral-mass prototype available
analytic real closure available
adoption review closure available
```

Boundary preserved:

```text
final theorem release remains closed
public theorem boundary remains held
full Hilbert-space Rayleigh theorem remains open
full self-adjoint H_phys theorem remains open
full spectral theorem integration remains open
full projection-valued-measure theorem remains open
observable atom theorem in operator-measure form remains open
```
