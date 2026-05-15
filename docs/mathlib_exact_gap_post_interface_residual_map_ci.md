# Mathlib exact-gap post-interface residual map CI

Run ID: 25900374399
Audit job ID: 76122274809
Build job ID: 76122281377
Commit checked out by CI: 9d7233720ece80a4485be2481d4166f0e5159563
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
MGAP4D/MathlibAnalytic/ExactGapPostInterfaceResidualMap.lean
MGAP4D/MathlibAnalytic/ExactGapFullInterfaceClosure.lean
MGAP4D/MathlibAnalytic.lean
docs/mathlib_exact_gap_post_interface_residual_map.md
```

Residual map checked:

```text
full Hilbert-space Rayleigh quotient theorem: open
full unbounded self-adjoint H_phys theorem: open
full spectral theorem integration: open
full projection-valued-measure theorem: open
full observable atom theorem in operator-measure form: open
compactly supported smeared centered plaquette construction theorem: open
operator-measure compatibility theorem: open
```

Meaning:

```text
full interface closure is ready
all open residuals are visible
interface closure alone cannot open final theorem release
public theorem boundary remains held
```

Boundary preserved:

```text
residual map only
not final theorem release
not public theorem release
next step should choose one residual theorem body to close
```
