# Gap infimum definition surface CI

Run ID: 25884214940
Audit job ID: 76071557632
Build job ID: 76071584106
Commit: d1db0e8ee3a8e42bbed000f0bc07eaf925ec4eaa
Result: success

Status: CI green.

Confirmed jobs:

```text
Audit metadata and Lean source: success
Build Lean project via direct elan: success
```

Build job confirmed steps:

```text
Checkout repository: success
Show Lean and Lake versions: success
Generate Lake manifest: success
Build Lean project with lake build: success
```

Observed toolchain:

```text
Lean: 4.30.0-rc2
Lake: 5.0.0-src+3dc1a08
```

Artifacts checked by this CI:

```text
MGAP4D/Spectral/GapInfimumDefinition.lean
MGAP4D/Spectral.lean
MGAP4D.lean
docs/gap_infimum_definition_surface.md
```

Gap-infimum targets tracked:

```text
orthogonalSectorCarrier
normalizedStatePredicate
rayleighFunctionalSurface
spectralInfimumSurface
infimumEqualsExactGap
lowerBoundCompatibility
eigenWitnessAttainmentCompatibility
```

Boundary:

```text
pre-Mathlib gap-infimum definition surface only
third residual-resolution target visible
analytic infimum theorem body not yet replaced
final theorem release not opened
Mathlib on main not introduced
public theorem boundary held
```
