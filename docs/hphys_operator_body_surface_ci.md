# H_phys operator body surface CI

Run ID: 25883820695
Audit job ID: 76070210067
Build job ID: 76070228292
Commit: 5f9f9fff426cce202a34627ef2748afa68af4cc7
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
MGAP4D/Hamiltonian/OperatorBody.lean
MGAP4D/Hamiltonian.lean
MGAP4D.lean
docs/hphys_operator_body_surface.md
```

Operator-body targets tracked:

```text
denseDomain
vacuumInDomain
orthogonalSectorAdmissible
selfAdjoint
semiboundedBelow
eigenWitnessInDomain
eigenRelationWellTyped
```

Boundary:

```text
pre-Mathlib H_phys operator-body surface only
second residual-resolution target visible
analytic self-adjoint operator theorem bodies not yet replaced
final theorem release not opened
Mathlib on main not introduced
public theorem boundary held
```
