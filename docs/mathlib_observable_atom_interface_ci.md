# Mathlib observable atom interface CI

Run ID: 25898709701
Audit job ID: 76117329200
Build job ID: 76117341885
Commit checked out by CI: 4fd9cd71ae0e03e9a9c29184d48396325a6bc932
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
MGAP4D/MathlibAnalytic/ObservableAtomInterface.lean
MGAP4D/MathlibAnalytic/PVMInterface.lean
MGAP4D/MathlibAnalytic.lean
docs/mathlib_observable_atom_interface.md
```

Surface checked:

```text
ObservableAtomInterface
ObservableAtomInterface.ready
PrototypeObservable
prototypeObservable
prototypeObservableSpectralWeight
singletonObservableAtomInterface
singleton_observable_atom_interface_ready
singleton_observable_atom_interface_exact_in_atom
singleton_observable_atom_interface_positive_weight
singleton_observable_atom_interface_nonzero_weight
singleton_observable_atom_interface_compatible_with_pvm
ObservableAtomReviewSurface
observableAtomReviewSurface
observable_atom_review_surface_ready
```

Meaning:

```text
PVM exact atom interface is linked to an observable spectral-weight surface
observable carrier is explicit
chosen observable is explicit
compact-support / centered / smeared witnesses are explicit
exact atom {33/20} is explicit
33/20 belongs to the exact atom
observable spectral weight at the exact atom is positive
observable spectral weight at the exact atom is nonzero
observable spectral weight is compatible with PVM exact atom mass
main is Mathlib-backed
final release remains held
```

Boundary preserved:

```text
observable-facing interface only
not yet full operator-measure observable atom theorem
not yet compactly supported plaquette construction theorem
not yet full PVM theorem
final theorem release not opened
public theorem boundary held
```
