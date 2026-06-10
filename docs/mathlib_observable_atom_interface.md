# Mathlib observable atom interface

Branch: main

This note records the observable-facing positive spectral-weight interface after the PVM exact atom surface.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/ObservableAtomInterface.lean
MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean
MGAP4D/MathlibAnalytic.lean
```

## Added surface

```text
MathlibAnalytic.ObservableAtomInterface
MathlibAnalytic.ObservableAtomInterface.ready
MathlibAnalytic.PrototypeObservable
MathlibAnalytic.prototypeObservable
MathlibAnalytic.prototypeObservableSpectralWeight
MathlibAnalytic.singletonObservableAtomInterface
MathlibAnalytic.singleton_observable_atom_interface_ready
MathlibAnalytic.singleton_observable_atom_interface_exact_in_atom
MathlibAnalytic.singleton_observable_atom_interface_positive_weight
MathlibAnalytic.singleton_observable_atom_interface_nonzero_weight
MathlibAnalytic.singleton_observable_atom_interface_compatible_with_pvm
MathlibAnalytic.ObservableAtomReviewSurface
MathlibAnalytic.ObservableAtomReviewSurface.ready
MathlibAnalytic.observableAtomReviewSurface
MathlibAnalytic.observable_atom_review_surface_ready
MathlibAnalytic.observable_atom_review_surface_final_release_held
```

## Final physical carrier routing

```text
PrototypeObservable is now a compatibility alias for FinalPhysicalHilbertCarrier.
prototypeObservable is finalPhysicalHilbertZero.
singletonObservableAtomInterface.observable is FinalPhysicalHilbertCarrier.
singletonObservableAtomInterface.chosenObservable is finalPhysicalHilbertZero.
The observable atom surface is routed through the final countable-coordinate physical Hilbert carrier, not a shell-only prototype carrier.
```

## Meaning

```text
PVM exact atom interface is linked to an observable spectral-weight surface
observable carrier is explicit and final-physical-carrier routed
chosen observable is explicit and final-physical-carrier routed
compact-support / centered / smeared witnesses are explicit
exact atom {33/20} is explicit
33/20 belongs to the exact atom
observable spectral weight at the exact atom is positive
observable spectral weight at the exact atom is nonzero
observable spectral weight is compatible with PVM exact atom mass
main is Mathlib-backed
final release remains held
```

## Boundary

```text
observable-facing interface only
not yet full operator-measure observable atom theorem
not yet compactly supported plaquette construction theorem
not yet full PVM theorem
final theorem release not opened
public theorem boundary held
```
