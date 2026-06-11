# Mathlib concrete Yang-Mills Hamiltonian skeleton

Branch: main

This note records the concrete Yang-Mills Hamiltonian skeleton after the physical unbounded-operator skeleton.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean
MGAP4D/MathlibAnalytic.lean
```

## Added surface

```text
MathlibAnalytic.ConcreteYangMillsHamiltonianSkeletonData
MathlibAnalytic.ConcreteYangMillsHamiltonianSkeletonData.ready
MathlibAnalytic.concrete_ym_hamiltonian_hphys_built_from_ym
MathlibAnalytic.concrete_ym_hamiltonian_plaquette_centered
MathlibAnalytic.concrete_ym_hamiltonian_normalization_bridge
MathlibAnalytic.concrete_ym_hamiltonian_domain_preserved
MathlibAnalytic.concrete_ym_hamiltonian_rayleigh_lower_bound
MathlibAnalytic.concrete_ym_hamiltonian_distinguished_attains_exact
MathlibAnalytic.finalConcreteYangMillsHamiltonianSkeletonData
MathlibAnalytic.final_concrete_ym_hamiltonian_skeleton_ready
MathlibAnalytic.ConcreteYangMillsHamiltonianSkeletonReviewSurface
MathlibAnalytic.ConcreteYangMillsHamiltonianSkeletonReviewSurface.ready
MathlibAnalytic.concreteYangMillsHamiltonianSkeletonReviewSurface
MathlibAnalytic.concrete_ym_hamiltonian_skeleton_review_surface_ready
```

## Final physical carrier route

```text
state := FinalPhysicalHilbertCarrier
ymData := FinalPhysicalHilbertCarrier
domain := finalPhysicalHilbertDomain
H_phys := finalPhysicalHamiltonian
rayleigh := finalPhysicalRayleigh
distinguished := finalPhysicalHilbertZero
```

The concrete Yang-Mills Hamiltonian skeleton is final-name routed without legacy prototype aliases.

Thus the concrete Yang-Mills Hamiltonian skeleton should now be read as a final-physical-carrier routed skeleton, not as a one-point carrier prototype.

## Meaning

```text
physical unbounded-operator skeleton is linked to concrete Yang-Mills Hamiltonian skeleton
Yang-Mills data and witness are explicit
plaquette observable is explicit
coupling and normalization are explicit and positive
H_phys is certified as built from Yang-Mills data
plaquette centered certificate surface is present
normalization bridge is present
Rayleigh lower bound is present
distinguished state attains exact value 33/20
```

## Boundary

```text
concrete Yang-Mills Hamiltonian skeleton only
not yet continuum-limit construction
not yet spectral realization construction
not final theorem release
public theorem boundary held
```
