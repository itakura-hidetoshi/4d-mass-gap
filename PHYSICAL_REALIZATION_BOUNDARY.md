# Physical Realization Boundary

This document clarifies the boundary between MGAP4D Lean proof-architecture surfaces and a full physical continuum Yang--Mills realization.

## Summary

The repository contains review surfaces, bridge surfaces, skeleton surfaces, and target-obligation surfaces. They are intended to keep the Lean architecture buildable and auditable while preserving the public mathematical review boundary.

The important current distinction is:

```text
some early bridge layers still use singleton witnesses for interface closure
physical unbounded-operator skeleton uses the final countable-coordinate physical carrier
concrete Yang--Mills Hamiltonian skeleton is routed through that final physical carrier
spectral and continuum theorem layers remain review-gated skeleton / target surfaces
```

## Current boundary in the Lean source

### Concrete Hilbert realization

Source:

```text
MGAP4D/MathlibAnalytic/ConcreteHilbertRealizationTheorem.lean
```

This file uses a concrete Lean witness for the review surface while preserving explicit boundary markers for the infinite-dimensional physical Hilbert realization.

Relevant boundary markers:

```text
infiniteDimensionalPhysicalHilbertStillOpen
finalReleaseHeld
publicBoundaryHeld
```

### Concrete `H_phys` realization

Source:

```text
MGAP4D/MathlibAnalytic/ConcreteHPhysRealizationTheorem.lean
```

This layer packages the `H_phys` / unbounded-operator realization surface after the concrete Hilbert realization.

Relevant boundary markers:

```text
fullUnboundedPhysicalOperatorStillOpen
publicBoundaryHeld
```

### Physical unbounded-operator skeleton

Source:

```text
MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean
```

This layer now uses:

```text
FinalPhysicalHilbertCarrier
finalPhysicalHamiltonian
finalPhysicalRayleigh
finalPhysicalUnboundedOperatorSkeletonData
```

The compatibility name:

```text
prototypePhysicalUnboundedOperatorSkeletonData
```

is retained for downstream imports, but it aliases the final physical carrier data rather than a singleton carrier.

Relevant boundary markers:

```text
concreteYangMillsHamiltonianStillOpen
publicBoundaryHeld
```

### Concrete Yang--Mills Hamiltonian skeleton

Source:

```text
MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean
```

This layer is routed through:

```text
FinalPhysicalHilbertCarrier
finalPhysicalHamiltonian
finalPhysicalRayleigh
finalConcreteYangMillsHamiltonianSkeletonData
```

The compatibility name:

```text
prototypeConcreteYangMillsHamiltonianSkeletonData
```

is retained for downstream imports, but it aliases the final physical carrier route.

Relevant boundary markers:

```text
continuumLimitStillOpen
spectralRealizationStillOpen
publicBoundaryHeld
```

### Spectral realization skeleton

Source:

```text
MGAP4D/MathlibAnalytic/SpectralRealizationSkeleton.lean
```

This layer packages spectral objects after the concrete Yang--Mills Hamiltonian skeleton, including a spectral projection surface, an exact spectral atom at `33/20`, an observable witness, and positive spectral mass at the exact value.

Relevant boundary markers:

```text
continuumSpectralTheoremStillOpen
finalReleaseHeld
publicBoundaryHeld
```

### Continuum spectral theorem skeleton

Source:

```text
MGAP4D/MathlibAnalytic/ContinuumSpectralTheoremSkeleton.lean
```

This layer carries preservation anchors and explicit review / release boundaries.

Relevant boundary markers:

```text
finalTheoremReleaseStillHeld
publicBoundaryHeld
```

### Physical Hamiltonian normalization bridge

Source:

```text
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
```

This layer records the normalized / dimensional reading:

```text
H_norm = H_phys / E0
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
```

In internal normalized units:

```text
E0 = 1
normalizedGap = exactGapValueReal = 33/20
```

For dimensional reading:

```text
physicalGap_dimensional = E0 * (33/20)
```

### Infinite-dimensional Yang--Mills realization target

Source:

```text
MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean
```

This layer makes the remaining analytic requirements first-class Lean-facing target obligations.

It includes targets for:

```text
infinite-dimensional Hilbert realization
separable Hilbert witness
dense core
domain density
symmetric H_phys
self-adjoint H_phys
gauge-invariant sector
Yang-Mills energy witness
continuum limit
OS positivity
spectral theorem
exact atom
positive plaquette spectral weight
nonempty vacuum-orthogonal sector
normalization preservation
```

Relevant boundary markers:

```text
publicBoundaryHeld
finalReleaseHeld
```

## Correct reading after the physical-carrier hardening

Singleton witnesses that remain in early or still-prototype surfaces are Lean interface witnesses. They should be read together with their boundary markers.

The physical unbounded-operator skeleton and the concrete Yang--Mills Hamiltonian skeleton should now be read as final-physical-carrier routed skeletons, not as one-point carrier skeletons.

The target layer should be read as an analytic proof-obligation map, not as a completed external continuum proof.

## Review rule

A correct review statement is:

```text
The repository provides internal normalized theorem-body and proof-architecture surfaces with replay support, bridge audit support, target obligations, final-physical-carrier routing for the unbounded-operator and concrete Yang--Mills Hamiltonian skeletons, and explicit review boundaries.
```

Use this document together with:

```text
README.md
INDEPENDENT_REPLAY.md
THEOREM_INDEX.md
```
