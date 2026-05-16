# Physical Realization Boundary

This document clarifies the boundary between the current MGAP4D Lean proof-architecture surfaces and a full physical continuum Yang--Mills realization.

It is intended to prevent a common external-review misunderstanding: the current `PUnit` / singleton / prototype surfaces are contract witnesses and proof-architecture closures, not a claim that the full infinite-dimensional physical Hilbert-space realization has already been replaced by a one-point model.

## Summary

The current repository contains several internal concrete or prototype surfaces. These surfaces are used to keep the Lean architecture buildable, auditable, and replayable while preserving the public boundary.

They should be read as:

```text
contract witness surfaces
review surfaces
bridge surfaces
skeleton / prototype closures
boundary-preserving Lean artifacts
```

They should not be read as:

```text
a full continuum Yang-Mills construction
a replacement for the physical Hilbert space
a claim that the physical Hamiltonian is literally one-point
a claim that prototype spectral mass is the final physical spectral measure
a public final theorem acceptance claim
```

## Current boundary in the Lean source

### Concrete Hilbert realization

Source:

```text
MGAP4D/MathlibAnalytic/ConcreteHilbertRealizationTheorem.lean
```

This file explicitly states that the concrete one-point realization is used to close the concrete-realization interface in Lean, while the full infinite-dimensional physical Hilbert-space realization remains a visible residual.

The relevant Lean boundary markers include:

```text
infiniteDimensionalPhysicalHilbertStillOpen
finalReleaseHeld
publicBoundaryHeld
```

The singleton object:

```text
singletonConcreteHilbertRealizationTheoremData
```

is therefore a concrete Lean witness for the review surface, not the final physical Hilbert-space model.

### Concrete `H_phys` realization

Source:

```text
MGAP4D/MathlibAnalytic/ConcreteHPhysRealizationTheorem.lean
```

This layer packages the `H_phys` / unbounded-operator realization surface after the concrete Hilbert realization.

Boundary markers include:

```text
fullUnboundedPhysicalOperatorStillOpen
publicBoundaryHeld
```

Thus the current surface is a proof-architecture bridge. It does not erase the distinction between a Lean-carried operator witness and the full physical unbounded Yang--Mills Hamiltonian realization.

### Physical unbounded-operator skeleton

Source:

```text
MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean
```

This layer carries a skeleton for physical unbounded-operator data, including domain preservation, symmetry, self-adjointness certificate surfaces, Rayleigh lower-bound surfaces, and exact-value witnesses.

Boundary markers include:

```text
concreteYangMillsHamiltonianStillOpen
publicBoundaryHeld
```

It is a skeleton surface, not a final continuum construction by itself.

### Concrete Yang--Mills Hamiltonian skeleton

Source:

```text
MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean
```

This layer connects the physical unbounded-operator skeleton to a Yang--Mills Hamiltonian skeleton through named witnesses such as coupling positivity, normalization positivity, plaquette centering, Rayleigh lower-bound, and exact-value preservation.

Boundary markers include:

```text
continuumLimitStillOpen
spectralRealizationStillOpen
publicBoundaryHeld
```

This means the Yang--Mills skeleton is part of the bridge chain and does not by itself claim the full continuum spectral theorem.

### Spectral realization skeleton

Source:

```text
MGAP4D/MathlibAnalytic/SpectralRealizationSkeleton.lean
```

This layer packages spectral objects after the concrete Yang--Mills Hamiltonian skeleton, including a spectral projection surface, an exact spectral atom at `33/20`, an observable witness, and positive spectral mass at the exact value.

The prototype object:

```text
prototypeSpectralRealizationSkeletonData
```

uses singleton carrier / observable surfaces. It is a proof-carrying skeleton.

Boundary markers include:

```text
continuumSpectralTheoremStillOpen
finalReleaseHeld
publicBoundaryHeld
```

Therefore, this surface should not be interpreted as a final public continuum spectral theorem.

### Continuum spectral theorem skeleton

Source:

```text
MGAP4D/MathlibAnalytic/ContinuumSpectralTheoremSkeleton.lean
```

This layer is the continuum spectral theorem skeleton surface. It carries preservation anchors and explicit review / release boundaries.

Boundary markers include:

```text
finalTheoremReleaseStillHeld
publicBoundaryHeld
```

It preserves the distinction between internal skeleton closure and external public theorem release.

### Physical Hamiltonian normalization bridge

Source:

```text
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
```

This layer records the explicit reference energy scale `E0` and the normalized / dimensional reading:

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

For a dimensional physical reading:

```text
physicalGap_dimensional = E0 * (33/20)
```

Boundary markers include:

```text
theoremBodyUnchanged
publicBoundaryHeld
```

Thus the normalized value `33/20` is a dimensionless internal theorem-body surface unless an external reference scale `E0` is supplied.

### Infinite-dimensional Yang--Mills realization target

Source:

```text
MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean
```

This layer is the next evolution step beyond skeleton-only closure. It does not claim that the full physical continuum proof is completed. Instead, it makes the missing analytic requirements first-class Lean objects.

It introduces a target structure:

```text
InfiniteDimensionalYangMillsRealizationTarget
```

and a review surface:

```text
InfiniteDimensionalYangMillsTargetReviewSurface
```

The target layer requires explicit witnesses for:

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

Boundary markers include:

```text
publicBoundaryHeld
finalReleaseHeld
```

Thus this layer is a proof-obligation map from skeleton closure toward physical realization. It strengthens the repository by making the analytic gap visible and auditable, but it does not by itself discharge the full continuum Yang--Mills proof.

## Correct reading of `PUnit` / singleton surfaces

The `PUnit` and singleton constructions are used as Lean-native contract witnesses for the current review surfaces.

They provide:

```text
an explicit carrier for interface closure
an executable witness for replay
stable theorem statements for audit
a way to keep boundary markers present in Lean
```

They do not provide:

```text
the final physical Hilbert space
the final physical domain of H_phys
the final continuum Yang-Mills Hamiltonian
the final physical spectral measure
the final Clay-style public theorem claim
```

The repository intentionally keeps both sides visible:

```text
closed internal review surface
open / held physical public boundary
```

## Correct reading of the infinite-dimensional target layer

The target layer should be read as:

```text
an analytic proof-obligation surface
a promotion checklist for physical realization
a typed target for future theorem hardening
an audit surface for the nontrivial continuum proof gap
```

It should not be read as:

```text
a completed infinite-dimensional Yang-Mills Hamiltonian construction
a completed self-adjointness proof
a completed continuum spectral theorem
a completed nonzero plaquette spectral-weight proof
a completed Clay-style final theorem claim
```

This is the intended evolution: the prior weakness is no longer hidden in prose; it is now named, imported, and audited as an explicit target layer.

## Why this boundary is useful

This design has four review advantages:

1. The repository remains buildable under Lean.
2. The theorem and bridge surfaces remain mechanically auditable.
3. The unresolved physical continuum boundary remains visible instead of being hidden by prose.
4. The next analytic obligations are now named and tracked as Lean-facing target surfaces.

This is why boundary markers such as `publicBoundaryHeld`, `finalReleaseHeld`, and `continuumSpectralTheoremStillOpen` are part of the Lean-facing review surface.

## Review rule

When reviewing this repository, read any singleton / prototype / skeleton / target construction together with its boundary markers.

A correct review statement is:

```text
The current repository provides an internal normalized theorem-body / proof-architecture surface with explicit replay, bridge audit, target obligations, and boundary markers.
```

An incorrect review statement is:

```text
The repository claims that a one-point PUnit model is the final physical Yang-Mills Hilbert space.
```

Another incorrect review statement is:

```text
The infinite-dimensional target layer by itself completes the full continuum Yang-Mills proof.
```

## Relation to other review documents

Use this document together with:

```text
README.md
INDEPENDENT_REPLAY.md
THEOREM_INDEX.md
```

`INDEPENDENT_REPLAY.md` explains how to replay the repository.

`THEOREM_INDEX.md` lists the theorem surfaces, bridge surfaces, and target surfaces to inspect.

This document explains how to interpret the physical-realization boundary while reading those surfaces.
