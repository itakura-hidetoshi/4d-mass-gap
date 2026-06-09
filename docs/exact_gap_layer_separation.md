# Exact gap layer separation note

This note fixes the most important external-review distinction around the value `33/20`.

The repository intentionally separates four layers:

```text
1. abstract theorem-body layer
2. normalized carrier layer
3. spectral receipt layer
4. engineering / review-marker layer
```

The canonical Lean map is:

```text
MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean
```

Primary summary theorem:

```text
exact_gap_layer_separation_ready
```

## 1. Abstract theorem-body layer

Lean anchor:

```text
ExactGapAbstractTheoremBodyLayerReady
exact_gap_abstract_theorem_body_layer_ready
```

This layer contains theorem-body readiness and observable-weight theorem facts from the abstract theorem route:

```text
Hilbert Rayleigh quotient theorem body
self-adjoint H_phys theorem body
spectral theorem theorem body
PVM theorem body
observable atom theorem body
compact plaquette construction theorem body
operator-measure compatibility theorem body
observable spectral weight positive / nonzero / equal to PVM mass
```

This layer deliberately excludes:

```text
exactGapValueReal := 33 / 20
spectral receipt alignment
StillOpen markers
publicBoundaryHeld / finalReleaseHeld markers
```

## 2. Normalized carrier layer

Lean anchor:

```text
ExactGapCarrierLayerReady
exact_gap_carrier_layer_ready
```

This layer contains:

```text
exactGapValueReal = 33 / 20
0 < exactGapValueReal
```

Source files:

```text
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
```

These are carrier checks. The local proofs by `rfl` and `norm_num` do not by themselves constitute a non-definitional Hamiltonian/spectral derivation.

## 3. Spectral receipt layer

Lean anchor:

```text
ExactGapSpectralReceiptLayerReady
exact_gap_spectral_receipt_layer_ready
```

This layer contains the current installed spectral receipt:

```text
YangMillsHamiltonianSpectralDerivation3320.ready
exactGapValueReal = derivedHamiltonianSpectralValue
derivedHamiltonianSpectralValue = 33 / 20
0 < spectralMassRealSurface.mass
spectralMassRealSurface.mass ≠ 0
continuum_hamiltonian_witness_provenance_map_ready
```

Source files:

```text
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessProvenance.lean
```

Important review reading:

```text
current spectral receipt = carrier-aligned spectral-route receipt
not yet = independent operator-theoretic construction of a spectral value followed by a calculation reducing it to 33/20
```

A stronger future proof lane may replace the carrier-aligned receipt by a genuinely independent spectral-value construction. That would be a new theorem-body surface, not merely a documentation rename.

## 4. Engineering / review-marker layer

Lean anchor:

```text
ExactGapEngineeringMarkerLayerReady
exact_gap_engineering_marker_layer_ready
```

This layer contains state markers historically mixed into closure records:

```text
allAbstractTheoremBodiesClosed
concreteHilbertRealizationStillOpen
concreteUnboundedOperatorStillOpen
concreteSpectralMeasureStillOpen
concretePVMStillOpen
concreteLatticeGaugePlaquetteStillOpen
concreteOperatorMeasureRealizationStillOpen
finalReleaseHeld
publicBoundaryHeld
```

These are review-state / boundary markers. They are not additional mathematical theorem bodies.

## Why this matters

Without this separation, external reviewers may reasonably confuse:

```text
carrier equality by rfl
spectral-route receipt alignment
actual mathematical theorem body
engineering progress marker
```

The correct reading is:

```text
Basic.lean / ExactGapReal.lean
  -> carrier layer

ExactGapTheoremBodyClosure.lean
  -> older mixed closure record

ExactGapLayerSeparation.lean
  -> current separation map

YangMillsHamiltonianSpectralDerivation3320.lean
  -> current spectral receipt layer, not independent spectral-value construction

ContinuumHamiltonianMassGapWitnessProvenance.lean
  -> provenance map from witness slots to upstream theorem anchors
```

## Review rule

When reviewing a claim, first ask which layer it belongs to:

```text
Is this a mathematical theorem-body claim?
Is this a normalized carrier claim?
Is this a spectral receipt / alignment claim?
Is this an engineering marker / boundary claim?
```

Only theorem-body claims should be treated as mathematical substance. Carrier and receipt claims are valid Lean objects, but their mathematical meaning is narrower. Engineering markers are audit-state objects.

## Boundary

This separation improves honesty and auditability. It does not by itself claim independent external mathematical consensus, and it does not claim that documentation replaces Lean theorem bodies or independent mathematical review.
