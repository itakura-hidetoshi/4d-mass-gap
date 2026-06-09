# Exact gap layer separation note

This note fixes the external-review distinction around the value `33/20`.

The repository separates four layers:

```text
1. abstract theorem-body layer
2. normalized carrier layer
3. operator/spectral derivation layer
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

## Current source of the `33/20` derivation claim

The carrier file is not the source of the derivation claim.  The current source is the R1--R7 terminal operator/spectral route:

```text
MGAP4D/ConcreteR1R7ResidualDischarge.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
```

Primary Lean anchors:

```text
concrete_r1r7_residual_discharge_3320_ready
concrete_r6_residual_discharge_nondefinitional_spectral_atom_3320
concrete_r7_residual_discharge_positive_spectral_weight_derivation_3320
concrete_r1r7_residual_discharge_exact_gap_value_3320
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
yang_mills_hamiltonian_spectral_derivation_3320_ready
```

Correct reading:

```text
Basic.lean / ExactGapReal.lean
  -> normalized target carrier and arithmetic check

R1--R7 terminal route + complete continuum-Hamiltonian spectral route
  -> derivation route that carries the value 33/20 and positive spectral weight
```

Thus `exactGapValueReal` is the normalized target/codomain used by the derivation, while the proof-facing derivation claim is carried by the R1--R7 / Hamiltonian / PVM / plaquette / spectral-weight route.

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
R1--R7 terminal derivation route
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

These are carrier checks.  The local proofs by `rfl` and `norm_num` identify the normalized codomain value; they are not where the operator/spectral route is reviewed.

## 3. Operator/spectral derivation layer

Lean anchor:

```text
ExactGapSpectralReceiptLayerReady
exact_gap_spectral_receipt_layer_ready
```

This layer contains the installed operator/spectral derivation interface:

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
MGAP4D/ConcreteR1R7ResidualDischarge.lean
```

Important review reading:

```text
current operator/spectral derivation
  = R1--R7 terminal route plus Hamiltonian/PVM/plaquette/spectral-weight route
  = not merely the Basic.lean carrier definition
```

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
R1--R7 operator/spectral derivation route
actual mathematical theorem body
engineering progress marker
```

The correct reading is:

```text
Basic.lean / ExactGapReal.lean
  -> carrier layer

ConcreteR1R7ResidualDischarge.lean
  -> current terminal derivation discharge

ContinuumHamiltonianCompleteMassGapDerivation.lean
  -> complete Hamiltonian spectral derivation surface

YangMillsHamiltonianSpectralDerivation3320.lean
  -> spectral derivation interface into the normalized carrier

ExactGapTheoremBodyClosure.lean
  -> older mixed closure record

ExactGapLayerSeparation.lean
  -> current separation map

ContinuumHamiltonianMassGapWitnessProvenance.lean
  -> provenance map from witness slots to upstream theorem anchors
```

## Review rule

When reviewing a claim, first ask which layer it belongs to:

```text
Is this a mathematical theorem-body claim?
Is this a normalized carrier claim?
Is this an R1--R7 operator/spectral derivation claim?
Is this an engineering marker / boundary claim?
```

The current `33/20` claim should be reviewed through the R1--R7 operator/spectral route, not through the local carrier definition alone.

## Boundary

This separation improves honesty and auditability. It does not claim that documentation replaces Lean theorem bodies or independent mathematical review.
