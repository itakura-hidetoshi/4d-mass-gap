# Exact gap layer separation note

This note fixes the external-review distinction around the final normalized
mass-gap value.

The repository separates four layers:

```text
1. abstract theorem-body layer
2. Basic-layer route marker and downstream real carrier layer
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

## Current source of the final-value derivation claim

The Basic file is not the source of the derivation claim and does not carry a
real-valued numerical assignment.  The exact-value equality is exposed through
the downstream Hamiltonian / PVM / spectral theorem route.

Current theorem-route anchors include:

```text
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianExactMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/ConcreteR1R7ResidualDischarge.lean
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
```

Primary Lean anchors:

```text
continuum_hamiltonian_derives_exact_mass_gap_value
physical_continuum_hamiltonian_to_exact_positive_mass_gap
physical_continuum_hamiltonian_exact_gap_33_over_20
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
yang_mills_hamiltonian_spectral_derivation_3320_ready
concrete_r1r7_residual_discharge_3320_ready
concrete_r6_residual_discharge_nondefinitional_spectral_atom_3320
concrete_r7_residual_discharge_positive_spectral_weight_derivation_3320
concrete_r1r7_residual_discharge_exact_gap_value_3320
```

Correct reading:

```text
Basic.lean
  -> no real-valued gap carrier
  -> route-deferred marker only

ExactGapReal.lean
  -> downstream real carrier
  -> raw route witness for the carrier
  -> no public final-value equality theorem

Continuum Hamiltonian / PVM / spectral theorem route
  -> derives the final normalized equality and positivity package
```

Thus `exactGapValueReal` is the downstream real carrier used by the derivation,
while the proof-facing final-value claim is carried by the Hamiltonian / PVM /
plaquette / spectral-weight theorem route.

## 1. Abstract theorem-body layer

Lean anchor:

```text
ExactGapAbstractTheoremBodyLayerReady
exact_gap_abstract_theorem_body_layer_ready
```

This layer contains theorem-body readiness and observable-weight theorem facts
from the abstract theorem route:

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
Basic-layer numerical assignment
final-value equality as a carrier definition
R1--R7 terminal derivation route
StillOpen markers
publicBoundaryHeld / finalReleaseHeld markers
```

## 2. Basic-layer marker and downstream real-carrier layer

Lean anchors:

```text
FourDYangMillsAnalyticGapValueOrigin.ready
four_d_yang_mills_analytic_gap_value_origin_ready
four_d_yang_mills_basic_layer_numeric_carrier_absent
ExactGapCarrierLayerReady
exact_gap_carrier_layer_ready
exactGapValueReal
exactGapValueRealRouteWitness
exactGapValueReal_pos
exactGapValueReal_above_one
```

Source files:

```text
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
```

Current policy:

```text
Basic.lean
  contains no final-value literal and no real-valued carrier
  records only that spectral / PVM / Hamiltonian theorem routes are deferred

ExactGapReal.lean
  introduces the real carrier and positivity facts
  exposes a raw route witness so downstream theorem files avoid unstable
  `Classical.choose_spec _` placeholders
  does not export the final normalized equality theorem
```

The final normalized equality is intentionally not treated as a Basic-layer or
early carrier assignment.  It is derived in the continuum Hamiltonian theorem
route.

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
derivedHamiltonianSpectralValue = final normalized value
0 < spectralMassRealSurface.mass
spectralMassRealSurface.mass ≠ 0
continuum_hamiltonian_witness_provenance_map_ready
```

Source files:

```text
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianExactMassGapDerivation.lean
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessProvenance.lean
MGAP4D/ConcreteR1R7ResidualDischarge.lean
```

Important review reading:

```text
current operator/spectral derivation
  = R1--R7 terminal route plus Hamiltonian/PVM/plaquette/spectral-weight route
  = not merely the Basic.lean marker
  = not merely the ExactGapReal.lean carrier witness
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

These are review-state / boundary markers. They are not additional mathematical
theorem bodies.

## Why this matters

Without this separation, external reviewers may reasonably confuse:

```text
Basic-layer route marker
ExactGapReal carrier witness
Hamiltonian/PVM/spectral derivation route
actual mathematical theorem body
engineering progress marker
```

The correct reading is:

```text
Basic.lean
  -> marker-only route-deferred layer

ExactGapReal.lean
  -> real carrier and positivity carrier witness

ContinuumHamiltonianMassGapTheorem.lean
  -> first local continuum-Hamiltonian theorem-route normalization boundary

ContinuumHamiltonianExactMassGapDerivation.lean
  -> exact positive mass-gap package boundary

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
Is this a Basic-layer marker claim?
Is this a downstream real-carrier claim?
Is this a Hamiltonian/PVM/spectral derivation claim?
Is this an engineering marker / boundary claim?
```

The final normalized value should be reviewed through the continuum Hamiltonian /
PVM / operator-spectral theorem route, not through `Basic.lean` and not through a
local carrier definition alone.

## Boundary

This separation improves honesty and auditability. It does not claim that
documentation replaces Lean theorem bodies or independent mathematical review.
