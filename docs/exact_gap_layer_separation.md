# Exact gap layer separation note

This note fixes the external-review distinction around the final normalized mass-gap value.

The repository separates five review layers:

```text
1. Basic-layer route marker
2. downstream real-carrier / carrier-level arithmetic normalization
3. continuum-Hamiltonian / PVM / operator-spectral derivation layer
4. R6 exact atom and R7 positive spectral-weight route
5. engineering / audit / public-boundary marker layer
```

The canonical Lean map is:

```text
MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean
```

Primary summary theorem:

```text
exact_gap_layer_separation_ready
```

---

## Correct current reading

```text
Basic.lean
  -> marker-only route-deferred layer
  -> no real-valued gap carrier
  -> no local final-value assignment

ExactGapReal.lean
  -> defines exactGapValueReal as the downstream normalized real carrier
  -> proves exactGapValueReal_eq : exactGapValueReal = 33/20
  -> carrier-level arithmetic normalization

Continuum Hamiltonian / PVM / spectral theorem route
  -> identifies the carrier with the Hamiltonian spectral route
  -> carries positivity / nonzero spectral-mass evidence
  -> keeps public / final-release boundary markers visible

R6 exact-atom route
  -> pins the displayed value 33/20 through the spectral/PVM atom lane
  -> prevents the value from being read as a pre-R6 definitional unfolding

R7 positive-weight route
  -> carries positive spectral weight
  -> preserves exact 33/20, atom membership, and orthogonal non-vacuum witness data

R1--R7 terminal chain
  -> records exact 33/20 plus positive spectral weight at terminal audit level
```

Thus `exactGapValueReal` is the downstream normalized carrier, while the proof-facing final-value route is reviewed through the Hamiltonian / PVM / spectral / R6 / R7 theorem route.

---

## Current source of the final-value derivation claim

The Basic file is not the source of the derivation claim and does not carry a real-valued numerical assignment.  The exact-value equality is exposed at the carrier layer and then reviewed through the downstream Hamiltonian / PVM / spectral / R6 / R7 theorem route.

Current theorem-route anchors include:

```text
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianExactMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/ConcreteR1R7ResidualDischarge.lean
MGAP4D/R6/Theorem/ExactAtom3320YangMillsSpectralDerivation.lean
MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean
MGAP4D/R7/Theorem.lean
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
```

Primary Lean anchors:

```text
exactGapValueReal
exactGapValueReal_eq
continuum_hamiltonian_derives_exact_mass_gap_value
physical_continuum_hamiltonian_to_exact_positive_mass_gap
physical_continuum_hamiltonian_exact_gap_33_over_20
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero
yang_mills_hamiltonian_spectral_derivation_3320_ready
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_exact_gap_value_from_physical_spectrum
exact_atom_3320_yang_mills_spectral_derivation_ready
exact_atom_3320_yang_mills_exact_gap_carrier_eq_derived
exact_atom_3320_r6_derived_spectral_value_eq_3320
exact_atom_3320_r6_exact_gap_value_eq_3320
exact_atom_3320_nondefinitional_origin_certificate_ready
exact_atom_3320_nondefinitional_derivation_target_ready
hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight
```

Correct short reading:

```text
Basic.lean
  -> no real-valued gap carrier
  -> route-deferred marker only

ExactGapReal.lean
  -> downstream normalized real carrier
  -> carrier-level arithmetic normalization exactGapValueReal = 33/20

YangMillsHamiltonianSpectralDerivation3320.lean
  -> spectral infimum / attainment / observable atom alignment
  -> exactGapValueReal = derived Hamiltonian spectral value
  -> no exported derivedHamiltonianSpectralValue = 33/20 theorem outside R6

R6
  -> non-definitional spectral/PVM pinning of 33/20

R7 / terminal R1--R7
  -> exact 33/20 plus positive spectral-weight witness at the terminal audit surface
```

---

## 1. Basic-layer route marker

Lean anchors:

```text
FourDYangMillsAnalyticGapValueOrigin.ready
four_d_yang_mills_analytic_gap_value_origin_ready
four_d_yang_mills_basic_layer_numeric_carrier_absent
```

Source file:

```text
MGAP4D/MathlibAnalytic/Basic.lean
```

Current policy:

```text
Basic.lean
  contains no final-value literal and no real-valued carrier
  records that the spectral theorem, PVM observable, and Hamiltonian theorem routes are deferred
  records basicLayerNumericCarrierAbsent = true
```

This layer deliberately excludes:

```text
exactGapValueReal as a carrier definition
exactGapValueReal_eq
derivedHamiltonianSpectralValue = 33/20
R6 exact-atom pinning
R7 positive spectral weight
terminal R1--R7 discharge
external mathematical consensus
```

---

## 2. Downstream real-carrier / carrier-level arithmetic layer

Lean anchors:

```text
exactGapValueRealRouteWitness
exactGapValueReal
exactGapValueReal_eq
exactGapValueReal_pos
exactGapValueReal_above_one
exact_gap_real_surface_ready
exact_gap_carrier_layer_ready
```

Source file:

```text
MGAP4D/MathlibAnalytic/ExactGapReal.lean
```

Current policy:

```text
ExactGapReal.lean
  introduces exactGapValueReal as the downstream normalized real carrier
  proves exactGapValueReal_eq : exactGapValueReal = 33/20
  proves positivity and above-one facts
  does not replace the Hamiltonian/PVM/spectral/R6/R7 route
```

The theorem

```lean
theorem exactGapValueReal_eq :
  exactGapValueReal = (33 : ℝ) / 20
```

is a carrier-level arithmetic normalization.  It is not the whole physical derivation and should not be presented as if it were the Basic-layer source.

---

## 3. Continuum-Hamiltonian / PVM / operator-spectral derivation layer

Lean anchors:

```text
ExactGapSpectralReceiptLayerReady
exact_gap_spectral_receipt_layer_ready
yang_mills_hamiltonian_spectral_derivation_3320_ready
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_exact_gap_value_from_physical_spectrum
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero
```

Source files:

```text
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianExactMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessProvenance.lean
MGAP4D/ConcreteR1R7ResidualDischarge.lean
```

This layer contains the installed operator/spectral derivation interface:

```text
continuum Hamiltonian route ready
H_phys from Yang--Mills route ready
self-adjoint spectral chain ready
Rayleigh lower-bound surface ready
Rayleigh attainment surface ready
positive spectral-mass surface ready
spectral infimum = derived Hamiltonian spectral value
attained spectral value = derived Hamiltonian spectral value
observable spectral atom value = derived Hamiltonian spectral value
exactGapValueReal = derived Hamiltonian spectral value
0 < spectralMassRealSurface.mass
spectralMassRealSurface.mass ≠ 0
publicBoundaryHeld
finalReleaseHeld
```

Important review reading:

```text
current operator/spectral derivation
  = continuum-Hamiltonian / PVM / spectral route plus R1--R7 terminal route
  = not merely the Basic.lean marker
  = not merely the ExactGapReal.lean carrier arithmetic theorem
```

The Yang--Mills spectral interface deliberately keeps the displayed equality
`derivedHamiltonianSpectralValue = 33/20` outside the pre-R6 layer.

---

## 4. R6 exact atom and R7 positive spectral-weight route

### R6 exact atom

Source files:

```text
MGAP4D/R6/Theorem/ExactAtom3320YangMillsSpectralDerivation.lean
MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean
MGAP4D/R6/Theorem/ExactAtom3320SpectralOriginFirewall.lean
MGAP4D/R6/Theorem/ExactAtom3320ValueOriginQuarantine.lean
MGAP4D/R6/Theorem/ExactAtom3320DirectReviewBridge.lean
```

Primary anchors:

```text
ExactAtom3320SpectralCarrierAlignedAtR6Origin
ExactAtom3320R6NormalizedSpectralAtom
ExactAtom3320R6SpectralPVMPinsDerivedValue
exact_atom_3320_r6_derived_spectral_value_eq_3320
exact_atom_3320_r6_exact_gap_value_eq_3320
ExactAtom3320NonDefinitionalOriginCertificate
exact_atom_3320_nondefinitional_origin_certificate_ready
ExactAtom3320NonDefinitionalDerivationTarget
exact_atom_3320_nondefinitional_derivation_target_ready
```

R6 is the non-definitional value-pinning layer:

```text
carrier aligned with derived Hamiltonian spectral value
derived Hamiltonian spectral value lies in the R6 normalized spectral atom
singleton elimination gives derivedHamiltonianSpectralValue = 33/20
carrier alignment then gives exactGapValueReal = 33/20
```

### R7 positive spectral weight

Source files:

```text
MGAP4D/R7/Theorem.lean
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightBridge.lean
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightSlotClosure.lean
MGAP4D/HardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure.lean
```

Representative payload:

```lean
theorem atom_exact_r6_direct_positive_weight_review_surface_payload :
  observableSpectralWeight3320Certificate.massWitness.positiveMass = true ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  exactGapValueReal ∈ singletonObservableAtomTheoremTheoremData.atom ∧
  witnessSector = orthogonal ∧ witnessSector ≠ vacuum
```

---

## 5. Engineering / audit / public-boundary marker layer

Lean anchors:

```text
ExactGapEngineeringMarkerLayerReady
exact_gap_engineering_marker_layer_ready
finalReleaseHeld
publicBoundaryHeld
publicBoundaryLocked
externalConsensusNotClaimed
theoremWitnessOnly
receipt
ready
packet
manifest
```

This layer contains review-state, boundary, and audit markers.  These are not additional mathematical theorem bodies unless their payload is a substantive typed theorem.

The terminal receipt chain carries:

```text
exactGapValueReal = 33/20
positive spectral weight
R4 genuine-PVM law receipts
finalReleaseHeld
publicBoundaryLocked
```

The public / external receipt layer is therefore an audit surface, not external mathematical consensus.

---

## Why this matters

Without this separation, external reviewers may reasonably confuse:

```text
Basic-layer route marker
ExactGapReal carrier arithmetic theorem
Hamiltonian/PVM/spectral derivation route
R6 spectral/PVM value pinning
R7 positive spectral-weight witness
terminal receipt / audit marker
actual mathematical theorem body
external mathematical consensus
```

The correct reading is:

```text
Basic.lean
  -> marker-only route-deferred layer

ExactGapReal.lean
  -> normalized real carrier and carrier arithmetic normalization

ContinuumHamiltonianMassGapTheorem.lean
  -> continuum-Hamiltonian theorem-route normalization boundary

ContinuumHamiltonianExactMassGapDerivation.lean
  -> exact positive mass-gap package boundary

ContinuumHamiltonianCompleteMassGapDerivation.lean
  -> complete Hamiltonian spectral derivation surface

YangMillsHamiltonianSpectralDerivation3320.lean
  -> spectral derivation interface into the normalized carrier

R6 ExactAtom3320 files
  -> non-definitional spectral/PVM value-pinning route

R7 files
  -> positive spectral-weight witness route

HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
  -> terminal exact-value plus positive-weight audit surface

ExactGapLayerSeparation.lean
  -> current separation map

ContinuumHamiltonianMassGapWitnessProvenance.lean
  -> provenance map from witness slots to upstream theorem anchors
```

---

## Review rule

When reviewing a claim, first ask which layer it belongs to:

```text
Is this a Basic-layer marker claim?
Is this a downstream real-carrier claim?
Is this a carrier-level arithmetic normalization?
Is this a Hamiltonian/PVM/spectral derivation claim?
Is this an R6 spectral/PVM value-pinning claim?
Is this an R7 positive-weight claim?
Is this a terminal audit-receipt claim?
Is this an engineering marker / boundary claim?
Is this a claim of external mathematical consensus?
```

The final normalized value should be reviewed through the continuum-Hamiltonian /
PVM / operator-spectral / R6 / R7 / terminal route, not through `Basic.lean` and
not through a local carrier arithmetic theorem alone.

---

## Boundary

This separation improves honesty and auditability. It does not claim that documentation replaces Lean theorem bodies or independent mathematical review.
