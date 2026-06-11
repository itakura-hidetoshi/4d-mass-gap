# Current proof status anchor

This file is the short status anchor for `main` when older open pull requests, README/ROADMAP text, or external summaries lag behind the proof spine.

## Current `main` proof-facing surface

The current `main` proof-facing surface is the carrier / spectral-route / R1--R7 terminal-public-external audit chain:

```text
Basic-layer route marker
  -> downstream exactGapValueReal carrier
  -> continuum-Hamiltonian / PVM / operator-spectral derivation route
  -> R6 exact atom 33/20 / spectral-PVM pinning route
  -> R7 positive spectral-weight witness route
  -> R1--R7 terminal discharge chain
  -> public / external audit receipt chain
```

Current terminal/public/external anchors:

```text
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean
```

Current public-boundary reading:

```text
internal Lean terminal discharge route: present
public / external audit receipt surface: present
external mathematical consensus: not claimed
independent peer-review completion: not claimed
Clay-style public acceptance: not claimed
```

## Central payload

The central Lean-facing payload is:

```text
MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

The terminal R1--R7 theorem anchor is:

```lean
theorem hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight :
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

## Exact-gap layer separation

The current route separates five review layers:

```text
1. Basic-layer route marker
2. downstream real-carrier / carrier-level arithmetic normalization
3. continuum-Hamiltonian / PVM / operator-spectral derivation layer
4. R6 exact atom and R7 positive spectral-weight layer
5. engineering / audit / public-boundary marker layer
```

Current Lean separation map:

```text
MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean
```

Human-readable note:

```text
docs/exact_gap_layer_separation.md
```

Primary separation theorem anchors:

```text
exact_gap_abstract_theorem_body_layer_ready
exact_gap_carrier_layer_ready
exact_gap_spectral_receipt_layer_ready
exact_gap_engineering_marker_layer_ready
exact_gap_layer_separation_ready
```

Correct reading:

```text
Basic.lean
  -> marker-only route-deferred layer
  -> no real-valued gap carrier
  -> no local final-value assignment

ExactGapReal.lean
  -> defines exactGapValueReal as the downstream normalized real carrier
  -> proves exactGapValueReal_eq : exactGapValueReal = 33/20
  -> this is a carrier-level arithmetic normalization

YangMillsHamiltonianSpectralDerivation3320.lean
  -> aligns the spectral infimum / attainment / observable atom value with exactGapValueReal
  -> keeps the public boundary and final-release boundary held
  -> intentionally does not export derivedHamiltonianSpectralValue = 33/20 outside R6

R6 ExactAtom3320 lane
  -> supplies the non-definitional spectral/PVM pinning route for the displayed value

R7 positive-weight lane
  -> supplies the positive spectral-weight witness and preserves the exact value

R1--R7 terminal chain
  -> records exact 33/20 plus positive spectral weight at terminal level
```

The final normalized value should therefore be reviewed through the R1--R7 terminal route plus the continuum-Hamiltonian / PVM / operator-spectral route.  It should not be reviewed as if `Basic.lean` or a local carrier arithmetic theorem alone were the physical derivation.

## Exact `33/20` derivation source

The repository distinguishes the following roles.

### 1. Basic-layer marker role

```text
MGAP4D/MathlibAnalytic/Basic.lean
```

`Basic.lean` records that the spectral theorem route, PVM observable route, and Hamiltonian theorem route are deferred.  It explicitly records that the Basic layer has no numeric carrier.

Primary anchors:

```text
FourDYangMillsAnalyticGapValueOrigin.ready
four_d_yang_mills_analytic_gap_value_origin_ready
four_d_yang_mills_basic_layer_numeric_carrier_absent
```

### 2. Real-carrier role

```text
MGAP4D/MathlibAnalytic/ExactGapReal.lean
```

`ExactGapReal.lean` defines the downstream normalized real carrier:

```text
exactGapValueReal
exactGapValueRealRouteWitness
exactGapValueReal_eq
exactGapValueReal_pos
exactGapValueReal_above_one
exactGapRealSurface
```

The theorem

```lean
theorem exactGapValueReal_eq :
  exactGapValueReal = (33 : ℝ) / 20
```

is the carrier-level arithmetic normalization.  It is important evidence, but documentation must not present it as the entire Hamiltonian/PVM/spectral derivation.

### 3. Continuum-Hamiltonian / PVM / spectral derivation role

```text
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianExactMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/ConcreteR1R7ResidualDischarge.lean
```

Primary anchors:

```text
continuum_hamiltonian_derives_exact_mass_gap_value
physical_continuum_hamiltonian_to_exact_positive_mass_gap
physical_continuum_hamiltonian_exact_gap_33_over_20
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero
yang_mills_hamiltonian_spectral_derivation_3320_ready
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_exact_gap_value_from_physical_spectrum
```

The Yang--Mills spectral interface aligns the derived Hamiltonian spectral value with `exactGapValueReal`, while its boundary comments and theorem surfaces keep the public / final-release boundary held.

### 4. R6 exact-atom / value-pinning role

```text
MGAP4D/R6/Theorem/ExactAtom3320YangMillsSpectralDerivation.lean
MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean
MGAP4D/R6/Theorem/ExactAtom3320SpectralOriginFirewall.lean
MGAP4D/R6/Theorem/ExactAtom3320ValueOriginQuarantine.lean
MGAP4D/R6/Theorem/ExactAtom3320DirectReviewBridge.lean
```

Primary anchors:

```text
exact_atom_3320_yang_mills_spectral_derivation_ready
exact_atom_3320_yang_mills_exact_gap_carrier_eq_derived
exact_atom_3320_yang_mills_positive_nonzero_spectral_mass
ExactAtom3320R6NormalizedSpectralAtom
ExactAtom3320R6SpectralPVMPinsDerivedValue
exact_atom_3320_r6_derived_spectral_value_eq_3320
exact_atom_3320_r6_exact_gap_value_eq_3320
exact_atom_3320_nondefinitional_origin_certificate_ready
exact_atom_3320_nondefinitional_derivation_target_ready
```

R6 is the review layer that prevents the displayed value `33/20` from being read as a pre-R6 definitional unfolding.  It should be reviewed as the non-definitional spectral/PVM pinning lane.

### 5. R7 positive spectral-weight role

```text
MGAP4D/R7/Theorem.lean
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightBridge.lean
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightSlotClosure.lean
MGAP4D/HardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure.lean
```

Primary payload:

```text
observableSpectralWeight3320Certificate.massWitness.positiveMass = true
exactGapValueReal = 33/20
exactGapValueReal ∈ singletonObservableAtomTheoremTheoremData.atom
witnessSector = orthogonal
witnessSector ≠ vacuum
```

### 6. Terminal receipt role

```text
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean
```

The terminal chain records:

```text
R1 concrete Hilbert closure readiness indexed
R2 dense-domain unbounded operator closure readiness indexed
R3 adjoint/self-adjointness theorem discharge readiness indexed
R4 genuine-PVM closure readiness indexed
R5 compact centered plaquette observable closure readiness indexed
R6 non-definitional exact atom 33/20 closure readiness indexed
R7 positive spectral-weight closure readiness indexed
exactGapValueReal = 33/20
positive spectral weight
R4 genuine-PVM law receipts
finalReleaseHeld
publicBoundaryLocked
```

When this receipt chain is read as an exact-value derivation, its upstream source is the R1--R7 operator/spectral route above, not the local Basic marker and not the carrier arithmetic theorem alone.

## R2 current main lane

R2 should now be read as the infinite-dimensional completed `ℓ²` diagonal operator lane, not merely as the old local residual taxonomy.

Current Lean anchor:

```text
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean
```

Current handoff anchors:

```text
MGAP4D/HardPhysicalResidualLedgerR2InfiniteLaneR3InputHandoff.lean
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteLaneSpectralInputHandoff.lean
```

Human-readable note:

```text
docs/r2_infinite_l2_diagonal_operator_lane.md
```

Review reading:

```text
old R2 taxonomy = historical local decomposition
current R2 body = completed ℓ² diagonal closed/unbounded operator lane
R1--R7 chain = terminal/public receipt route that consumes the current R2 body
```

Boundary reading:

```text
R2 gives completed diagonal closed-operator and unboundedness surfaces.
R2-to-R3 handoff consumes the current R2 body without shortcutting downstream obligations.
R2-to-spectral-input handoff connects the current R2 body to the LinearPMap self-adjoint spectral input surface.
Full spectral theorem, PVM construction, exact atom 33/20, and positive spectral-weight construction remain separately reviewable downstream surfaces.
```

## R4 status and historical `StillOpen` markers

Current canonical R4 status is terminal-visible through the R1--R7 route:

```text
R4 genuine PVM closure
  -> R5 compact centered plaquette observable closure
  -> R6 non-definitional exact atom 33/20 closure
  -> R7 positive spectral-weight closure
  -> R1--R7 terminal discharge chain index
```

Older endpoint-stage files may still contain identifiers such as:

```text
SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen
SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen
```

These markers must be classified as historical or explicitly superseded before they can coexist with a terminal R4 closure reading. If a `StillOpen` marker is active, the corresponding obligation remains not discharged.

Current R4 status should be reviewed through:

```text
docs/r4_terminal_status_supersession.md
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
```

## Witness-slot provenance

The current route distinguishes a receipt slot from the theorem anchor that generates it. External reviewers should inspect:

```text
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessProvenance.lean
docs/continuum_hamiltonian_witness_provenance.md
```

The summary theorem is:

```text
continuum_hamiltonian_witness_provenance_map_ready
```

## Placeholder / witness inventory

External review must distinguish mathematical theorem bodies from placeholders, witnesses, receipts, and readiness packets.

Primary inventory note:

```text
docs/proof_placeholder_inventory.md
```

Inventory audit script:

```text
scripts/audit_proof_placeholder_inventory.py
```

`PUnit`, `True`, and `StillOpen` are open proof-debt markers. They must be replaced, discharged, or explicitly superseded by typed theorem anchors before any public analytic theorem route can count as discharged. Provenance and readiness markers such as `theoremWitnessOnly`, `receipt`, `ready`, `prototype`, `skeleton`, `boundary`, `packet`, and `manifest` remain review-order evidence unless their payload is a substantive typed theorem.

## Physical normalization

The exact value is normalized and dimensionless:

```text
Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
```

A dimensional physical mass gap requires a positive reference scale `E0`.  Internal normalized units correspond to `E0 = 1`.

## Audit route

The current hard physical residual audit checks the terminal discharge index and the public/external receipt chain. The placeholder inventory audit separately lists review markers and witness-like surfaces:

```text
scripts/audit_hard_physical_residual_ledger.py
scripts/audit_proof_placeholder_inventory.py
docs/hard_physical_residual_ledger.md
docs/hard_physical_residual_ledger_terminal_discharge_index.md
docs/r2_infinite_l2_diagonal_operator_lane.md
docs/proof_placeholder_inventory.md
docs/exact_gap_layer_separation.md
docs/continuum_hamiltonian_witness_provenance.md
docs/r4_terminal_status_supersession.md
```

## Final public boundary

Use:

```text
internal Lean terminal discharge route with public / external audit receipt surface
```

Do not use:

```text
external mathematical consensus
independent peer-review completion
Clay-style public acceptance
Basic-layer numerical derivation
carrier arithmetic theorem alone as physical derivation
CI success as mathematical proof review
```
