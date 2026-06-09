# Current proof status anchor

This file is the current short status anchor for `main` when older open pull requests or README/ROADMAP text lag behind the proof spine.

## Current `main` proof-facing surface

The current `main` proof-facing surface is the R1--R7 terminal/public/external audit receipt chain:

```text
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean
```

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

Primary theorem anchors:

```text
concrete_analytic_spine_l2_r2_infinite_diagonal_operator_lane_ready
concrete_analytic_spine_l2_r2_infinite_diagonal_operator_lane_closed_operator
concrete_analytic_spine_l2_r2_infinite_diagonal_operator_lane_unbounded
concrete_analytic_spine_l2_r2_infinite_diagonal_operator_lane_graph_promotions
hard_physical_residual_ledger_r2_infinite_lane_r3_input_handoff_ready
concrete_analytic_spine_l2_r2_infinite_lane_spectral_input_handoff_ready
concrete_analytic_spine_l2_r2_infinite_lane_spectral_input_handoff_boundaries_visible
```

Review reading:

```text
old R2 taxonomy = historical local decomposition
current R2 body = completed ℓ² diagonal closed/unbounded operator lane
R1--R7 chain = terminal/public receipt route that consumes the current R2 body
```

Current R2 route:

```text
ConcreteL2R1HilbertCarrier
  -> ConcreteL2R2DiagonalDomainCandidate
  -> finite-support domain/core
  -> graph-norm finite-support density
  -> graph-norm core release
  -> graph-closedness readiness promotion
  -> graph-closedness obligation promotion
  -> graph-closure closed theorem
  -> completed diagonal graph-defined closed operator
  -> completed Hilbert operator-norm unboundedness
  -> self-adjointness concrete preconditions
  -> R2InfiniteLaneR3InputHandoff
  -> R2InfiniteLaneSpectralInputHandoff
  -> R3 self-adjointness lane
```

Boundary reading:

```text
R2 gives completed diagonal closed-operator and unboundedness surfaces.
R2-to-R3 handoff consumes the current R2 body without shortcutting downstream obligations.
R2-to-spectral-input handoff connects the current R2 body to the actual LinearPMap self-adjoint spectral input surface.
Full spectral theorem, PVM construction, exact atom 33/20, and positive spectral-weight construction remain separately reviewable downstream surfaces.
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

## Exact-gap layer separation

The current route separates four layers:

```text
abstract theorem-body layer
normalized carrier layer
operator/spectral derivation layer
engineering / review-marker layer
```

Current Lean separation map:

```text
MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean
```

Human-readable note:

```text
docs/exact_gap_layer_separation.md
```

Primary theorem anchors:

```text
exact_gap_abstract_theorem_body_layer_ready
exact_gap_carrier_layer_ready
exact_gap_spectral_receipt_layer_ready
exact_gap_engineering_marker_layer_ready
exact_gap_layer_separation_ready
```

Review reading:

```text
Basic.lean / ExactGapReal.lean = carrier layer
ConcreteR1R7ResidualDischarge.lean = current terminal derivation discharge
ContinuumHamiltonianCompleteMassGapDerivation.lean = complete Hamiltonian spectral derivation surface
YangMillsHamiltonianSpectralDerivation3320.lean = spectral derivation interface into the normalized carrier
ExactGapTheoremBodyClosure.lean = older mixed closure record
ExactGapLayerSeparation.lean = current separation map
```

The value `exactGapValueReal` is the normalized target/codomain. The current exact-value route is reviewed through the R1--R7 terminal discharge and the complete continuum-Hamiltonian spectral route, not through the carrier file alone.

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

## Exact `33/20` derivation source

The repository distinguishes two roles:

```text
carrier role:
  MGAP4D/MathlibAnalytic/Basic.lean
  MGAP4D/MathlibAnalytic/ExactGapReal.lean

operator/spectral derivation role:
  MGAP4D/ConcreteR1R7ResidualDischarge.lean
  MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
  MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
  MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
```

`exactGapValueReal : ℝ := 33 / 20` remains the canonical normalized carrier. Its local `rfl` / `norm_num` checks are carrier checks.

The current exact-value route is the R1--R7 terminal route plus the complete continuum-Hamiltonian spectral route:

```text
concrete_r1r7_residual_discharge_3320_ready
concrete_r6_residual_discharge_nondefinitional_spectral_atom_3320
concrete_r7_residual_discharge_positive_spectral_weight_derivation_3320
concrete_r1r7_residual_discharge_exact_gap_value_3320
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero
yang_mills_hamiltonian_spectral_derivation_3320_ready
```

## Terminal R1--R7 receipt

The terminal receipt indexes the following readiness chain:

```text
R1 concrete Hilbert closure readiness indexed
R2 dense-domain unbounded operator closure readiness indexed
R3 adjoint-graph theorem discharge readiness indexed
R3 concrete self-adjointness theorem discharge readiness indexed
R4 genuine PVM closure readiness indexed
R5 compact centered plaquette observable closure readiness indexed
R6 non-definitional exact atom 33/20 closure readiness indexed
R7 positive spectral-weight closure readiness indexed
```

## Public/external audit receipt

The public/external receipt chain carries:

```text
exactGapValueReal = 33 / 20
positive spectral weight
R4 genuine-PVM law receipts
finalReleaseHeld
publicBoundaryLocked
```

When this receipt chain is read as an exact-value derivation, its upstream source is the R1--R7 operator/spectral route above, not the local carrier definition.

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
