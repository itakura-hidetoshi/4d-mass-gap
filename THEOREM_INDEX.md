# MGAP4D Public Route Index

This index gives the current external-review map for the MGAP4D public proof route on `main`.

Last synchronized: 2026-06-09

## Current public route

The current public route is the R1--R7 terminal / public / external audit receipt chain.

```text
R1 ConcreteRealHilbertSpace
  -> R2 InfiniteL2DiagonalOperatorLane
  -> R2 DenselyDefinedOperator
  -> R2 GraphClosednessReadinessPromotion
  -> R2 GraphClosednessObligationPromotion
  -> R2 DenseDomainUnboundedHamiltonian
  -> R2InfiniteLaneR3InputHandoff
  -> R2InfiniteLaneSpectralInputHandoff
  -> R3 SelfAdjointPhysicalHamiltonian
  -> R4 ConcretePVMSpectralMeasure
  -> R4 OperatorTopologyConcreteRouteTopLevelFinalPacket
  -> R5 CompactCenteredPlaquetteObservable
  -> R6 NondefinitionalSpectralAtom3320
  -> R7 PositiveSpectralWeightDerivation3320
  -> ConcreteR1R7ResidualDischarge
  -> ContinuumHamiltonianCompleteMassGapDerivation
  -> YangMillsHamiltonianSpectralDerivation3320
  -> ExactGapLayerSeparation
  -> ContinuumHamiltonianMassGapWitnessProvenance
  -> R1R7TerminalDischargeChainIndex
  -> R1R7PublicAuditSurface
  -> R1R7PublicAuditChainIndex
  -> R1R7ExternalAuditHandoff
  -> R1R7ExternalAuditReceiptChainIndex
```

## R2 infinite-dimensional `ℓ²` diagonal operator lane

R2 should now be read as the infinite-dimensional completed `ℓ²` diagonal operator lane, not merely as the old local residual taxonomy.

Primary Lean anchor:

```text
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean
```

R2-to-R3 handoff anchor:

```text
MGAP4D/HardPhysicalResidualLedgerR2InfiniteLaneR3InputHandoff.lean
```

R2-to-spectral-input handoff anchor:

```text
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

Review interpretation:

```text
old R2 taxonomy = historical local decomposition
current R2 body = completed ℓ² diagonal closed/unbounded operator lane
R1--R7 chain = terminal/public receipt route that consumes the current R2 body
```

Important R2 boundary:

```text
R2 now gives completed diagonal closed-operator and unboundedness surfaces.
R2 does not by itself assert full symmetry, adjoint-domain agreement, self-adjointness, spectral theorem, PVM, exact atom 33/20, or positive spectral weight.
The R2InfiniteLaneR3InputHandoff only hands the current R2 body to the existing R3 input bridge and keeps downstream obligations visible.
The R2InfiniteLaneSpectralInputHandoff connects the current R2 body to the existing actual LinearPMap self-adjoint spectral input handoff, while keeping full spectral theorem, PVM construction, and positive spectral-weight construction as separate downstream obligations.
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

The inventory classifies `PUnit`, `True`, `StillOpen`, `theoremWitnessOnly`, `receipt`, `ready`, `prototype`, `skeleton`, `boundary`, `packet`, and `manifest` surfaces by replacement strength. These markers do not automatically substitute for analytic theorem bodies.

## Exact `33/20` source roles

The public route distinguishes the normalized carrier from the derivation route.

Carrier files:

```text
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
```

These files expose the normalized carrier `exactGapValueReal = 33/20`. Their local `rfl` / `norm_num` proofs are carrier checks.

Derivation-route files:

```text
MGAP4D/ConcreteR1R7ResidualDischarge.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
```

These files are the current proof-facing route for the claim that the normalized value `33/20` is carried by the Hamiltonian / PVM / plaquette / spectral-weight chain. The carrier is the normalized target value; the derivation claim is reviewed through the R1--R7 terminal route.

Primary derivation anchors:

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

## Exact-gap layer separation

The exact-gap route separates four review layers:

```text
abstract theorem-body layer
normalized carrier layer
operator/spectral derivation layer
engineering / review-marker layer
```

Primary Lean map:

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

## R4 terminal status and historical endpoint-stage markers

Older R4 endpoint-stage files may still contain names such as:

```text
SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen
SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen
```

These names are append-only historical boundary markers for earlier local endpoint-stage files. They are not the current global R4 status on `main`.

Current R4 status is read through:

```text
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean
docs/r4_terminal_status_supersession.md
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
```

## Continuum Hamiltonian witness provenance

Primary provenance file:

```text
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessProvenance.lean
```

Human-readable provenance note:

```text
docs/continuum_hamiltonian_witness_provenance.md
```

Primary provenance theorem anchor:

```text
continuum_hamiltonian_witness_provenance_map_ready
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

Primary terminal theorem anchor:

```text
hard_physical_residual_ledger_r1_r7_terminal_discharge_chain_index_3320_ready
```

## Public and external audit route

The public/external route carries:

```text
exactGapValueReal = 33 / 20
positive spectral weight
R4 genuine-PVM law receipts
finalReleaseHeld
publicBoundaryLocked
```

When this route refers to the exact value as derived, its upstream source is the R1--R7 operator/spectral route above, not the local carrier definition in `Basic.lean`.

## Audit route

```text
scripts/audit_hard_physical_residual_ledger.py
scripts/audit_proof_placeholder_inventory.py
docs/hard_physical_residual_ledger.md
docs/hard_physical_residual_ledger_terminal_discharge_index.md
docs/current_proof_status.md
docs/r2_infinite_l2_diagonal_operator_lane.md
docs/proof_placeholder_inventory.md
docs/exact_gap_layer_separation.md
docs/continuum_hamiltonian_witness_provenance.md
docs/r4_terminal_status_supersession.md
```

Strongest executable check:

```bash
bash scripts/check.sh
```

Strongest Lean kernel gate:

```bash
lake build
```

## Active Lean roots

| Root | Role |
|---|---|
| `MGAP4D.lean` | Top-level Lean import root. |
| `MGAP4D/MathlibAnalytic.lean` | Mathlib analytic theorem-surface root. |
| `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean` | Current R2 infinite-dimensional completed `ℓ²` diagonal operator lane. |
| `MGAP4D/HardPhysicalResidualLedgerR2InfiniteLaneR3InputHandoff.lean` | Current R2 infinite lane handoff into the R3 self-adjointness input bridge. |
| `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteLaneSpectralInputHandoff.lean` | Current R2 infinite lane handoff into the actual LinearPMap self-adjoint spectral input surface. |
| `MGAP4D/ConcreteR1R7ResidualDischarge.lean` | Current terminal derivation discharge for the R1--R7 route. |
| `MGAP4D/MathlibAnalytic/ExactGapLayerSeparation.lean` | Separation map for theorem-body, carrier, derivation, and marker layers. |
| `MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean` | Spectral derivation interface into the normalized carrier. |
| `MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean` | Complete continuum-Hamiltonian spectral derivation route. |
| `MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessProvenance.lean` | Provenance map from witness slots to upstream theorem anchors. |
| `MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean` | Current R4 operator-topology final packet. |
| `MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean` | Terminal R1--R7 hard residual discharge index. |

## Review order

1. Run `bash scripts/check.sh`.
2. Run `python3 scripts/audit_proof_placeholder_inventory.py`.
3. Inspect `docs/proof_placeholder_inventory.md`.
4. Inspect `docs/current_proof_status.md`.
5. Inspect `THEOREM_INDEX.md`.
6. Inspect `docs/r2_infinite_l2_diagonal_operator_lane.md`.
7. Inspect `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean`.
8. Inspect `MGAP4D/HardPhysicalResidualLedgerR2InfiniteLaneR3InputHandoff.lean`.
9. Inspect `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteLaneSpectralInputHandoff.lean`.
10. Inspect `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2CompletedHilbertOperatorNormUnboundedness.lean`.
11. Inspect `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditions.lean`.
12. Inspect `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2PhysicalSpectralPromotionAuditChecklist.lean`.
13. Inspect `docs/exact_gap_layer_separation.md`.
14. Inspect `MGAP4D/ConcreteR1R7ResidualDischarge.lean`.
15. Inspect the R4/R5/R6/R7 and terminal/public/external audit files.
16. Confirm `lake build` on a fresh clone with the pinned `lean-toolchain`.

## Boundary

This index is a navigation and audit surface. It preserves `finalReleaseHeld`, `publicBoundaryLocked`, and the requirement for independent mathematical review.
