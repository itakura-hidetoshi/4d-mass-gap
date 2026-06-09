# MGAP4D Public Route Index

This index gives the current external-review map for the MGAP4D public proof route on `main`.

It is a navigation and audit document. It does not replace Lean kernel checking, mathematical proof review, or the source files themselves.

Last synchronized: 2026-06-09

Current short status anchor:

```text
docs/current_proof_status.md
```

## Current public route

The current public route is the R1--R7 terminal / public / external audit receipt chain.

```text
R1 ConcreteRealHilbertSpace
  -> R2 DenselyDefinedOperator
  -> R2 GraphClosednessReadinessPromotion
  -> R2 GraphClosednessObligationPromotion
  -> R2 DenseDomainUnboundedHamiltonian
  -> R3 SelfAdjointPhysicalHamiltonian
  -> R4 ConcretePVMSpectralMeasure
  -> R4 OperatorTopologyConcreteRouteTopLevelFinalPacket
  -> R5 CompactCenteredPlaquetteObservable
  -> R6 NondefinitionalSpectralAtom3320
  -> R7 PositiveSpectralWeightDerivation3320
  -> YangMillsHamiltonianSpectralDerivation3320
  -> ContinuumHamiltonianCompleteMassGapDerivation
  -> ContinuumHamiltonianMassGapWitnessProvenance
  -> R1R7TerminalDischargeChainIndex
  -> R1R7PublicAuditSurface
  -> R1R7PublicAuditChainIndex
  -> R1R7ExternalAuditHandoff
  -> R1R7ExternalAuditReceiptChainIndex
```

Canonical source files:

```text
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean
docs/r4_terminal_status_supersession.md
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessProvenance.lean
docs/continuum_hamiltonian_witness_provenance.md
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean
```

## R2 graph-closedness route milestones

These milestones are the explicit bridge between the densely-defined unbounded operator and the R3 adjoint/self-adjointness route. They should be read as the R2 graph-closedness subroute inside the top-level public route.

```text
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2DenselyDefinedOperator.lean
  -> establishes the concrete densely-defined operator surface.

MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2GraphClosednessReadinessPromotion.lean
  -> promotes graph-closedness readiness from the concrete operator route.

MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2GraphClosednessObligationPromotion.lean
  -> promotes graph-closedness obligations into the downstream adjoint/self-adjointness route.
```

Review interpretation:

```text
DenselyDefinedOperator is the R2 operator-body entry point.
GraphClosednessReadinessPromotion is the R2 graph-readiness bridge.
GraphClosednessObligationPromotion is the R2-to-R3 obligation bridge.
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

Primary current R4 theorem anchors:

```text
spectral_measure_pvm_operator_topology_r4_concrete_route_top_level_final_packet_ready
spectral_measure_pvm_operator_topology_r4_concrete_route_top_level_final_packet_public_boundary_held
spectral_measure_pvm_operator_topology_r4_concrete_route_top_level_final_packet_extracts_operator_topology_convergence_target
spectral_measure_pvm_operator_topology_r4_concrete_route_top_level_final_packet_extracts_genuine_bridge
spectral_measure_pvm_operator_topology_r4_concrete_route_top_level_final_packet_preserves_no_shell_collapse
```

External-review interpretation:

```text
old endpoint-stage StillOpen marker
  -> historical local lineage marker
  -> superseded for current public status by R4 operator-topology final packet and R1--R7 terminal receipt
```

## Continuum Hamiltonian witness provenance

The receipt slots in `ContinuumHamiltonianMassGapWitnessData` are no longer meant to be externally reviewed as opaque `Prop` fields. The provenance map gives a theorem-level route from each slot to an upstream construction, bridge, or spectral derivation theorem.

Primary provenance file:

```text
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessProvenance.lean
```

Human-readable provenance note:

```text
docs/continuum_hamiltonian_witness_provenance.md
```

Primary provenance theorem anchors:

```text
continuum_hamiltonian_witness_physical_surface_provenance
continuum_hamiltonian_witness_hphys_from_ym_provenance
continuum_hamiltonian_witness_self_adjoint_spectral_slot_provenance
continuum_hamiltonian_witness_normalization_slot_provenance
continuum_hamiltonian_witness_compact_plaquette_provenance
continuum_hamiltonian_witness_spectral_mass_observable_provenance
continuum_hamiltonian_witness_mass_gap_derivation_slot_provenance
continuum_hamiltonian_witness_chain_slot_provenance
continuum_hamiltonian_witness_exact_value_derivation_provenance
continuum_hamiltonian_witness_positive_spectral_mass_provenance
continuum_hamiltonian_witness_provenance_map_ready
```

External-review interpretation:

```text
receipt slot exists
  -> provenance theorem identifies its upstream theorem anchor
  -> external reviewer inspects that upstream theorem / construction
```

## Exact `33/20` derivation source

The public route distinguishes the normalized carrier from the derivation receipt.

Carrier files:

```text
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
```

These files define and expose the normalized real carrier `exactGapValueReal = 33/20`. Their local `rfl` / `norm_num` proofs are carrier checks.

Derivation files:

```text
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
```

These files are the current source for the claim that the Hamiltonian/spectral route derives the same normalized value. Public/external receipt layers should cite these derivation receipts when the intended meaning is "derived from the Yang--Mills Hamiltonian spectral route".

Primary derivation theorem anchors:

```text
yang_mills_hamiltonian_spectral_derivation_3320_ready
yang_mills_hamiltonian_spectral_infimum_eq_3320
yang_mills_hamiltonian_spectral_attainment_eq_3320
yang_mills_hamiltonian_observable_atom_eq_3320
yang_mills_hamiltonian_spectral_analysis_derives_3320
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_spectral_derivation_exact_gap_value
yang_mills_hamiltonian_spectral_derivation_positive_mass
yang_mills_hamiltonian_spectral_derivation_nonzero_mass
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero
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

## Public audit route

The public audit surface and public audit chain index expose these projections without adding release authority:

```text
exactGapValueReal = 33 / 20
observableSpectralWeight3320Certificate.massWitness.positiveMass = true
R4 genuine-PVM law visibility
finalReleaseHeld
publicBoundaryLocked
```

When the public audit route refers to the exact value as a derived value, the intended upstream source is the spectral derivation route above, not the local carrier definition in `Basic.lean`.

Primary public theorem anchors:

```text
hard_physical_residual_ledger_r1_r7_public_audit_surface_3320_ready
hard_physical_residual_ledger_public_audit_surface_exact_3320_positive_weight
hard_physical_residual_ledger_public_audit_surface_r4_genuine_pvm_laws_visible
hard_physical_residual_ledger_public_audit_surface_boundary_locked
hard_physical_residual_ledger_r1_r7_public_audit_chain_index_3320_ready
hard_physical_residual_ledger_public_audit_chain_exact_3320_positive_weight
hard_physical_residual_ledger_public_audit_chain_r4_genuine_pvm_laws_visible
hard_physical_residual_ledger_public_audit_chain_boundary_locked
```

## External-audit handoff route

The guarded external-audit handoff and external-audit receipt chain carry the same proof-facing projections outward:

```text
exactGapValueReal = 33 / 20
observableSpectralWeight3320Certificate.massWitness.positiveMass = true
R4 genuine-PVM law receipts
finalReleaseHeld
publicBoundaryLocked
receiptChainIndexed
```

Primary external theorem anchors:

```text
hard_physical_residual_ledger_r1_r7_external_audit_handoff_3320_ready
hard_physical_residual_ledger_external_audit_handoff_exact_3320_positive_weight
hard_physical_residual_ledger_external_audit_handoff_r4_genuine_pvm_laws_visible
hard_physical_residual_ledger_external_audit_handoff_boundary_locked
hard_physical_residual_ledger_r1_r7_external_audit_receipt_chain_index_3320_ready
hard_physical_residual_ledger_external_audit_receipt_chain_exact_3320_positive_weight
hard_physical_residual_ledger_external_audit_receipt_chain_r4_genuine_pvm_laws_visible
hard_physical_residual_ledger_external_audit_receipt_chain_boundary_locked
```

## Exact value / positive-weight receipt

The current public route exposes the exact normalized value and positive-weight receipt as:

```text
exactGapValueReal = 33 / 20
positive spectral weight at the routed exact atom
R4 genuine PVM law visibility
```

The exact value remains normalized. Dimensional physical reading still requires an external reference scale:

```text
physicalGap_dimensional = E0 * (33/20)
```

## Audit route

The current hard physical residual audit checks the terminal discharge index and the public / external receipt chain:

```text
scripts/audit_hard_physical_residual_ledger.py
docs/hard_physical_residual_ledger.md
docs/hard_physical_residual_ledger_terminal_discharge_index.md
docs/current_proof_status.md
docs/continuum_hamiltonian_witness_provenance.md
docs/r4_terminal_status_supersession.md
```

The strongest executable check remains:

```bash
bash scripts/check.sh
```

The strongest Lean kernel gate remains:

```bash
lake build
```

## Active Lean roots

| Root | Role |
|---|---|
| `MGAP4D.lean` | Top-level Lean import root. |
| `MGAP4D/MathlibAnalytic.lean` | Mathlib analytic theorem-surface root. |
| `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2DenselyDefinedOperator.lean` | R2 densely-defined operator entry point. |
| `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2GraphClosednessReadinessPromotion.lean` | R2 graph-closedness readiness promotion surface. |
| `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2GraphClosednessObligationPromotion.lean` | R2 graph-closedness obligation promotion surface. |
| `MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean` | Current R4 operator-topology final packet and supersession anchor. |
| `MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean` | Exact `33/20` spectral derivation route. |
| `MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean` | Complete continuum-Hamiltonian spectral derivation route. |
| `MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessProvenance.lean` | Provenance map from witness slots to upstream theorem anchors. |
| `MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean` | Terminal R1--R7 hard residual discharge index. |
| `MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean` | Public audit surface for exact value, positive weight, R4 genuine-PVM visibility, and boundary lock. |
| `MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean` | Public route index for exact value, positive weight, R4 genuine-PVM visibility, and boundary lock. |
| `MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean` | Guarded external-audit handoff surface. |
| `MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean` | External-audit receipt route index. |

## Review order

Recommended external review order:

1. Run `bash scripts/check.sh`.
2. Inspect `docs/current_proof_status.md`.
3. Inspect `THEOREM_INDEX.md`.
4. Inspect `docs/r4_terminal_status_supersession.md`.
5. Inspect `MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean`.
6. Inspect `docs/continuum_hamiltonian_witness_provenance.md`.
7. Inspect `MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessProvenance.lean`.
8. Inspect `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2DenselyDefinedOperator.lean`.
9. Inspect `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2GraphClosednessReadinessPromotion.lean`.
10. Inspect `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2GraphClosednessObligationPromotion.lean`.
11. Inspect `MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean`.
12. Inspect `MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean`.
13. Inspect `docs/hard_physical_residual_ledger.md`.
14. Inspect `docs/hard_physical_residual_ledger_terminal_discharge_index.md`.
15. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean`.
16. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean`.
17. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean`.
18. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean`.
19. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean`.
20. Confirm `lake build` on a fresh clone with the pinned `lean-toolchain`.

## Superseded route notes

Older open pull requests or older route documents that describe R3/R4/R5/R6/R7 as still downstream or open are historical. They should not be used as the current public route unless they are rebased and rewritten against this R1--R7 receipt chain.

Older R4 endpoint-stage files that still expose `StillOpen` markers are also historical local lineage files. They are superseded for current public status by the R4 operator-topology final packet and the R1--R7 terminal receipt chain.

The previous continuum-Hamiltonian / R2 frontier route is preserved as historical context, not as the current public route index.

## Boundary

The current chain is a receipt / handoff / audit surface. It preserves:

```text
finalReleaseHeld
publicBoundaryLocked
no external mathematical consensus claim
no Clay-style public final theorem acceptance claim
no replacement of independent mathematical review by CI or audit scripts
```

A successful replay of this index means that the repository's declared terminal, public, and external-audit receipt surfaces are present, auditable, and buildable in the pinned Lean environment.

It does not by itself discharge independent mathematical review of the full physical continuum Yang--Mills mass gap problem.
