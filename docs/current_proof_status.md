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

## Exact-gap layer separation

The current route separates four layers:

```text
abstract theorem-body layer
normalized carrier layer
spectral receipt layer
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
YangMillsHamiltonianSpectralDerivation3320.lean = current spectral receipt / carrier alignment layer
ExactGapTheoremBodyClosure.lean = older mixed closure record
ExactGapLayerSeparation.lean = current separation map
```

The current spectral receipt is not presented as an independent operator-theoretic construction of a new spectral value followed by a calculation reducing it to `33/20`. It is a carrier-aligned spectral-route receipt. A stronger independent spectral-value construction would require a distinct future theorem-body lane.

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

These are historical local boundary markers for earlier endpoint-stage files, not the current global status of the R4 route on `main`.

Current R4 status should be reviewed through:

```text
docs/r4_terminal_status_supersession.md
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
```

The review reading is:

```text
old endpoint-stage StillOpen marker
  -> historical local lineage marker
  -> superseded for current public status by R4 operator-topology final packet and R1--R7 terminal receipt
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

This theorem bundles explicit provenance for the non-boundary `ContinuumHamiltonianMassGapWitnessData` slots:

```text
physicalContinuumHamiltonianReady
hphysFromContinuumYMReady
selfAdjointSpectralChainReady
normalizationToExactGapReady
compactCenteredPlaquetteWeightReady
spectralMassObservableReady
massGapDerivationWitness
continuumHamiltonianToMassGapChainReady
```

The intended review reading is:

```text
receipt slot exists
  -> provenance theorem identifies upstream theorem anchor
  -> external reviewer inspects that upstream theorem / construction
```

## Exact `33/20` derivation source

The repository now distinguishes two roles:

```text
carrier role:
  MGAP4D/MathlibAnalytic/Basic.lean
  MGAP4D/MathlibAnalytic/ExactGapReal.lean

spectral receipt role:
  MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
  MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
```

`exactGapValueReal : ℝ := 33 / 20` remains the canonical normalized carrier. Its local `rfl` / `norm_num` checks are not the derivation source.

The current spectral receipt identifies the Hamiltonian spectral receipt value with the same normalized carrier and carries positive spectral mass:

```text
yang_mills_hamiltonian_spectral_derivation_3320_ready
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

## Public/external audit receipt

The public/external receipt chain carries:

```text
exactGapValueReal = 33 / 20
positive spectral weight
R4 genuine-PVM law receipts
finalReleaseHeld
publicBoundaryLocked
```

When this receipt chain is read as an exact-value derivation, its upstream source is the spectral receipt route above, not the local carrier definition.

Primary named theorem anchors:

```text
hard_physical_residual_ledger_r1_r7_terminal_discharge_chain_index_3320_ready
hard_physical_residual_ledger_r1_r7_public_audit_surface_3320_ready
hard_physical_residual_ledger_r1_r7_public_audit_chain_index_3320_ready
hard_physical_residual_ledger_r1_r7_external_audit_handoff_3320_ready
hard_physical_residual_ledger_r1_r7_external_audit_receipt_chain_index_3320_ready
```

## Audit route

The current hard physical residual audit checks both the terminal discharge index and the public/external receipt chain:

```text
scripts/audit_hard_physical_residual_ledger.py
docs/hard_physical_residual_ledger.md
docs/hard_physical_residual_ledger_terminal_discharge_index.md
docs/exact_gap_layer_separation.md
docs/continuum_hamiltonian_witness_provenance.md
docs/r4_terminal_status_supersession.md
```

## Boundary

Older open PRs that describe R3/R4/R5/R6/R7 as downstream or open are historical. They should not be used as the current proof frontier unless they are rebased and rewritten against the current R1--R7 receipt chain.

The current chain is still a receipt / handoff / audit surface. It preserves the existing public final-release boundary and does not claim external mathematical consensus.
