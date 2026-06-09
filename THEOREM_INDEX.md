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
  -> R5 CompactCenteredPlaquetteObservable
  -> R6 NondefinitionalSpectralAtom3320
  -> R7 PositiveSpectralWeightDerivation3320
  -> R1R7TerminalDischargeChainIndex
  -> R1R7PublicAuditSurface
  -> R1R7PublicAuditChainIndex
  -> R1R7ExternalAuditHandoff
  -> R1R7ExternalAuditReceiptChainIndex
```

Canonical source files:

```text
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
4. Inspect `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2DenselyDefinedOperator.lean`.
5. Inspect `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2GraphClosednessReadinessPromotion.lean`.
6. Inspect `MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2GraphClosednessObligationPromotion.lean`.
7. Inspect `docs/hard_physical_residual_ledger.md`.
8. Inspect `docs/hard_physical_residual_ledger_terminal_discharge_index.md`.
9. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean`.
10. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean`.
11. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean`.
12. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean`.
13. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean`.
14. Confirm `lake build` on a fresh clone with the pinned `lean-toolchain`.

## Superseded route notes

Older open pull requests or older route documents that describe R3/R4/R5/R6/R7 as still downstream or open are historical. They should not be used as the current public route unless they are rebased and rewritten against this R1--R7 receipt chain.

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
