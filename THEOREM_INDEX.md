# MGAP4D Public Route Index

This index gives the current external-review map for the MGAP4D public proof route on `main`.

It is a navigation and audit document. It does not replace Lean kernel checking, mathematical proof review, or the source files themselves.

Last synchronized: 2026-06-09

## Current public route

The current public route is the R1--R7 terminal / public / external audit receipt chain.

```text
R1 concrete Hilbert closure
  -> R2 dense-domain unbounded operator closure
  -> R3 adjoint-graph theorem discharge
  -> R3 concrete self-adjointness theorem discharge
  -> R4 genuine PVM closure
  -> R5 compact centered plaquette observable closure
  -> R6 non-definitional exact atom 33/20 closure
  -> R7 positive spectral-weight closure
  -> terminal discharge chain index
  -> public audit surface
  -> public audit chain index
  -> guarded external-audit handoff
  -> external-audit receipt chain index
```

Canonical source files:

```text
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean
```

Current short status anchor:

```text
docs/current_proof_status.md
```

## Primary public theorem anchors

```text
hard_physical_residual_ledger_r1_r7_terminal_discharge_chain_index_3320_ready
hard_physical_residual_ledger_r1_r7_public_audit_surface_3320_ready
hard_physical_residual_ledger_r1_r7_public_audit_chain_index_3320_ready
hard_physical_residual_ledger_r1_r7_external_audit_handoff_3320_ready
hard_physical_residual_ledger_r1_r7_external_audit_receipt_chain_index_3320_ready
```

## Public audit projections

The public audit chain index exposes these projections without adding release authority:

```text
exactGapValueReal = 33 / 20
observableSpectralWeight3320Certificate.massWitness.positiveMass = true
R4 genuine-PVM law visibility
finalReleaseHeld
publicBoundaryLocked
```

Named public audit projection theorems:

```text
hard_physical_residual_ledger_public_audit_chain_exact_3320_positive_weight
hard_physical_residual_ledger_public_audit_chain_r4_genuine_pvm_laws_visible
hard_physical_residual_ledger_public_audit_chain_boundary_locked
```

## External-audit receipt projections

The guarded external-audit receipt chain carries the same proof-facing projections outward:

```text
exactGapValueReal = 33 / 20
observableSpectralWeight3320Certificate.massWitness.positiveMass = true
R4 genuine-PVM law receipts
finalReleaseHeld
publicBoundaryLocked
receiptChainIndexed
```

Named external receipt projection theorems:

```text
hard_physical_residual_ledger_external_audit_receipt_chain_exact_3320_positive_weight
hard_physical_residual_ledger_external_audit_receipt_chain_r4_genuine_pvm_laws_visible
hard_physical_residual_ledger_external_audit_receipt_chain_boundary_locked
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
| `MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean` | Terminal R1--R7 hard residual discharge index. |
| `MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean` | Public route index for exact value, positive weight, R4 genuine-PVM visibility, and boundary lock. |
| `MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean` | External-audit receipt route index. |

## Review order

Recommended external review order:

1. Run `bash scripts/check.sh`.
2. Inspect `docs/current_proof_status.md`.
3. Inspect `docs/hard_physical_residual_ledger.md`.
4. Inspect `docs/hard_physical_residual_ledger_terminal_discharge_index.md`.
5. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean`.
6. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean`.
7. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean`.
8. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean`.
9. Inspect `MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean`.
10. Confirm `lake build` on a fresh clone with the pinned `lean-toolchain`.

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
