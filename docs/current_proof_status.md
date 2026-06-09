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
```

## Boundary

Older open PRs that describe R3/R4/R5/R6/R7 as downstream or open are historical. They should not be used as the current proof frontier unless they are rebased and rewritten against the current R1--R7 receipt chain.

The current chain is still a receipt / handoff / audit surface. It preserves the existing public final-release boundary and does not claim external mathematical consensus.
