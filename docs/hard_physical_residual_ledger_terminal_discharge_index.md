# Hard Physical Residual Ledger Terminal Discharge Chain Index v0.1

This supplemental ledger page records the importable terminal receipt added after the local R1--R7 discharge components were connected.

It is additive to `docs/hard_physical_residual_ledger.md`. It records a proof-carrying terminal discharge chain index while preserving the public-boundary and final-release guards.

```text
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex
hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320
hard_physical_residual_ledger_r1_r7_terminal_discharge_chain_index_3320_ready
hard_physical_residual_ledger_r1_r7_terminal_discharged
hard_physical_residual_ledger_r1_r7_terminal_final_release_held
hard_physical_residual_ledger_r1_r7_terminal_public_boundary_locked
hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight
```

The terminal receipt bundles these component readiness proofs:

```text
R1 concrete Hilbert closure readiness indexed
R2 dense-domain unbounded operator closure readiness indexed
R3 adjoint-graph theorem discharge readiness indexed
R3 concrete self-adjointness theorem discharge readiness indexed
R4 genuine PVM closure readiness indexed
R5 compact centered plaquette observable closure readiness indexed
R6 non-definitional exact atom 33/20 closure readiness indexed
R7 positive spectral-weight closure readiness indexed
internal discharge spine binding present
```

The terminal receipt now has a public audit surface and public audit chain index:

```text
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
HardPhysicalResidualLedgerR1R7PublicAuditSurface
hardPhysicalResidualLedgerR1R7PublicAuditSurface3320
hard_physical_residual_ledger_r1_r7_public_audit_surface_3320_ready
hard_physical_residual_ledger_public_surface_exact_3320_positive_weight
hard_physical_residual_ledger_public_surface_r4_genuine_pvm_laws_visible
hard_physical_residual_ledger_public_surface_boundary_locked
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean
HardPhysicalResidualLedgerR1R7PublicAuditChainIndex
hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320
hard_physical_residual_ledger_r1_r7_public_audit_chain_index_3320_ready
hard_physical_residual_ledger_public_audit_chain_exact_3320_positive_weight
hard_physical_residual_ledger_public_audit_chain_r4_genuine_pvm_laws_visible
hard_physical_residual_ledger_public_audit_chain_boundary_locked
```

The public audit chain is exported through a guarded external-audit handoff:

```text
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean
HardPhysicalResidualLedgerR1R7ExternalAuditHandoff
hardPhysicalResidualLedgerR1R7ExternalAuditHandoff3320
hard_physical_residual_ledger_r1_r7_external_audit_handoff_3320_ready
hard_physical_residual_ledger_external_audit_handoff_exact_3320_positive_weight
hard_physical_residual_ledger_external_audit_handoff_r4_genuine_pvm_laws_visible
hard_physical_residual_ledger_external_audit_handoff_boundary_locked
```

Status line for audit:

```text
R1--R7 terminal discharge chain index: installed / terminal discharge receipt visible
Terminal exact 33/20 and positive spectral-weight projection: carried
Terminal final-release boundary: held
Terminal public boundary: locked
R1--R7 public audit surface: installed / public receipt visible
R1--R7 public audit chain index: installed / indexed public receipt visible
Public audit exact 33/20 and positive spectral-weight projection: carried
Public audit R4 genuine-PVM law receipts: visible
Public audit boundary: non-releasing and locked
R1--R7 external audit handoff: installed / guarded handoff visible
External audit handoff exact 33/20 and positive spectral-weight projection: carried
External audit handoff R4 genuine-PVM law receipts: visible
External audit handoff boundary: non-releasing and locked
```

Boundary statement:

```text
The terminal chain index, public audit surface, public audit chain index, and external-audit handoff are receipt/index layers. They preserve the existing public final-release boundary.
```
