import MGAP4D.HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex

namespace MGAP4D

/-- Audit receipt for the terminal R1--R7 hard-physical-residual discharge chain.

This is a receipt/index layer over the terminal discharge chain.  It preserves
both the exact `33/20` value and the positive spectral-weight witness, while
keeping the final-release and public-boundary gates closed. -/
structure HardPhysicalResidualLedgerTerminalDischargeAuditReceipt where
  terminalIndexReady :
    hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.ready
  terminalDischarged :
    hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.r1R7TerminalDischarged
  exactValueAndPositiveWeight :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
      Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
  orthogonalNonvacuum :
    Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
        Spectral.SpectralSector.orthogonal ∧
      Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
        Spectral.SpectralSector.vacuum
  finalReleaseHeld : r1r7TheoremObligationCompletion3320.finalReleaseHeld
  publicBoundaryLocked : r1r7TheoremObligationCompletion3320.publicBoundaryLocked
  auditReceiptVisible : Prop
  auditReceiptVisible_proof : auditReceiptVisible

/-- Readiness predicate for the terminal discharge audit receipt. -/
def HardPhysicalResidualLedgerTerminalDischargeAuditReceipt.ready
    (R : HardPhysicalResidualLedgerTerminalDischargeAuditReceipt) : Prop :=
  hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.ready ∧
  hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.r1R7TerminalDischarged ∧
  (MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
    Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true) ∧
  (Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
      Spectral.SpectralSector.orthogonal ∧
    Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
      Spectral.SpectralSector.vacuum) ∧
  r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
  r1r7TheoremObligationCompletion3320.publicBoundaryLocked ∧
  R.auditReceiptVisible

/-- Canonical audit receipt for the terminal R1--R7 discharge chain. -/
def hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320 :
    HardPhysicalResidualLedgerTerminalDischargeAuditReceipt :=
  { terminalIndexReady :=
      hard_physical_residual_ledger_r1_r7_terminal_discharge_chain_index_3320_ready
    terminalDischarged :=
      hard_physical_residual_ledger_r1_r7_terminal_discharged
    exactValueAndPositiveWeight :=
      hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight
    orthogonalNonvacuum :=
      hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.positiveWeightOrthogonalNonvacuum
    finalReleaseHeld :=
      hard_physical_residual_ledger_r1_r7_terminal_final_release_held
    publicBoundaryLocked :=
      hard_physical_residual_ledger_r1_r7_terminal_public_boundary_locked
    auditReceiptVisible := True
    auditReceiptVisible_proof := True.intro }

/-- The canonical terminal-discharge audit receipt is ready. -/
theorem hard_physical_residual_ledger_terminal_discharge_audit_receipt_3320_ready :
    hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.ready := by
  exact ⟨
    hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.terminalIndexReady,
    hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.terminalDischarged,
    hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.exactValueAndPositiveWeight,
    hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.orthogonalNonvacuum,
    hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.finalReleaseHeld,
    hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.publicBoundaryLocked,
    hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.auditReceiptVisible_proof⟩

/-- Projection: the terminal audit receipt carries exact `33/20` and positive weight. -/
theorem hard_physical_residual_ledger_terminal_discharge_audit_receipt_exact_value_and_positive_weight :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
      Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true := by
  exact hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.exactValueAndPositiveWeight

/-- Projection: the terminal audit receipt preserves the orthogonal non-vacuum witness. -/
theorem hard_physical_residual_ledger_terminal_discharge_audit_receipt_orthogonal_nonvacuum :
    Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
        Spectral.SpectralSector.orthogonal ∧
      Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
        Spectral.SpectralSector.vacuum := by
  exact hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.orthogonalNonvacuum

/-- Projection: the terminal audit receipt does not open final release. -/
theorem hard_physical_residual_ledger_terminal_discharge_audit_receipt_final_release_held :
    r1r7TheoremObligationCompletion3320.finalReleaseHeld := by
  exact hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.finalReleaseHeld

/-- Projection: the terminal audit receipt keeps the public boundary locked. -/
theorem hard_physical_residual_ledger_terminal_discharge_audit_receipt_public_boundary_locked :
    r1r7TheoremObligationCompletion3320.publicBoundaryLocked := by
  exact hardPhysicalResidualLedgerTerminalDischargeAuditReceipt3320.publicBoundaryLocked

end MGAP4D
