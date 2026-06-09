import MGAP4D.HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex

namespace MGAP4D

/-- Public audit surface for the terminal R1--R7 hard physical residual discharge.

This surface exposes the terminal discharge receipts in a compact form:
R1--R7 discharge, exact `33/20`, positive spectral weight, R4 genuine-PVM law
visibility, and the public/final boundary locks.  It remains a receipt layer and
carries no automatic final-release authority. -/
structure HardPhysicalResidualLedgerR1R7PublicAuditSurface where
  terminalIndexReady :
    hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.ready
  terminalDischarged :
    hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.r1R7TerminalDischarged
  exactValueEq3320 : MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
  positiveMassProof :
    Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
  r4CountableAdditivityAtTerminal :
    R4.Theorem.SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem
  r4NoShellBoundaryAtTerminal :
    R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary
  finalReleaseHeld : r1r7TheoremObligationCompletion3320.finalReleaseHeld
  publicBoundaryLocked : r1r7TheoremObligationCompletion3320.publicBoundaryLocked
  publicAuditSurfaceClosed : Prop
  publicAuditSurfaceClosed_proof : publicAuditSurfaceClosed

/-- Readiness predicate for the public audit surface. -/
def HardPhysicalResidualLedgerR1R7PublicAuditSurface.ready
    (S : HardPhysicalResidualLedgerR1R7PublicAuditSurface) : Prop :=
  hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.ready ∧
  hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.r1R7TerminalDischarged ∧
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true ∧
  R4.Theorem.SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem ∧
  R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary ∧
  r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
  r1r7TheoremObligationCompletion3320.publicBoundaryLocked ∧
  S.publicAuditSurfaceClosed

/-- Canonical public audit surface for the R1--R7 terminal discharge. -/
def hardPhysicalResidualLedgerR1R7PublicAuditSurface3320 :
    HardPhysicalResidualLedgerR1R7PublicAuditSurface :=
  { terminalIndexReady :=
      hard_physical_residual_ledger_r1_r7_terminal_discharge_chain_index_3320_ready
    terminalDischarged :=
      hard_physical_residual_ledger_r1_r7_terminal_discharged
    exactValueEq3320 :=
      hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.exactValueEq3320
    positiveMassProof :=
      hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.positiveMassProof
    r4CountableAdditivityAtTerminal :=
      hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.r4CountableAdditivityAtTerminal
    r4NoShellBoundaryAtTerminal :=
      hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.r4NoShellBoundaryAtTerminal
    finalReleaseHeld :=
      hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.finalReleaseHeld
    publicBoundaryLocked :=
      hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320.publicBoundaryLocked
    publicAuditSurfaceClosed := True
    publicAuditSurfaceClosed_proof := True.intro }

/-- The canonical R1--R7 public audit surface is ready. -/
theorem hard_physical_residual_ledger_r1_r7_public_audit_surface_3320_ready :
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.ready := by
  exact ⟨
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.terminalIndexReady,
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.terminalDischarged,
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.exactValueEq3320,
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.positiveMassProof,
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.r4CountableAdditivityAtTerminal,
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.r4NoShellBoundaryAtTerminal,
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.finalReleaseHeld,
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.publicBoundaryLocked,
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.publicAuditSurfaceClosed_proof⟩

/-- Projection: the public audit surface records exact `33/20` and positive
spectral weight. -/
theorem hard_physical_residual_ledger_public_surface_exact_3320_positive_weight :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
      Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true := by
  exact ⟨
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.exactValueEq3320,
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.positiveMassProof⟩

/-- Projection: the public audit surface keeps R4 genuine-PVM law receipts
visible at terminal discharge. -/
theorem hard_physical_residual_ledger_public_surface_r4_genuine_pvm_laws_visible :
    R4.Theorem.SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem ∧
      R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  exact ⟨
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.r4CountableAdditivityAtTerminal,
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.r4NoShellBoundaryAtTerminal⟩

/-- Projection: the public audit surface remains non-releasing. -/
theorem hard_physical_residual_ledger_public_surface_boundary_locked :
    r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
      r1r7TheoremObligationCompletion3320.publicBoundaryLocked := by
  exact ⟨
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.finalReleaseHeld,
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.publicBoundaryLocked⟩

end MGAP4D
