import MGAP4D.HardPhysicalResidualLedgerR1R7PublicAuditSurface

namespace MGAP4D

/-- Chain index for the public audit surface of the terminal R1--R7 hard
physical residual discharge.

This is intentionally a thin receipt/index layer.  It exposes the public audit
surface, its exact-value/positive-weight projection, its R4 genuine-PVM law
projection, and its boundary-lock projection without adding release authority. -/
structure HardPhysicalResidualLedgerR1R7PublicAuditChainIndex where
  publicSurfaceReady :
    hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.ready
  exactPositiveProjection :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
      Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
  r4GenuinePVMProjection :
    R4.Theorem.SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem ∧
      R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary
  boundaryLockedProjection :
    r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
      r1r7TheoremObligationCompletion3320.publicBoundaryLocked
  publicAuditChainIndexed : Prop
  publicAuditChainIndexed_proof : publicAuditChainIndexed

/-- Readiness predicate for the public audit chain index. -/
def HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.ready
    (I : HardPhysicalResidualLedgerR1R7PublicAuditChainIndex) : Prop :=
  hardPhysicalResidualLedgerR1R7PublicAuditSurface3320.ready ∧
  (MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
    Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true) ∧
  (R4.Theorem.SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem ∧
    R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary) ∧
  (r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
    r1r7TheoremObligationCompletion3320.publicBoundaryLocked) ∧
  I.publicAuditChainIndexed

/-- Canonical public audit chain index. -/
def hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320 :
    HardPhysicalResidualLedgerR1R7PublicAuditChainIndex :=
  { publicSurfaceReady :=
      hard_physical_residual_ledger_r1_r7_public_audit_surface_3320_ready
    exactPositiveProjection :=
      hard_physical_residual_ledger_public_surface_exact_3320_positive_weight
    r4GenuinePVMProjection :=
      hard_physical_residual_ledger_public_surface_r4_genuine_pvm_laws_visible
    boundaryLockedProjection :=
      hard_physical_residual_ledger_public_surface_boundary_locked
    publicAuditChainIndexed := True
    publicAuditChainIndexed_proof := True.intro }

/-- The canonical public audit chain index is ready. -/
theorem hard_physical_residual_ledger_r1_r7_public_audit_chain_index_3320_ready :
    hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320.ready := by
  exact ⟨
    hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320.publicSurfaceReady,
    hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320.exactPositiveProjection,
    hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320.r4GenuinePVMProjection,
    hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320.boundaryLockedProjection,
    hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320.publicAuditChainIndexed_proof⟩

/-- Projection: the public audit chain preserves exact `33/20` and positive
spectral weight. -/
theorem hard_physical_residual_ledger_public_audit_chain_exact_3320_positive_weight :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
      Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true := by
  exact hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320.exactPositiveProjection

/-- Projection: the public audit chain preserves R4 genuine-PVM law visibility. -/
theorem hard_physical_residual_ledger_public_audit_chain_r4_genuine_pvm_laws_visible :
    R4.Theorem.SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem ∧
      R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  exact hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320.r4GenuinePVMProjection

/-- Projection: the public audit chain remains boundary-locked and non-releasing. -/
theorem hard_physical_residual_ledger_public_audit_chain_boundary_locked :
    r1r7TheoremObligationCompletion3320.finalReleaseHeld ∧
      r1r7TheoremObligationCompletion3320.publicBoundaryLocked := by
  exact hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320.boundaryLockedProjection

end MGAP4D
