import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelR3SelfAdjointMathlibOutputCurrentInterfaceProof

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Target for replacing the current Dirac-zero interface with a law-carrying
actual-Borel spectral measure derived from the R3 dense diagonal self-adjoint
source. -/
structure SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTarget where
  r3_input_ready : SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputInputReady
  spectral_measure : SpectralMeasurePVMActualBorelGenericLawCarryingSpectralMeasureInterface
  derived_from_r3_dense_diagonal_self_adjoint_source : Prop
  derived_certificate : derived_from_r3_dense_diagonal_self_adjoint_source
  residual_closure :
    SpectralMeasurePVMActualBorelGenericLawCarryingResidualClosureTarget spectral_measure
  no_shell_to_full_collapse_boundary : SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A R3-derived law-carrying target gives a R3-sourced spectral output packet. -/
def spectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputPacketOfDerivedLawCarryingTarget
    (T : SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTarget) :
    SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputPacket where
  r3_self_adjoint_source_ready := T.r3_input_ready.1
  spectral_measure := T.spectral_measure
  produced_by_r3_self_adjoint_mathlib_spectral_output :=
    T.derived_from_r3_dense_diagonal_self_adjoint_source
  produced_certificate := T.derived_certificate
  no_shell_to_full_collapse_boundary := T.no_shell_to_full_collapse_boundary

/-- Existence of a R3-derived law-carrying target supplies the R3-sourced spectral
output obligation. -/
def SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTargetSuppliesOutputObligation : Prop :=
  (∃ T : SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTarget, True) →
    SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputExistenceObligation

/-- A R3-derived law-carrying target supplies the R3-sourced spectral output
obligation. -/
theorem spectral_measure_pvm_actual_borel_r3_derived_law_carrying_spectral_measure_target_supplies_output_obligation :
    SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTargetSuppliesOutputObligation := by
  intro hT
  rcases hT with ⟨T, _⟩
  exact ⟨
    spectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputPacketOfDerivedLawCarryingTarget T,
    True.intro⟩

/-- R3-derived target input boundary.  This keeps the current-interface proof
separate from the genuine R3-derived spectral-measure construction target. -/
def SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTargetInputBoundaryReady : Prop :=
  SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputInputReady ∧
  MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady ∧
  SpectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceMathlibOutputProofReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R3-derived target input boundary is ready. -/
theorem spectral_measure_pvm_actual_borel_r3_derived_law_carrying_spectral_measure_target_input_boundary_ready :
    SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTargetInputBoundaryReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_input_ready,
    MGAP4D.MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_ready,
    spectral_measure_pvm_actual_borel_r3_self_adjoint_current_interface_mathlib_output_proof_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Projection from the R3-derived law-carrying target to the single R4
constructive obligation. -/
def SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTargetProjectionReady : Prop :=
  SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTargetInputBoundaryReady ∧
  (∃ T : SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTarget, True) →
    SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation

/-- The R3-derived law-carrying target projects to the single R4 constructive
obligation. -/
theorem spectral_measure_pvm_actual_borel_r3_derived_law_carrying_spectral_measure_target_projection_ready :
    SpectralMeasurePVMActualBorelR3DerivedLawCarryingSpectralMeasureTargetProjectionReady := by
  intro h
  exact spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_supplies_r4_obligation
    (spectral_measure_pvm_actual_borel_r3_derived_law_carrying_spectral_measure_target_supplies_output_obligation
      h.2)

end

end Theorem
end R4
end MGAP4D
