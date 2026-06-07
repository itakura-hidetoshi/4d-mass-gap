import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoff
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelR3SelfAdjointPacketHandoff

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R3-sourced spectral-output existence obligation for R4.

R3 owns actual self-adjointness.  R4 now needs the law-carrying actual-Borel
spectral-measure output produced from that R3 source. -/
def SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputExistenceObligation : Prop :=
  ∃ P : SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputPacket, True

/-- The concrete dense diagonal input package available to the R4 spectral-output
obligation. -/
def SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputInputReady : Prop :=
  SpectralMeasurePVMActualBorelR3SelfAdjointSourcePacketReady ∧
  MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady ∧
  MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R3-sourced spectral-output input package is ready. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_input_ready :
    SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputInputReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_r3_self_adjoint_source_packet_ready,
    MGAP4D.MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready,
    MGAP4D.MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Projection from the R3-sourced spectral-output obligation to the R4 single
remaining constructive obligation. -/
def SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputObligationProjectionReady : Prop :=
  SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputInputReady ∧
  (SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputExistenceObligation →
    SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation) ∧
  SpectralMeasurePVMActualBorelR3SelfAdjointPacketHandoffBoundaryReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R3-sourced spectral-output obligation projects to the R4 single remaining
constructive obligation. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_obligation_projection_ready :
    SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputObligationProjectionReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_input_ready,
    spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_supplies_r4_obligation,
    spectral_measure_pvm_actual_borel_r3_self_adjoint_packet_handoff_boundary_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the R3-sourced spectral-output obligation projection. -/
def SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputObligationProjectionPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputObligationProjectionReady ∧
  SpectralMeasurePVMActualBorelR3SelfAdjointPacketHandoffBoundaryReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the R3-sourced spectral-output obligation projection is held. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_obligation_projection_public_boundary_held :
    SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputObligationProjectionPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_obligation_projection_ready,
    spectral_measure_pvm_actual_borel_r3_self_adjoint_packet_handoff_boundary_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
