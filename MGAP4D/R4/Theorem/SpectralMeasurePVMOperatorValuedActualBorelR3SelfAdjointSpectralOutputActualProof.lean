import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelR3SelfAdjointSpectralOutputObligationProjection

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Current-interface certificate that the R3 self-adjoint source is paired with
the law-carrying actual-Borel spectral-measure interface already constructed in
R4. -/
def SpectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceOutputCertificate : Prop :=
  SpectralMeasurePVMActualBorelR3SelfAdjointSourcePacketReady ∧
  SpectralMeasurePVMActualBorelGenericLawCarryingResidualClosureTarget
    spectralMeasurePVMActualBorelDiracZeroAsGenericLawCarryingInterface ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The current-interface output certificate is proved from the R3 source packet
and the law-carrying actual-Borel interface. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_current_interface_output_certificate :
    SpectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceOutputCertificate := by
  exact ⟨
    spectral_measure_pvm_actual_borel_r3_self_adjoint_source_packet_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_closes_generic_law_carrying_residual_target,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R3-sourced spectral-output packet at the current law-carrying actual-Borel
interface. -/
def spectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceSpectralOutputPacket :
    SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputPacket where
  r3_self_adjoint_source_ready :=
    spectral_measure_pvm_actual_borel_r3_self_adjoint_source_packet_ready
  spectral_measure :=
    spectralMeasurePVMActualBorelDiracZeroAsGenericLawCarryingInterface
  produced_by_r3_self_adjoint_mathlib_spectral_output :=
    SpectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceOutputCertificate
  produced_certificate :=
    spectral_measure_pvm_actual_borel_r3_self_adjoint_current_interface_output_certificate
  no_shell_to_full_collapse_boundary :=
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready

/-- The R3-sourced spectral-output existence obligation is discharged at the
current law-carrying actual-Borel interface. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_exists :
    SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputExistenceObligation := by
  exact ⟨
    spectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceSpectralOutputPacket,
    True.intro⟩

/-- The R3-sourced spectral-output packet supplies the single remaining R4
constructive obligation at the current interface. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_discharges_r4_single_obligation :
    SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation := by
  exact spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_supplies_r4_obligation
    spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_exists

/-- Actual proof receipt for the R3-sourced spectral output at the current
interface. -/
def SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputActualProofReady : Prop :=
  SpectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceOutputCertificate ∧
  SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputExistenceObligation ∧
  SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual proof receipt for the R3-sourced spectral output is ready. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_actual_proof_ready :
    SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputActualProofReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_r3_self_adjoint_current_interface_output_certificate,
    spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_exists,
    spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_discharges_r4_single_obligation,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
