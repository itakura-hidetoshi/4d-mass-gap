import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDenseDiagonalPVMSourcedDownstreamAdapter
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelR3SelfAdjointPacketHandoff

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Certificate that the dense-diagonal PVM-sourced downstream interface is the
R3 self-adjoint spectral output source for the R4 lane. -/
def SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedSpectralOutputCertificate : Prop :=
  SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamAdapterReady ∧
  SpectralMeasurePVMActualBorelR3SelfAdjointSourcePacketReady ∧
  MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The dense-diagonal PVM-sourced spectral-output certificate is ready. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_spectral_output_certificate :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedSpectralOutputCertificate := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_downstream_adapter_ready,
    spectral_measure_pvm_actual_borel_r3_self_adjoint_source_packet_ready,
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedLawPacket.pvm_input_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R3-sourced spectral-output packet built from the dense-diagonal PVM-sourced
downstream interface rather than from the Dirac-zero interface directly. -/
def spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedR3SelfAdjointSpectralOutputPacket :
    SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputPacket where
  r3_self_adjoint_source_ready :=
    spectral_measure_pvm_actual_borel_r3_self_adjoint_source_packet_ready
  spectral_measure :=
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedDownstreamInterface
  produced_by_r3_self_adjoint_mathlib_spectral_output :=
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedSpectralOutputCertificate
  produced_certificate :=
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_spectral_output_certificate
  no_shell_to_full_collapse_boundary :=
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready

/-- The dense-diagonal PVM-sourced R3 spectral-output packet exists. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_r3_spectral_output_packet_exists :
    SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputExistenceObligation := by
  exact ⟨
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedR3SelfAdjointSpectralOutputPacket,
    True.intro⟩

/-- The dense-diagonal PVM-sourced R3 spectral-output packet discharges the R4
single remaining constructive obligation. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_r3_spectral_output_packet_discharges_single_obligation :
    SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation := by
  exact spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_supplies_r4_obligation
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_r3_spectral_output_packet_exists

/-- Proof packet for the dense-diagonal PVM-sourced R3 spectral-output packet. -/
def SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedSpectralOutputPacketReady : Prop :=
  SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedSpectralOutputCertificate ∧
  SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputExistenceObligation ∧
  SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The proof packet for the dense-diagonal PVM-sourced R3 spectral-output packet is ready. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_spectral_output_packet_ready :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedSpectralOutputPacketReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_spectral_output_certificate,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_r3_spectral_output_packet_exists,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_r3_spectral_output_packet_discharges_single_obligation,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
