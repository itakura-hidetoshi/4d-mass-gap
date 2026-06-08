import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDenseDiagonalPVMSourcedSpectralOutputPacket

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Mathlib nontrivial spectral output produced from the dense-diagonal
PVM-sourced R3 spectral-output packet. -/
def spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedMathlibOutput :
    SpectralMeasurePVMActualBorelMathlibNontrivialSpectralOutput :=
  spectralMeasurePVMActualBorelMathlibOutputOfR3SelfAdjointSpectralOutputPacket
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedR3SelfAdjointSpectralOutputPacket

/-- The dense-diagonal PVM-sourced Mathlib output exists. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_mathlib_output_exists :
    ∃ O : SpectralMeasurePVMActualBorelMathlibNontrivialSpectralOutput, True := by
  exact ⟨spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedMathlibOutput, True.intro⟩

/-- The dense-diagonal PVM-sourced Mathlib output closes the full R4 residual via
the nontrivial witness interface. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_mathlib_output_closes_full_r4_residual :
    SpectralMeasurePVMActualBorelFullR4ResidualClosureFromNontrivialWitness
      (spectralMeasurePVMActualBorelNontrivialWitnessOfMathlibSpectralOutput
        spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedMathlibOutput) := by
  exact spectral_measure_pvm_actual_borel_mathlib_nontrivial_spectral_output_closes_full_r4_residual
    spectralMeasurePVMActualBorelDenseDiagonalPVMSourcedMathlibOutput

/-- The dense-diagonal PVM-sourced Mathlib output discharges the single remaining
R4 constructive obligation. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_mathlib_output_discharges_single_obligation :
    SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation := by
  exact spectral_measure_pvm_actual_borel_mathlib_output_supplies_single_remaining_obligation
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_mathlib_output_exists

/-- Proof packet for the dense-diagonal PVM-sourced Mathlib output. -/
def SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedMathlibOutputProofReady : Prop :=
  (∃ O : SpectralMeasurePVMActualBorelMathlibNontrivialSpectralOutput, True) ∧
  SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation ∧
  SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedSpectralOutputPacketReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The proof packet for the dense-diagonal PVM-sourced Mathlib output is ready. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_mathlib_output_proof_ready :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedMathlibOutputProofReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_mathlib_output_exists,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_mathlib_output_discharges_single_obligation,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_spectral_output_packet_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
