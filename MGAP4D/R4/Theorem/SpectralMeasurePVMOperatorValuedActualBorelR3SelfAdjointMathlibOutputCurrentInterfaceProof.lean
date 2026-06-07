import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelR3SelfAdjointSpectralOutputActualProof

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Current-interface Mathlib-output packet obtained from the R3-sourced spectral
output packet. -/
def spectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceMathlibOutput :
    SpectralMeasurePVMActualBorelMathlibNontrivialSpectralOutput :=
  spectralMeasurePVMActualBorelMathlibOutputOfR3SelfAdjointSpectralOutputPacket
    spectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceSpectralOutputPacket

/-- At the current interface, the R3-sourced packet gives existence of the
Mathlib-output object expected by the R4 bridge. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_current_interface_mathlib_output_exists :
    ∃ O : SpectralMeasurePVMActualBorelMathlibNontrivialSpectralOutput, True := by
  exact ⟨spectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceMathlibOutput, True.intro⟩

/-- The current-interface Mathlib-output object closes the full R4 residual via
the nontrivial witness interface. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_current_interface_mathlib_output_closes_full_r4_residual :
    SpectralMeasurePVMActualBorelFullR4ResidualClosureFromNontrivialWitness
      (spectralMeasurePVMActualBorelNontrivialWitnessOfMathlibSpectralOutput
        spectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceMathlibOutput) := by
  exact spectral_measure_pvm_actual_borel_mathlib_nontrivial_spectral_output_closes_full_r4_residual
    spectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceMathlibOutput

/-- The current-interface Mathlib output supplies the single remaining R4
constructive obligation. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_current_interface_mathlib_output_discharges_single_obligation :
    SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation := by
  exact spectral_measure_pvm_actual_borel_mathlib_output_supplies_single_remaining_obligation
    spectral_measure_pvm_actual_borel_r3_self_adjoint_current_interface_mathlib_output_exists

/-- Proof receipt for the current-interface Mathlib-output existence obtained
from the R3 self-adjoint source. -/
def SpectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceMathlibOutputProofReady : Prop :=
  (∃ O : SpectralMeasurePVMActualBorelMathlibNontrivialSpectralOutput, True) ∧
  SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation ∧
  SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputActualProofReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The proof receipt for the current-interface Mathlib output is ready. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_current_interface_mathlib_output_proof_ready :
    SpectralMeasurePVMActualBorelR3SelfAdjointCurrentInterfaceMathlibOutputProofReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_r3_self_adjoint_current_interface_mathlib_output_exists,
    spectral_measure_pvm_actual_borel_r3_self_adjoint_current_interface_mathlib_output_discharges_single_obligation,
    spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_actual_proof_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
