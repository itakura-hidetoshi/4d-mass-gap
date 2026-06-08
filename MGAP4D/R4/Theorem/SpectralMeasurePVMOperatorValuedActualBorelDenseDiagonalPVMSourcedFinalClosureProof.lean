import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDenseDiagonalPVMSourcedMathlibOutputProof
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelNontrivialWitnessExistenceClosure

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The dense-diagonal PVM-sourced Mathlib output closes the conditional final R4
actual-Borel route. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_final_closure :
    SpectralMeasurePVMActualBorelPostInterfaceResidualCertificate ∧
    SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  exact spectral_measure_pvm_actual_borel_full_r4_conditional_final_closure
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_mathlib_output_discharges_single_obligation

/-- Final closure receipt for the dense-diagonal PVM-sourced actual-Borel R4
route. -/
def SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedFinalClosureReady : Prop :=
  SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedMathlibOutputProofReady ∧
  SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation ∧
  SpectralMeasurePVMActualBorelPostInterfaceResidualCertificate ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The final closure receipt for the dense-diagonal PVM-sourced actual-Borel R4
route is ready. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_final_closure_ready :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedFinalClosureReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_mathlib_output_proof_ready,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_mathlib_output_discharges_single_obligation,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_final_closure.1,
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_final_closure.2⟩

/-- Public boundary for the dense-diagonal PVM-sourced final closure. -/
def SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedFinalClosurePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedFinalClosureReady ∧
  SpectralMeasurePVMActualBorelFullR4ConditionalFinalClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the dense-diagonal PVM-sourced final closure is held. -/
theorem spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_final_closure_public_boundary_held :
    SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedFinalClosurePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_final_closure_ready,
    spectral_measure_pvm_actual_borel_full_r4_conditional_final_closure_public_boundary_held,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
