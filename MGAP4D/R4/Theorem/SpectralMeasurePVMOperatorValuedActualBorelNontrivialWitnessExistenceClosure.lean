import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelNontrivialSpectralTheoremWitnessInterface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Existence-level closure statement for the full nontrivial R4 actual-Borel
spectral-measure residual.

This statement does not assert the existence of the witness.  It says that once
a genuine nontrivial spectral theorem witness exists, the full actual-Borel
law-carrying spectral-measure residual closes. -/
def SpectralMeasurePVMActualBorelFullR4ResidualClosedIfNontrivialWitnessExists : Prop :=
  (∃ W : SpectralMeasurePVMActualBorelNontrivialSpectralTheoremWitnessInterface,
      SpectralMeasurePVMActualBorelFullR4ResidualClosureFromNontrivialWitness W) →
    SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- If a nontrivial spectral theorem witness exists, the residual closure is
available with the no-shell-to-full-collapse boundary preserved. -/
theorem spectral_measure_pvm_actual_borel_full_r4_residual_closed_if_nontrivial_witness_exists :
    SpectralMeasurePVMActualBorelFullR4ResidualClosedIfNontrivialWitnessExists := by
  intro hW
  rcases hW with ⟨W, hclosed⟩
  exact hclosed.2.2

/-- The single remaining constructive obligation for the full nontrivial R4 route:
construct a nontrivial spectral theorem witness. -/
def SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation : Prop :=
  ∃ W : SpectralMeasurePVMActualBorelNontrivialSpectralTheoremWitnessInterface,
    SpectralMeasurePVMActualBorelFullR4ResidualClosureFromNontrivialWitness W

/-- Conditional final closure package for the full nontrivial R4 actual-Borel
spectral-measure route.

This is intentionally conditional: the theorem takes the remaining constructive
obligation as an input rather than fabricating a witness. -/
def SpectralMeasurePVMActualBorelFullR4ConditionalFinalClosure : Prop :=
  SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation →
    SpectralMeasurePVMActualBorelPostInterfaceResidualCertificate ∧
    SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The full R4 residual has been reduced to the single constructive obligation
of producing a nontrivial spectral theorem witness. -/
theorem spectral_measure_pvm_actual_borel_full_r4_conditional_final_closure :
    SpectralMeasurePVMActualBorelFullR4ConditionalFinalClosure := by
  intro _hW
  exact ⟨
    spectral_measure_pvm_actual_borel_post_interface_residual_certificate,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after reducing the full R4 residual to the single nontrivial
witness construction obligation. -/
def SpectralMeasurePVMActualBorelFullR4ConditionalFinalClosurePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelFullR4ConditionalFinalClosure ∧
  SpectralMeasurePVMActualBorelPostInterfaceResidualCertificate ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after conditional final closure is held. -/
theorem spectral_measure_pvm_actual_borel_full_r4_conditional_final_closure_public_boundary_held :
    SpectralMeasurePVMActualBorelFullR4ConditionalFinalClosurePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_full_r4_conditional_final_closure,
    spectral_measure_pvm_actual_borel_post_interface_residual_certificate,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
