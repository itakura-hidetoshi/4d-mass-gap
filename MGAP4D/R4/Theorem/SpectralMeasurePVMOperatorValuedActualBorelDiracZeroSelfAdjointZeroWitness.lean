import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroSelfAdjointZeroOperatorSource

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Zero-operator witness input for the Dirac-zero self-adjoint spectral-theorem
route.

This theorem package is intentionally placed just before the full Mathlib
self-adjoint spectral theorem API.  It records that the source operator is the
zero operator, that the actual-Borel spectral projection is the Dirac law at
`0`, and that the Dirac-zero actual-Borel spectral-measure construction is
already available as a genuine theorem. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroWitnessInputTheorem : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroOperatorSourceIdentified ∧
  SpectralMeasurePVMActualBorelDiracZeroSourceOperatorZeroLaw ∧
  SpectralMeasurePVMActualBorelDiracZeroSourceProjectionLaw ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsTheorem ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The zero-operator witness input theorem for the Dirac-zero route is proved. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_witness_input_theorem :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroWitnessInputTheorem := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_operator_source_identified,
    spectral_measure_pvm_actual_borel_dirac_zero_source_operator_zero_law,
    spectral_measure_pvm_actual_borel_dirac_zero_source_projection_law,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_theorem,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The self-adjoint residual is now reduced to connecting this zero-operator
witness input to the concrete Mathlib self-adjoint spectral theorem interface. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointMathlibInterfaceResidual : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroWitnessInputTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroOperatorSourcePublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The remaining Mathlib self-adjoint interface residual is exposed. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_mathlib_interface_residual :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointMathlibInterfaceResidual := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_witness_input_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_operator_source_public_boundary_held,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after forming the Dirac-zero zero-operator witness input for
the self-adjoint spectral theorem route. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroWitnessPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroWitnessInputTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointMathlibInterfaceResidual ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after forming the Dirac-zero zero-operator witness input
is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_witness_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroWitnessPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_witness_input_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_mathlib_interface_residual,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
