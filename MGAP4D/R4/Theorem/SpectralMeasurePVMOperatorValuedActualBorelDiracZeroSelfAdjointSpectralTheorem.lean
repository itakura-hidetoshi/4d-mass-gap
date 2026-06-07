import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroSelfAdjointZeroInnerSymmetry

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Genuine self-adjoint spectral theorem package for the Dirac-zero actual-Borel
route.

This is the route-specific theorem: the source operator is the zero operator,
it is self-adjoint in the inner-product symmetry witness sense, its actual-Borel
spectral projection law is the Dirac law at `0`, and the corresponding
projection-valued spectral-measure construction has already been proved.  This
is deliberately not a claim that the full R4 spectral theorem for the intended
nontrivial Yang--Mills operator has been discharged. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralTheorem : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfaceReceiver ∧
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroInnerSymmetryWitness ∧
  SpectralMeasurePVMActualBorelProjectionOperatorInnerSymmetric
    spectralMeasurePVMActualBorelDiracZeroSourceOperator ∧
  SpectralMeasurePVMActualBorelDiracZeroSourceOperatorZeroLaw ∧
  SpectralMeasurePVMActualBorelDiracZeroSourceProjectionLaw ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsTheorem ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The Dirac-zero actual-Borel self-adjoint spectral theorem route is proved. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_spectral_theorem :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralTheorem := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_mathlib_self_adjoint_interface_receiver,
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_inner_symmetry_witness,
    spectral_measure_pvm_actual_borel_dirac_zero_source_operator_inner_symmetric,
    spectral_measure_pvm_actual_borel_dirac_zero_source_operator_zero_law,
    spectral_measure_pvm_actual_borel_dirac_zero_source_projection_law,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_theorem,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The self-adjoint spectral theorem residual is closed for the Dirac-zero
zero-operator route, while the full nontrivial R4/Yang--Mills operator route
remains separated by the no-shell-to-full-collapse boundary. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralTheoremClosed : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroInnerSymmetryPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsPublicBoundaryHeld ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The Dirac-zero zero-operator self-adjoint spectral theorem route is closed. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_spectral_theorem_closed :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralTheoremClosed := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_spectral_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_inner_symmetry_public_boundary_held,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_public_boundary_held,
    spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_public_boundary_held,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after closing the Dirac-zero self-adjoint spectral theorem
route. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralTheoremPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralTheoremClosed ∧
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralTheorem ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after closing the Dirac-zero self-adjoint spectral theorem
route is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_spectral_theorem_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralTheoremPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_spectral_theorem_closed,
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_spectral_theorem,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
