import Mathlib.Analysis.InnerProductSpace.Continuous
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroMathlibSelfAdjointInterfaceReceiver

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Inner-product symmetry formulation of self-adjointness for an actual-Borel
projection operator.  This is the Mathlib-facing witness form used before
choosing a concrete `IsSelfAdjoint` API name. -/
def SpectralMeasurePVMActualBorelProjectionOperatorInnerSymmetric
    (A : SpectralMeasurePVMActualBorelProjectionOperator) : Prop :=
  ∀ x y : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    inner ℝ (A x) y = inner ℝ x (A y)

/-- The zero source operator is inner-product symmetric, hence self-adjoint in
the witness sense needed by the Dirac-zero spectral-theorem route. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_source_operator_inner_symmetric :
    SpectralMeasurePVMActualBorelProjectionOperatorInnerSymmetric
      spectralMeasurePVMActualBorelDiracZeroSourceOperator := by
  intro x y
  simp [SpectralMeasurePVMActualBorelProjectionOperatorInnerSymmetric,
    spectralMeasurePVMActualBorelDiracZeroSourceOperator]

/-- The Dirac-zero zero-operator source is a concrete self-adjoint witness in the
inner-product symmetry sense. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroInnerSymmetryWitness : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfaceReceiver ∧
  SpectralMeasurePVMActualBorelProjectionOperatorInnerSymmetric
    spectralMeasurePVMActualBorelDiracZeroSourceOperator ∧
  SpectralMeasurePVMActualBorelDiracZeroSourceOperatorZeroLaw ∧
  SpectralMeasurePVMActualBorelDiracZeroSourceProjectionLaw ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The Dirac-zero zero-operator self-adjoint witness is proved by inner-product
symmetry. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_inner_symmetry_witness :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroInnerSymmetryWitness := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_mathlib_self_adjoint_interface_receiver,
    spectral_measure_pvm_actual_borel_dirac_zero_source_operator_inner_symmetric,
    spectral_measure_pvm_actual_borel_dirac_zero_source_operator_zero_law,
    spectral_measure_pvm_actual_borel_dirac_zero_source_projection_law,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- After the inner-symmetry witness, the remaining residual is only the naming /
API connection from this witness to Mathlib's concrete self-adjoint spectral
 theorem interface. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroInnerSymmetryInterfaceResidual : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroInnerSymmetryWitness ∧
  SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfaceResidual ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The inner-symmetry interface residual is exposed. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_inner_symmetry_interface_residual :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroInnerSymmetryInterfaceResidual := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_inner_symmetry_witness,
    spectral_measure_pvm_actual_borel_dirac_zero_mathlib_self_adjoint_interface_residual,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after proving the zero-operator inner-symmetry self-adjoint
witness for the Dirac-zero route. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroInnerSymmetryPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroInnerSymmetryWitness ∧
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroInnerSymmetryInterfaceResidual ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the zero-operator inner-symmetry witness is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_inner_symmetry_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroInnerSymmetryPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_inner_symmetry_witness,
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_inner_symmetry_interface_residual,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
