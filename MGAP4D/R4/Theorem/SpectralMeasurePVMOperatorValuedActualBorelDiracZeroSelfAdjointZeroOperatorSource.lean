import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroSelfAdjointSpectralSourceInput

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Zero operator source for the Dirac-zero actual-Borel spectral measure route. -/
def spectralMeasurePVMActualBorelDiracZeroSourceOperator :
    SpectralMeasurePVMActualBorelProjectionOperator :=
  0

/-- The Dirac-zero source operator is the zero operator. -/
def SpectralMeasurePVMActualBorelDiracZeroSourceOperatorZeroLaw : Prop :=
  spectralMeasurePVMActualBorelDiracZeroSourceOperator = 0 ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelDiracZeroSourceOperator x = 0)

/-- The Dirac-zero source operator satisfies the zero law. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_source_operator_zero_law :
    SpectralMeasurePVMActualBorelDiracZeroSourceOperatorZeroLaw := by
  constructor
  · rfl
  · intro x
    rfl

/-- Pointwise Dirac-zero source law: the spectral projection for a Borel set is
identity exactly when the source eigenvalue `0` belongs to the set, and zero
otherwise. -/
def SpectralMeasurePVMActualBorelDiracZeroSourceProjectionLaw : Prop :=
  ∀ s : SpectralMeasurePVMActualBorelCarrierSet,
    spectralMeasurePVMActualBorelDiracZeroProjectionMap s =
      if (0 : ℝ) ∈ s.1 then
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier
      else
        0

/-- The Dirac-zero source projection law holds by definition of the Dirac-zero
projection map. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_source_projection_law :
    SpectralMeasurePVMActualBorelDiracZeroSourceProjectionLaw := by
  classical
  intro s
  simp [SpectralMeasurePVMActualBorelDiracZeroSourceProjectionLaw,
    spectralMeasurePVMActualBorelDiracZeroProjectionMap]

/-- The Dirac-zero spectral measure is identified with the zero-operator source.

This does not yet invoke Mathlib's full self-adjoint spectral theorem API.  It
closes the source-identification part for this route: the constructed
actual-Borel spectral measure is the Dirac spectral measure at the source
operator value `0`. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroOperatorSourceIdentified : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralSourceInputTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSourceOperatorZeroLaw ∧
  SpectralMeasurePVMActualBorelDiracZeroSourceProjectionLaw ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsTheorem ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The Dirac-zero spectral measure is identified with the zero-operator source. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_operator_source_identified :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroOperatorSourceIdentified := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_spectral_source_input_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_source_operator_zero_law,
    spectral_measure_pvm_actual_borel_dirac_zero_source_projection_law,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_theorem,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after identifying the Dirac-zero route with the zero-operator
source. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroOperatorSourcePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroOperatorSourceIdentified ∧
  SpectralMeasurePVMActualBorelDiracZeroSourceProjectionLaw ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after identifying the Dirac-zero route with the
zero-operator source is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_operator_source_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroOperatorSourcePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_operator_source_identified,
    spectral_measure_pvm_actual_borel_dirac_zero_source_projection_law,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
