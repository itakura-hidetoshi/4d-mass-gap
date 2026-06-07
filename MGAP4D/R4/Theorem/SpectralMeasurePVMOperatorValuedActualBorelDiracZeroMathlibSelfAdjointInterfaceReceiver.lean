import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroSelfAdjointZeroWitness

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Mathlib self-adjoint interface receiver for the Dirac-zero route.

This receiver is the exact input shape expected by the next, fully Mathlib-facing
step: the zero-operator witness is available, the Dirac-zero spectral measure is
constructed as a genuine theorem, and the remaining open item is only the direct
connection to the concrete Mathlib self-adjoint spectral theorem API. -/
def SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfaceReceiver : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroWitnessInputTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointZeroOperatorSourceIdentified ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSourceProjectionLaw ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The Dirac-zero zero-operator witness supplies the Mathlib self-adjoint
interface receiver. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_mathlib_self_adjoint_interface_receiver :
    SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfaceReceiver := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_witness_input_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_zero_operator_source_identified,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_source_projection_law,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The self-adjoint spectral theorem residual after the receiver is formed.

After this point, there should be no remaining actual-Borel/PVM/countable-
additivity work in the residual.  The only remaining task is to instantiate the
Mathlib self-adjoint spectral theorem API for the zero operator and identify its
spectral measure with the Dirac-zero construction. -/
def SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfaceResidual : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfaceReceiver ∧
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointMathlibInterfaceResidual ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The remaining self-adjoint spectral theorem residual is now isolated at the
Mathlib interface. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_mathlib_self_adjoint_interface_residual :
    SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfaceResidual := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_mathlib_self_adjoint_interface_receiver,
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_mathlib_interface_residual,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after forming the Dirac-zero Mathlib self-adjoint interface
receiver. -/
def SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfacePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfaceReceiver ∧
  SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfaceResidual ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after forming the Dirac-zero Mathlib self-adjoint
interface receiver is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_mathlib_self_adjoint_interface_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroMathlibSelfAdjointInterfacePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_mathlib_self_adjoint_interface_receiver,
    spectral_measure_pvm_actual_borel_dirac_zero_mathlib_self_adjoint_interface_residual,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
