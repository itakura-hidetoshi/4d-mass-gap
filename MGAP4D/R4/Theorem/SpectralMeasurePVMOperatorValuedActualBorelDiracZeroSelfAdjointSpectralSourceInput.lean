import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroSpectralMeasureConstructionTheorem

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Self-adjoint spectral-source input theorem for the Dirac-zero actual-Borel
route.

The concrete spectral-measure side is now closed for the Dirac-zero route.  This
object records exactly what is handed to the next residual: a genuine
actual-Borel projection-valued spectral-measure construction, with PVM laws and
operator-topology countable additivity already proved.  The remaining task is to
identify it as the spectral measure of a concrete self-adjoint operator. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralSourceInputTheorem : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionPublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The self-adjoint spectral-source input theorem for the Dirac-zero route is
ready as a theorem, not a target. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_spectral_source_input_theorem :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralSourceInputTheorem := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_genuine_operator_topology_convergence_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_public_boundary_held,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The remaining self-adjoint spectral theorem residual has been narrowed to a
source-identification obligation for the Dirac-zero route. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSourceIdentificationResidual : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralSourceInputTheorem ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The narrowed self-adjoint source-identification residual is exposed. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_source_identification_residual :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSourceIdentificationResidual := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_spectral_source_input_theorem,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the Dirac-zero self-adjoint spectral-source input. -/
def SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralSourceInputPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralSourceInputTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSourceIdentificationResidual ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the Dirac-zero self-adjoint spectral-source input is
held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_spectral_source_input_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroSelfAdjointSpectralSourceInputPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_spectral_source_input_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_self_adjoint_source_identification_residual,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
