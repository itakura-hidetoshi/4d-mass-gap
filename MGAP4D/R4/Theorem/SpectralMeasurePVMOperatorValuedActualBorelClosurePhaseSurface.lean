import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelPhaseSurface
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelSetAlgebraClosure

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Surface bundle for the actual-Borel closure phase.

This exposes the move from a mere actual Borel wrapper to explicit Boolean
closure of that wrapper, while preserving the genuine analytic obligations as
open. -/
def SpectralMeasurePVMActualBorelClosurePhaseSurfaceReady : Prop :=
  SpectralMeasurePVMActualBorelPhaseSurfaceReady ∧
  SpectralMeasurePVMActualBorelSetAlgebraClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel closure phase surface is ready. -/
theorem spectral_measure_pvm_actual_borel_closure_phase_surface_ready :
    SpectralMeasurePVMActualBorelClosurePhaseSurfaceReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_phase_surface_ready,
    spectral_measure_pvm_actual_borel_set_algebra_closure_public_boundary_held,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
