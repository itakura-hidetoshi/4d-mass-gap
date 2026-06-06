import MGAP4D.R4.TheoremSurface
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelSetWrapper

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Surface bundle for the actual-Borel phase after the endpoint carrier/set-algebra
bridges. This keeps the main theorem surface untouched while exposing the new
actual Borel wrapper bridge. -/
def SpectralMeasurePVMActualBorelPhaseSurfaceReady : Prop :=
  SpectralMeasurePVMActualBorelEndpointSetAlgebraPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelSetWrapperPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel phase surface is ready. -/
theorem spectral_measure_pvm_actual_borel_phase_surface_ready :
    SpectralMeasurePVMActualBorelPhaseSurfaceReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_set_algebra_public_boundary_held,
    spectral_measure_pvm_actual_borel_set_wrapper_public_boundary_held,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
