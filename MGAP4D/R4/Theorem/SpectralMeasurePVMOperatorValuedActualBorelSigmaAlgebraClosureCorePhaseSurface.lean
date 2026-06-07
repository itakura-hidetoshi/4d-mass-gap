import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelSigmaAlgebraClosureCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Phase surface for the actual-Borel sigma-algebra closure core.

This surface reads the reusable sigma-closure core: finite Boolean closure,
countable union closure, and countable intersection closure for the actual
Borel carrier wrapper.  It keeps the analytic operator-topology and spectral
measure obligations open. -/
def SpectralMeasurePVMActualBorelSigmaAlgebraClosureCorePhaseSurfaceReady : Prop :=
  SpectralMeasurePVMActualBorelSigmaAlgebraClosureCoreReady ∧
  SpectralMeasurePVMActualBorelSigmaAlgebraClosureCorePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelCountableUnionClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelCountableInterClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The phase surface for the actual-Borel sigma-algebra closure core is ready. -/
theorem spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_phase_surface_ready :
    SpectralMeasurePVMActualBorelSigmaAlgebraClosureCorePhaseSurfaceReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_ready,
    spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_public_boundary_held,
    spectral_measure_pvm_actual_borel_countable_union_closure_public_boundary_held,
    spectral_measure_pvm_actual_borel_countable_inter_closure_public_boundary_held,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the actual-Borel sigma-algebra closure core phase surface. -/
def SpectralMeasurePVMActualBorelSigmaAlgebraClosureCorePhaseSurfacePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelSigmaAlgebraClosureCorePhaseSurfaceReady ∧
  SpectralMeasurePVMActualBorelSigmaAlgebraClosureCorePublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the actual-Borel sigma-algebra closure core phase
surface is held. -/
theorem spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_phase_surface_public_boundary_held :
    SpectralMeasurePVMActualBorelSigmaAlgebraClosureCorePhaseSurfacePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_phase_surface_ready,
    spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_public_boundary_held,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
