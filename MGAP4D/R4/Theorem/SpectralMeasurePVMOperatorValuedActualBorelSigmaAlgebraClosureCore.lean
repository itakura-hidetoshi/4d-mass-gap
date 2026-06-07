import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelCountableInterClosure

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Sigma-algebra closure core for the actual Borel carrier wrapper.

This is stronger than the earlier finite Boolean closure: it records complement,
finite union/intersection, countable union, and countable intersection closure on
the actual subtype `{s : Set ℝ // MeasurableSet s}`.  It still does not assert
operator-topology countable additivity or the self-adjoint spectral theorem.

The countable-intersection operation and its endpoint sanity theorem live in
`SpectralMeasurePVMOperatorValuedActualBorelCountableInterClosure`; this core
imports and reuses them rather than redeclaring the same fully-qualified names. -/
def SpectralMeasurePVMActualBorelSigmaAlgebraClosureCoreReady : Prop :=
  SpectralMeasurePVMActualBorelSetAlgebraClosureTarget ∧
  SpectralMeasurePVMActualBorelCountableUnionClosureTarget ∧
  SpectralMeasurePVMActualBorelCountableInterClosureTarget ∧
  SpectralMeasurePVMActualBorelCountableUnionEndpointTarget ∧
  SpectralMeasurePVMActualBorelCountableInterEndpointTarget ∧
  SpectralMeasurePVMActualBorelCountableInterClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The sigma-algebra closure core for the actual Borel carrier wrapper is ready. -/
theorem spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_ready :
    SpectralMeasurePVMActualBorelSigmaAlgebraClosureCoreReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_set_algebra_closure_target_ready,
    spectral_measure_pvm_actual_borel_countable_union_closure_target_ready,
    spectral_measure_pvm_actual_borel_countable_inter_closure_target_ready,
    spectral_measure_pvm_actual_borel_countable_union_endpoint_target_ready,
    spectral_measure_pvm_actual_borel_countable_inter_endpoint_target_ready,
    spectral_measure_pvm_actual_borel_countable_inter_closure_public_boundary_held,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual-Borel sigma-algebra closure core. -/
def SpectralMeasurePVMActualBorelSigmaAlgebraClosureCorePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelSigmaAlgebraClosureCoreReady ∧
  SpectralMeasurePVMActualBorelCountableUnionClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelCountableInterClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual-Borel sigma-algebra closure core is held. -/
theorem spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_public_boundary_held :
    SpectralMeasurePVMActualBorelSigmaAlgebraClosureCorePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_sigma_algebra_closure_core_ready,
    spectral_measure_pvm_actual_borel_countable_union_closure_public_boundary_held,
    spectral_measure_pvm_actual_borel_countable_inter_closure_public_boundary_held,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
