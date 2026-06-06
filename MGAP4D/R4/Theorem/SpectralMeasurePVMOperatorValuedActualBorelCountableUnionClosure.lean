import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelSetAlgebraClosure

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Countable union operation on the actual Borel carrier wrapper. -/
def spectralMeasurePVMActualBorelCarrierSetIUnion
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMActualBorelCarrierSet :=
  ⟨⋃ n, (F n).1, by
    exact MeasurableSet.iUnion (fun n => (F n).2)⟩

/-- Countable union on the wrapper forgets to countable union on `Set ℝ`. -/
theorem spectral_measure_pvm_actual_borel_carrier_set_iUnion_forget
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet) :
    (spectralMeasurePVMActualBorelCarrierSetIUnion F).1 = ⋃ n, (F n).1 := by
  rfl

/-- Closure target for countable unions of actual Borel carrier sets. -/
def SpectralMeasurePVMActualBorelCountableUnionClosureTarget : Prop :=
  ∀ F : ℕ → SpectralMeasurePVMActualBorelCarrierSet,
    ∃ u : SpectralMeasurePVMActualBorelCarrierSet, u.1 = ⋃ n, (F n).1

/-- The actual Borel carrier wrapper is closed under countable unions. -/
theorem spectral_measure_pvm_actual_borel_countable_union_closure_target_ready :
    SpectralMeasurePVMActualBorelCountableUnionClosureTarget := by
  intro F
  exact ⟨spectralMeasurePVMActualBorelCarrierSetIUnion F, rfl⟩

/-- Endpoint sanity target for countable unions: the constant-empty family has
empty union after forgetting to `Set ℝ`. -/
def SpectralMeasurePVMActualBorelCountableUnionEndpointTarget : Prop :=
  (spectralMeasurePVMActualBorelCarrierSetIUnion
      (fun _ : ℕ => spectralMeasurePVMActualBorelEmptySet)).1 = (∅ : Set ℝ)

/-- Endpoint sanity for the constant-empty countable union. -/
theorem spectral_measure_pvm_actual_borel_countable_union_endpoint_target_ready :
    SpectralMeasurePVMActualBorelCountableUnionEndpointTarget := by
  dsimp [SpectralMeasurePVMActualBorelCountableUnionEndpointTarget,
    spectralMeasurePVMActualBorelCarrierSetIUnion,
    spectralMeasurePVMActualBorelEmptySet]
  ext x
  simp

/-- Actual-Borel countable-union closure bridge.

This strengthens the arbitrary Borel carrier wrapper from finite Boolean closure
to countable-union closure, still without asserting operator-topology countable
additivity or a completed spectral theorem. -/
def SpectralMeasurePVMActualBorelCountableUnionClosureBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelSetAlgebraClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelCountableUnionClosureTarget ∧
  SpectralMeasurePVMActualBorelCountableUnionEndpointTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel countable-union closure bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_countable_union_closure_bridge_ready :
    SpectralMeasurePVMActualBorelCountableUnionClosureBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_set_algebra_closure_public_boundary_held,
    spectral_measure_pvm_actual_borel_countable_union_closure_target_ready,
    spectral_measure_pvm_actual_borel_countable_union_endpoint_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual-Borel countable-union closure bridge. -/
def SpectralMeasurePVMActualBorelCountableUnionClosurePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelCountableUnionClosureBridgeReady ∧
  SpectralMeasurePVMActualBorelCountableUnionClosureTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual-Borel countable-union closure bridge is held. -/
theorem spectral_measure_pvm_actual_borel_countable_union_closure_public_boundary_held :
    SpectralMeasurePVMActualBorelCountableUnionClosurePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_countable_union_closure_bridge_ready,
    spectral_measure_pvm_actual_borel_countable_union_closure_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
