import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelCountableUnionClosure

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Countable intersection operation on the actual Borel carrier wrapper. -/
def spectralMeasurePVMActualBorelCarrierSetIInter
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMActualBorelCarrierSet :=
  ⟨⋂ n, (F n).1, by
    exact MeasurableSet.iInter (fun n => (F n).2)⟩

/-- Countable intersection on the wrapper forgets to countable intersection on `Set ℝ`. -/
theorem spectral_measure_pvm_actual_borel_carrier_set_iInter_forget
    (F : ℕ → SpectralMeasurePVMActualBorelCarrierSet) :
    (spectralMeasurePVMActualBorelCarrierSetIInter F).1 = ⋂ n, (F n).1 := by
  rfl

/-- Closure target for countable intersections of actual Borel carrier sets. -/
def SpectralMeasurePVMActualBorelCountableInterClosureTarget : Prop :=
  ∀ F : ℕ → SpectralMeasurePVMActualBorelCarrierSet,
    ∃ u : SpectralMeasurePVMActualBorelCarrierSet, u.1 = ⋂ n, (F n).1

/-- The actual Borel carrier wrapper is closed under countable intersections. -/
theorem spectral_measure_pvm_actual_borel_countable_inter_closure_target_ready :
    SpectralMeasurePVMActualBorelCountableInterClosureTarget := by
  intro F
  exact ⟨spectralMeasurePVMActualBorelCarrierSetIInter F, rfl⟩

/-- Endpoint sanity target for countable intersections: the constant-universal family
has universal intersection after forgetting to `Set ℝ`. -/
def SpectralMeasurePVMActualBorelCountableInterEndpointTarget : Prop :=
  (spectralMeasurePVMActualBorelCarrierSetIInter
      (fun _ : ℕ => spectralMeasurePVMActualBorelUnivSet)).1 = (Set.univ : Set ℝ)

/-- Endpoint sanity for the constant-universal countable intersection. -/
theorem spectral_measure_pvm_actual_borel_countable_inter_endpoint_target_ready :
    SpectralMeasurePVMActualBorelCountableInterEndpointTarget := by
  dsimp [SpectralMeasurePVMActualBorelCountableInterEndpointTarget,
    spectralMeasurePVMActualBorelCarrierSetIInter,
    spectralMeasurePVMActualBorelUnivSet]
  ext x
  simp

/-- Actual-Borel countable-intersection closure bridge.

This adds the countable-intersection side of the Borel carrier wrapper closure,
still without asserting operator-topology countable additivity or a completed
spectral theorem. -/
def SpectralMeasurePVMActualBorelCountableInterClosureBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelCountableUnionClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelCountableInterClosureTarget ∧
  SpectralMeasurePVMActualBorelCountableInterEndpointTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel countable-intersection closure bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_countable_inter_closure_bridge_ready :
    SpectralMeasurePVMActualBorelCountableInterClosureBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_countable_union_closure_public_boundary_held,
    spectral_measure_pvm_actual_borel_countable_inter_closure_target_ready,
    spectral_measure_pvm_actual_borel_countable_inter_endpoint_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual-Borel countable-intersection closure bridge. -/
def SpectralMeasurePVMActualBorelCountableInterClosurePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelCountableInterClosureBridgeReady ∧
  SpectralMeasurePVMActualBorelCountableInterClosureTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual-Borel countable-intersection closure bridge is held. -/
theorem spectral_measure_pvm_actual_borel_countable_inter_closure_public_boundary_held :
    SpectralMeasurePVMActualBorelCountableInterClosurePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_countable_inter_closure_bridge_ready,
    spectral_measure_pvm_actual_borel_countable_inter_closure_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
