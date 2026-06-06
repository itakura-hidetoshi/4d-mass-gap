import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelEndpointSetAlgebra

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The genuine `Set ℝ`-based Borel carrier wrapper for the next R4 phase.

This is still only the carrier/wrapper layer: an element is an actual subset of
`ℝ` together with its `MeasurableSet` witness. It deliberately does not assert
operator-valued countable additivity or the self-adjoint spectral theorem. -/
def SpectralMeasurePVMActualBorelCarrierSet :=
  { s : Set ℝ // MeasurableSet s }

/-- Constructor for the actual Borel carrier wrapper. -/
def spectralMeasurePVMActualBorelCarrierSetOf
    (s : Set ℝ) (hs : MeasurableSet s) :
    SpectralMeasurePVMActualBorelCarrierSet :=
  ⟨s, hs⟩

/-- The empty actual Borel carrier. -/
def spectralMeasurePVMActualBorelEmptySet :
    SpectralMeasurePVMActualBorelCarrierSet :=
  ⟨∅, by simp⟩

/-- The whole actual Borel carrier. -/
def spectralMeasurePVMActualBorelUnivSet :
    SpectralMeasurePVMActualBorelCarrierSet :=
  ⟨Set.univ, by simp⟩

/-- Complement operation on the actual Borel carrier wrapper. -/
def spectralMeasurePVMActualBorelCarrierSetCompl
    (s : SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMActualBorelCarrierSet :=
  ⟨s.1ᶜ, s.2.compl⟩

/-- Union operation on the actual Borel carrier wrapper. -/
def spectralMeasurePVMActualBorelCarrierSetUnion
    (s t : SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMActualBorelCarrierSet :=
  ⟨s.1 ∪ t.1, s.2.union t.2⟩

/-- Intersection operation on the actual Borel carrier wrapper. -/
def spectralMeasurePVMActualBorelCarrierSetInter
    (s t : SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMActualBorelCarrierSet :=
  ⟨s.1 ∩ t.1, s.2.inter t.2⟩

/-- Lift endpoint spectral slots into the actual Borel carrier wrapper. -/
def spectralMeasurePVMActualBorelEndpointCarrierSetFromSlot :
    SpectralMeasurePVMSpectralSetSlot → SpectralMeasurePVMActualBorelCarrierSet
  | SpectralMeasurePVMSpectralSetSlot.emptySet =>
      spectralMeasurePVMActualBorelEmptySet
  | SpectralMeasurePVMSpectralSetSlot.wholeSet =>
      spectralMeasurePVMActualBorelUnivSet

/-- The empty wrapper forgets to the empty subset of `ℝ`. -/
theorem spectral_measure_pvm_actual_borel_empty_set_forget :
    spectralMeasurePVMActualBorelEmptySet.1 = (∅ : Set ℝ) := by
  rfl

/-- The whole wrapper forgets to the universal subset of `ℝ`. -/
theorem spectral_measure_pvm_actual_borel_univ_set_forget :
    spectralMeasurePVMActualBorelUnivSet.1 = (Set.univ : Set ℝ) := by
  rfl

/-- Complement on the wrapper forgets to complement on `Set ℝ`. -/
theorem spectral_measure_pvm_actual_borel_carrier_set_compl_forget
    (s : SpectralMeasurePVMActualBorelCarrierSet) :
    (spectralMeasurePVMActualBorelCarrierSetCompl s).1 = s.1ᶜ := by
  rfl

/-- Union on the wrapper forgets to union on `Set ℝ`. -/
theorem spectral_measure_pvm_actual_borel_carrier_set_union_forget
    (s t : SpectralMeasurePVMActualBorelCarrierSet) :
    (spectralMeasurePVMActualBorelCarrierSetUnion s t).1 = s.1 ∪ t.1 := by
  rfl

/-- Intersection on the wrapper forgets to intersection on `Set ℝ`. -/
theorem spectral_measure_pvm_actual_borel_carrier_set_inter_forget
    (s t : SpectralMeasurePVMActualBorelCarrierSet) :
    (spectralMeasurePVMActualBorelCarrierSetInter s t).1 = s.1 ∩ t.1 := by
  rfl

/-- Endpoint lifting is compatible with the earlier actual endpoint carrier. -/
theorem spectral_measure_pvm_actual_borel_endpoint_carrier_set_from_slot_forget
    (slot : SpectralMeasurePVMSpectralSetSlot) :
    (spectralMeasurePVMActualBorelEndpointCarrierSetFromSlot slot).1 =
      spectralMeasurePVMActualBorelEndpointCarrierFromSlot slot := by
  cases slot <;> rfl

/-- Actual Borel wrapper existence target. -/
def SpectralMeasurePVMActualBorelSetWrapperExistenceTarget : Prop :=
  Nonempty SpectralMeasurePVMActualBorelCarrierSet

/-- The actual Borel wrapper carrier exists. -/
theorem spectral_measure_pvm_actual_borel_set_wrapper_existence_target_ready :
    SpectralMeasurePVMActualBorelSetWrapperExistenceTarget := by
  exact ⟨spectralMeasurePVMActualBorelEmptySet⟩

/-- Endpoint lift target for the actual Borel wrapper. -/
def SpectralMeasurePVMActualBorelSetWrapperEndpointLiftTarget : Prop :=
  (spectralMeasurePVMActualBorelEndpointCarrierSetFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet).1 =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet ∧
  (spectralMeasurePVMActualBorelEndpointCarrierSetFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet).1 =
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet

/-- Endpoint lifting into the actual Borel wrapper is ready. -/
theorem spectral_measure_pvm_actual_borel_set_wrapper_endpoint_lift_target_ready :
    SpectralMeasurePVMActualBorelSetWrapperEndpointLiftTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_carrier_set_from_slot_forget
      SpectralMeasurePVMSpectralSetSlot.emptySet,
    spectral_measure_pvm_actual_borel_endpoint_carrier_set_from_slot_forget
      SpectralMeasurePVMSpectralSetSlot.wholeSet⟩

/-- Boolean closure laws on the actual Borel wrapper, forgetting back to `Set ℝ`. -/
def SpectralMeasurePVMActualBorelSetWrapperBooleanClosureTarget : Prop :=
  (∀ s : SpectralMeasurePVMActualBorelCarrierSet,
      (spectralMeasurePVMActualBorelCarrierSetCompl s).1 = s.1ᶜ) ∧
  (∀ s t : SpectralMeasurePVMActualBorelCarrierSet,
      (spectralMeasurePVMActualBorelCarrierSetUnion s t).1 = s.1 ∪ t.1) ∧
  (∀ s t : SpectralMeasurePVMActualBorelCarrierSet,
      (spectralMeasurePVMActualBorelCarrierSetInter s t).1 = s.1 ∩ t.1)

/-- Boolean closure laws on the actual Borel wrapper are ready. -/
theorem spectral_measure_pvm_actual_borel_set_wrapper_boolean_closure_target_ready :
    SpectralMeasurePVMActualBorelSetWrapperBooleanClosureTarget := by
  exact ⟨
    (by intro s; rfl),
    (by intro s t; rfl),
    (by intro s t; rfl)⟩

/-- Actual Borel set-wrapper bridge.

This is the first arbitrary-Borel-wrapper surface after the endpoint-only
set-algebra bridge: arbitrary Borel sets are represented as measurable subsets
of `ℝ`, and complement/union/intersection are closed by mathlib's
`MeasurableSet` closure operations. It remains a wrapper/interface layer, so
genuine operator-topology countable additivity and spectral-theorem
construction stay open. -/
def SpectralMeasurePVMActualBorelSetWrapperBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelEndpointSetAlgebraPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelSetWrapperExistenceTarget ∧
  SpectralMeasurePVMActualBorelSetWrapperEndpointLiftTarget ∧
  SpectralMeasurePVMActualBorelSetWrapperBooleanClosureTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual Borel set-wrapper bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_set_wrapper_bridge_ready :
    SpectralMeasurePVMActualBorelSetWrapperBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_set_algebra_public_boundary_held,
    spectral_measure_pvm_actual_borel_set_wrapper_existence_target_ready,
    spectral_measure_pvm_actual_borel_set_wrapper_endpoint_lift_target_ready,
    spectral_measure_pvm_actual_borel_set_wrapper_boolean_closure_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual Borel set-wrapper bridge. -/
def SpectralMeasurePVMActualBorelSetWrapperPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelSetWrapperBridgeReady ∧
  SpectralMeasurePVMActualBorelSetWrapperBooleanClosureTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual Borel set-wrapper bridge is held. -/
theorem spectral_measure_pvm_actual_borel_set_wrapper_public_boundary_held :
    SpectralMeasurePVMActualBorelSetWrapperPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_set_wrapper_bridge_ready,
    spectral_measure_pvm_actual_borel_set_wrapper_boolean_closure_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
