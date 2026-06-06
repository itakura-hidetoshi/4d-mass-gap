import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedGenuineBorelIndexedCarrierBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Actual Borel endpoint carrier for the R4 spectral-measure upgrade.

This is the first step after the local finite-supported PVM phase: the carrier is
no longer the two-slot local carrier.  The endpoint slots are realized as actual
subsets of `ℝ`: `∅` and `Set.univ`. -/
def spectralMeasurePVMActualBorelEndpointCarrierFromSlot :
    SpectralMeasurePVMSpectralSetSlot → Set ℝ
  | SpectralMeasurePVMSpectralSetSlot.emptySet => ∅
  | SpectralMeasurePVMSpectralSetSlot.wholeSet => Set.univ

/-- Empty spectral slot realizes the actual empty subset of `ℝ`. -/
theorem spectral_measure_pvm_actual_borel_endpoint_carrier_empty_realizes :
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
        SpectralMeasurePVMSpectralSetSlot.emptySet = (∅ : Set ℝ) := by
  rfl

/-- Whole spectral slot realizes the actual universal subset of `ℝ`. -/
theorem spectral_measure_pvm_actual_borel_endpoint_carrier_whole_realizes :
    spectralMeasurePVMActualBorelEndpointCarrierFromSlot
        SpectralMeasurePVMSpectralSetSlot.wholeSet = (Set.univ : Set ℝ) := by
  rfl

/-- The actual empty endpoint is Borel-measurable. -/
theorem spectral_measure_pvm_actual_borel_endpoint_empty_measurable :
    MeasurableSet (spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet) := by
  simp [spectralMeasurePVMActualBorelEndpointCarrierFromSlot]

/-- The actual whole endpoint is Borel-measurable. -/
theorem spectral_measure_pvm_actual_borel_endpoint_whole_measurable :
    MeasurableSet (spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet) := by
  simp [spectralMeasurePVMActualBorelEndpointCarrierFromSlot]

/-- Endpoint realization target in the actual Borel carrier `Set ℝ`. -/
def SpectralMeasurePVMActualBorelEndpointCarrierRealizationTarget : Prop :=
  spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet = (∅ : Set ℝ) ∧
  spectralMeasurePVMActualBorelEndpointCarrierFromSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet = (Set.univ : Set ℝ)

/-- Endpoint realization in the actual Borel carrier is ready. -/
theorem spectral_measure_pvm_actual_borel_endpoint_carrier_realization_target_ready :
    SpectralMeasurePVMActualBorelEndpointCarrierRealizationTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_carrier_empty_realizes,
    spectral_measure_pvm_actual_borel_endpoint_carrier_whole_realizes⟩

/-- Endpoint measurability target in the actual Borel carrier `Set ℝ`. -/
def SpectralMeasurePVMActualBorelEndpointMeasurabilityTarget : Prop :=
  MeasurableSet (spectralMeasurePVMActualBorelEndpointCarrierFromSlot
    SpectralMeasurePVMSpectralSetSlot.emptySet) ∧
  MeasurableSet (spectralMeasurePVMActualBorelEndpointCarrierFromSlot
    SpectralMeasurePVMSpectralSetSlot.wholeSet)

/-- Endpoint measurability in the actual Borel carrier is ready. -/
theorem spectral_measure_pvm_actual_borel_endpoint_measurability_target_ready :
    SpectralMeasurePVMActualBorelEndpointMeasurabilityTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_empty_measurable,
    spectral_measure_pvm_actual_borel_endpoint_whole_measurable⟩

/-- Actual Borel endpoint carrier bridge.

This bridge advances beyond the local two-slot carrier by realizing the endpoint
slots as actual Borel-measurable subsets of `ℝ`.  It still does not assert the
full genuine spectral measure: arbitrary Borel sets, operator-topology countable
additivity, and the self-adjoint spectral theorem bridge remain open. -/
def SpectralMeasurePVMActualBorelEndpointCarrierBridgeReady : Prop :=
  SpectralMeasurePVMOperatorValuedGenuineBorelIndexedCarrierBridgeReady ∧
  SpectralMeasurePVMActualBorelEndpointCarrierRealizationTarget ∧
  SpectralMeasurePVMActualBorelEndpointMeasurabilityTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMSpectralSetSlotRealizationCompatibilityStillOpen ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual Borel endpoint carrier bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_endpoint_carrier_bridge_ready :
    SpectralMeasurePVMActualBorelEndpointCarrierBridgeReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_genuine_borel_indexed_carrier_bridge_ready,
    spectral_measure_pvm_actual_borel_endpoint_carrier_realization_target_ready,
    spectral_measure_pvm_actual_borel_endpoint_measurability_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_spectral_set_slot_realization_compatibility_still_open_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual Borel endpoint carrier bridge. -/
def SpectralMeasurePVMActualBorelEndpointCarrierPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelEndpointCarrierBridgeReady ∧
  SpectralMeasurePVMActualBorelEndpointMeasurabilityTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual Borel endpoint carrier bridge is held. -/
theorem spectral_measure_pvm_actual_borel_endpoint_carrier_public_boundary_held :
    SpectralMeasurePVMActualBorelEndpointCarrierPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_carrier_bridge_ready,
    spectral_measure_pvm_actual_borel_endpoint_measurability_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
