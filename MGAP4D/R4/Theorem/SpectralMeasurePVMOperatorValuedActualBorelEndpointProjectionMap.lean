import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelProjectionValuedMapInterface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Endpoint projection map induced by the actual-Borel projection-valued map
interface and the endpoint carrier lift. -/
def spectralMeasurePVMActualBorelEndpointProjectionMap
    (slot : SpectralMeasurePVMSpectralSetSlot) :
    SpectralMeasurePVMActualBorelProjectionOperator :=
  spectralMeasurePVMActualBorelEndpointSeededProjectionValuedMapInterface.map
    (spectralMeasurePVMActualBorelEndpointCarrierSetFromSlot slot)

/-- The empty endpoint maps to the zero operator. -/
theorem spectral_measure_pvm_actual_borel_endpoint_projection_map_empty :
    spectralMeasurePVMActualBorelEndpointProjectionMap
      SpectralMeasurePVMSpectralSetSlot.emptySet = 0 := by
  exact spectralMeasurePVMActualBorelEndpointSeededProjectionValuedMapInterface.empty_maps_to_zero

/-- The whole endpoint maps to the identity operator. -/
theorem spectral_measure_pvm_actual_borel_endpoint_projection_map_whole :
    spectralMeasurePVMActualBorelEndpointProjectionMap
      SpectralMeasurePVMSpectralSetSlot.wholeSet =
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier := by
  exact spectralMeasurePVMActualBorelEndpointSeededProjectionValuedMapInterface.univ_maps_to_identity

/-- Pointwise empty endpoint law. -/
theorem spectral_measure_pvm_actual_borel_endpoint_projection_map_empty_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelEndpointProjectionMap
      SpectralMeasurePVMSpectralSetSlot.emptySet x = 0 := by
  rw [spectral_measure_pvm_actual_borel_endpoint_projection_map_empty]
  rfl

/-- Pointwise whole endpoint law. -/
theorem spectral_measure_pvm_actual_borel_endpoint_projection_map_whole_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelEndpointProjectionMap
      SpectralMeasurePVMSpectralSetSlot.wholeSet x = x := by
  rw [spectral_measure_pvm_actual_borel_endpoint_projection_map_whole]
  rfl

/-- Endpoint projection-map law target. -/
def SpectralMeasurePVMActualBorelEndpointProjectionMapLawTarget : Prop :=
  spectralMeasurePVMActualBorelEndpointProjectionMap
      SpectralMeasurePVMSpectralSetSlot.emptySet = 0 ∧
  spectralMeasurePVMActualBorelEndpointProjectionMap
      SpectralMeasurePVMSpectralSetSlot.wholeSet =
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier

/-- Endpoint projection-map laws are ready. -/
theorem spectral_measure_pvm_actual_borel_endpoint_projection_map_law_target_ready :
    SpectralMeasurePVMActualBorelEndpointProjectionMapLawTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_projection_map_empty,
    spectral_measure_pvm_actual_borel_endpoint_projection_map_whole⟩

/-- Pointwise endpoint projection-map law target. -/
def SpectralMeasurePVMActualBorelEndpointProjectionMapPointwiseTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelEndpointProjectionMap
      SpectralMeasurePVMSpectralSetSlot.emptySet x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelEndpointProjectionMap
      SpectralMeasurePVMSpectralSetSlot.wholeSet x = x)

/-- Pointwise endpoint projection-map laws are ready. -/
theorem spectral_measure_pvm_actual_borel_endpoint_projection_map_pointwise_target_ready :
    SpectralMeasurePVMActualBorelEndpointProjectionMapPointwiseTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_projection_map_empty_apply,
    spectral_measure_pvm_actual_borel_endpoint_projection_map_whole_apply⟩

/-- Actual-Borel endpoint projection-map bridge. -/
def SpectralMeasurePVMActualBorelEndpointProjectionMapBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelProjectionValuedMapInterfacePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelEndpointProjectionMapLawTarget ∧
  SpectralMeasurePVMActualBorelEndpointProjectionMapPointwiseTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel endpoint projection-map bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_endpoint_projection_map_bridge_ready :
    SpectralMeasurePVMActualBorelEndpointProjectionMapBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_projection_valued_map_interface_public_boundary_held,
    spectral_measure_pvm_actual_borel_endpoint_projection_map_law_target_ready,
    spectral_measure_pvm_actual_borel_endpoint_projection_map_pointwise_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual-Borel endpoint projection-map bridge. -/
def SpectralMeasurePVMActualBorelEndpointProjectionMapPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelEndpointProjectionMapBridgeReady ∧
  SpectralMeasurePVMActualBorelEndpointProjectionMapLawTarget ∧
  SpectralMeasurePVMActualBorelEndpointProjectionMapPointwiseTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual-Borel endpoint projection-map bridge is held. -/
theorem spectral_measure_pvm_actual_borel_endpoint_projection_map_public_boundary_held :
    SpectralMeasurePVMActualBorelEndpointProjectionMapPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_projection_map_bridge_ready,
    spectral_measure_pvm_actual_borel_endpoint_projection_map_law_target_ready,
    spectral_measure_pvm_actual_borel_endpoint_projection_map_pointwise_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
