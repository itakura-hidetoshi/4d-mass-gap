import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelSetAlgebraClosure
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

abbrev SpectralMeasurePVMActualBorelProjectionOperator :=
  MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
    MathlibAnalytic.ConcreteL2R1HilbertCarrier

structure SpectralMeasurePVMActualBorelProjectionValuedMapInterface where
  map : SpectralMeasurePVMActualBorelCarrierSet →
    SpectralMeasurePVMActualBorelProjectionOperator
  empty_maps_to_zero : map spectralMeasurePVMActualBorelEmptySet = 0
  univ_maps_to_identity :
    map spectralMeasurePVMActualBorelUnivSet =
      ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier

def spectralMeasurePVMActualBorelEndpointSeededProjectionMap
    (s : SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMActualBorelProjectionOperator :=
  if s.1 = (∅ : Set ℝ) then 0
  else ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier

theorem spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_empty :
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
      spectralMeasurePVMActualBorelEmptySet = 0 := by
  simp [spectralMeasurePVMActualBorelEndpointSeededProjectionMap,
    spectralMeasurePVMActualBorelEmptySet]

theorem spectral_measure_pvm_actual_borel_univ_ne_empty_set :
    (Set.univ : Set ℝ) ≠ (∅ : Set ℝ) := by
  intro h
  have hx : (0 : ℝ) ∈ (Set.univ : Set ℝ) := by simp
  have hx_empty : (0 : ℝ) ∈ (∅ : Set ℝ) := by simpa [h] using hx
  simpa using hx_empty

theorem spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_univ :
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
      spectralMeasurePVMActualBorelUnivSet =
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier := by
  simp [spectralMeasurePVMActualBorelEndpointSeededProjectionMap,
    spectralMeasurePVMActualBorelUnivSet,
    spectral_measure_pvm_actual_borel_univ_ne_empty_set]

def spectralMeasurePVMActualBorelEndpointSeededProjectionValuedMapInterface :
    SpectralMeasurePVMActualBorelProjectionValuedMapInterface where
  map := spectralMeasurePVMActualBorelEndpointSeededProjectionMap
  empty_maps_to_zero :=
    spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_empty
  univ_maps_to_identity :=
    spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_univ

def SpectralMeasurePVMActualBorelProjectionValuedMapInterfaceExistenceTarget : Prop :=
  Nonempty SpectralMeasurePVMActualBorelProjectionValuedMapInterface

theorem spectral_measure_pvm_actual_borel_projection_valued_map_interface_existence_target_ready :
    SpectralMeasurePVMActualBorelProjectionValuedMapInterfaceExistenceTarget := by
  exact ⟨spectralMeasurePVMActualBorelEndpointSeededProjectionValuedMapInterface⟩

def SpectralMeasurePVMActualBorelProjectionValuedMapEndpointLawTarget : Prop :=
  spectralMeasurePVMActualBorelEndpointSeededProjectionValuedMapInterface.map
      spectralMeasurePVMActualBorelEmptySet = 0 ∧
  spectralMeasurePVMActualBorelEndpointSeededProjectionValuedMapInterface.map
      spectralMeasurePVMActualBorelUnivSet =
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier

theorem spectral_measure_pvm_actual_borel_projection_valued_map_endpoint_law_target_ready :
    SpectralMeasurePVMActualBorelProjectionValuedMapEndpointLawTarget := by
  exact ⟨
    spectralMeasurePVMActualBorelEndpointSeededProjectionValuedMapInterface.empty_maps_to_zero,
    spectralMeasurePVMActualBorelEndpointSeededProjectionValuedMapInterface.univ_maps_to_identity⟩

def SpectralMeasurePVMActualBorelProjectionValuedMapInterfaceBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelSetAlgebraClosurePublicBoundaryHeld ∧
  SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyBoundaryHeld ∧
  SpectralMeasurePVMActualBorelProjectionValuedMapInterfaceExistenceTarget ∧
  SpectralMeasurePVMActualBorelProjectionValuedMapEndpointLawTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

theorem spectral_measure_pvm_actual_borel_projection_valued_map_interface_bridge_ready :
    SpectralMeasurePVMActualBorelProjectionValuedMapInterfaceBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_set_algebra_closure_public_boundary_held,
    spectral_measure_pvm_operator_valued_continuous_projection_family_boundary_held,
    spectral_measure_pvm_actual_borel_projection_valued_map_interface_existence_target_ready,
    spectral_measure_pvm_actual_borel_projection_valued_map_endpoint_law_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

def SpectralMeasurePVMActualBorelProjectionValuedMapInterfacePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelProjectionValuedMapInterfaceBridgeReady ∧
  SpectralMeasurePVMActualBorelProjectionValuedMapEndpointLawTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

theorem spectral_measure_pvm_actual_borel_projection_valued_map_interface_public_boundary_held :
    SpectralMeasurePVMActualBorelProjectionValuedMapInterfacePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_projection_valued_map_interface_bridge_ready,
    spectral_measure_pvm_actual_borel_projection_valued_map_endpoint_law_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
