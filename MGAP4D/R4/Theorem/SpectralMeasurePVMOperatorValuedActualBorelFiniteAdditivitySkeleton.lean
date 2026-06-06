import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelEndpointProjectionMap

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Actual-Borel endpoint union projected through the endpoint-seeded map. -/
def spectralMeasurePVMActualBorelEndpointUnionProjectionMap
    (s t : SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMActualBorelProjectionOperator :=
  spectralMeasurePVMActualBorelEndpointSeededProjectionMap
    (spectralMeasurePVMActualBorelCarrierSetUnion s t)

/-- Pointwise finite additivity for `∅ ∪ ∅`. -/
theorem spectral_measure_pvm_actual_borel_finite_additivity_empty_empty_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelEndpointUnionProjectionMap
        spectralMeasurePVMActualBorelEmptySet
        spectralMeasurePVMActualBorelEmptySet x =
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelEmptySet x +
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelEmptySet x := by
  simp [spectralMeasurePVMActualBorelEndpointUnionProjectionMap,
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap,
    spectralMeasurePVMActualBorelCarrierSetUnion,
    spectralMeasurePVMActualBorelEmptySet]

/-- Pointwise finite additivity for `∅ ∪ univ`. -/
theorem spectral_measure_pvm_actual_borel_finite_additivity_empty_univ_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelEndpointUnionProjectionMap
        spectralMeasurePVMActualBorelEmptySet
        spectralMeasurePVMActualBorelUnivSet x =
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelEmptySet x +
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelUnivSet x := by
  simp [spectralMeasurePVMActualBorelEndpointUnionProjectionMap,
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap,
    spectralMeasurePVMActualBorelCarrierSetUnion,
    spectralMeasurePVMActualBorelEmptySet,
    spectralMeasurePVMActualBorelUnivSet]

/-- Pointwise finite additivity for `univ ∪ ∅`. -/
theorem spectral_measure_pvm_actual_borel_finite_additivity_univ_empty_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelEndpointUnionProjectionMap
        spectralMeasurePVMActualBorelUnivSet
        spectralMeasurePVMActualBorelEmptySet x =
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelUnivSet x +
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelEmptySet x := by
  simp [spectralMeasurePVMActualBorelEndpointUnionProjectionMap,
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap,
    spectralMeasurePVMActualBorelCarrierSetUnion,
    spectralMeasurePVMActualBorelEmptySet,
    spectralMeasurePVMActualBorelUnivSet]

/-- Endpoint finite-additivity skeleton target for the actual-Borel projection map.

Only the disjoint endpoint cases are included: `∅∪∅`, `∅∪univ`, and
`univ∪∅`.  This is intentionally weaker than genuine countable additivity. -/
def SpectralMeasurePVMActualBorelFiniteAdditivitySkeletonTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelEndpointUnionProjectionMap
        spectralMeasurePVMActualBorelEmptySet
        spectralMeasurePVMActualBorelEmptySet x =
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelEmptySet x +
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelEmptySet x) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelEndpointUnionProjectionMap
        spectralMeasurePVMActualBorelEmptySet
        spectralMeasurePVMActualBorelUnivSet x =
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelEmptySet x +
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelUnivSet x) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelEndpointUnionProjectionMap
        spectralMeasurePVMActualBorelUnivSet
        spectralMeasurePVMActualBorelEmptySet x =
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelUnivSet x +
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        spectralMeasurePVMActualBorelEmptySet x)

/-- The endpoint finite-additivity skeleton target is ready. -/
theorem spectral_measure_pvm_actual_borel_finite_additivity_skeleton_target_ready :
    SpectralMeasurePVMActualBorelFiniteAdditivitySkeletonTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_finite_additivity_empty_empty_apply,
    spectral_measure_pvm_actual_borel_finite_additivity_empty_univ_apply,
    spectral_measure_pvm_actual_borel_finite_additivity_univ_empty_apply⟩

/-- Actual-Borel finite-additivity skeleton bridge. -/
def SpectralMeasurePVMActualBorelFiniteAdditivitySkeletonBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelEndpointProjectionMapPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelFiniteAdditivitySkeletonTarget ∧
  SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel finite-additivity skeleton bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_finite_additivity_skeleton_bridge_ready :
    SpectralMeasurePVMActualBorelFiniteAdditivitySkeletonBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_endpoint_projection_map_public_boundary_held,
    spectral_measure_pvm_actual_borel_finite_additivity_skeleton_target_ready,
    spectral_measure_pvm_actual_borel_set_algebra_realization_still_open_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual-Borel finite-additivity skeleton bridge. -/
def SpectralMeasurePVMActualBorelFiniteAdditivitySkeletonPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelFiniteAdditivitySkeletonBridgeReady ∧
  SpectralMeasurePVMActualBorelFiniteAdditivitySkeletonTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual-Borel finite-additivity skeleton is held. -/
theorem spectral_measure_pvm_actual_borel_finite_additivity_skeleton_public_boundary_held :
    SpectralMeasurePVMActualBorelFiniteAdditivitySkeletonPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_finite_additivity_skeleton_bridge_ready,
    spectral_measure_pvm_actual_borel_finite_additivity_skeleton_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
