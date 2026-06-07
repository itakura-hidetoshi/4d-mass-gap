import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelProjectionValuedMapInterface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Pointwise idempotence for a concrete actual-Borel projection operator. -/
def SpectralMeasurePVMActualBorelProjectionOperatorPointwiseIdempotent
    (P : SpectralMeasurePVMActualBorelProjectionOperator) : Prop :=
  ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier, P (P x) = P x

/-- The endpoint-seeded actual-Borel projection map takes only the two concrete
projection values `0` and `id`. -/
theorem spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_zero_or_identity
    (s : SpectralMeasurePVMActualBorelCarrierSet) :
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap s = 0 ∨
      spectralMeasurePVMActualBorelEndpointSeededProjectionMap s =
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier := by
  by_cases hs : s.1 = (∅ : Set ℝ)
  · left
    simp [spectralMeasurePVMActualBorelEndpointSeededProjectionMap, hs]
  · right
    simp [spectralMeasurePVMActualBorelEndpointSeededProjectionMap, hs]

/-- Every value of the endpoint-seeded actual-Borel projection map is pointwise
idempotent.  This is the first genuine operator law beyond the endpoint receipt:
the map is no longer only a shell/interface, each value is a projection operator
in the pointwise idempotence sense. -/
theorem spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_pointwise_idempotent
    (s : SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMActualBorelProjectionOperatorPointwiseIdempotent
      (spectralMeasurePVMActualBorelEndpointSeededProjectionMap s) := by
  intro x
  by_cases hs : s.1 = (∅ : Set ℝ)
  · simp [spectralMeasurePVMActualBorelEndpointSeededProjectionMap, hs]
  · simp [spectralMeasurePVMActualBorelEndpointSeededProjectionMap, hs]

/-- A concrete projection kernel over the actual Borel carrier.

Compared with the earlier interface, this structure adds the pointwise
idempotence law for every value of the map.  It is still not a full spectral
measure: countable additivity and the spectral theorem remain separate residuals. -/
structure SpectralMeasurePVMActualBorelProjectionKernel where
  map : SpectralMeasurePVMActualBorelCarrierSet →
    SpectralMeasurePVMActualBorelProjectionOperator
  empty_maps_to_zero : map spectralMeasurePVMActualBorelEmptySet = 0
  univ_maps_to_identity :
    map spectralMeasurePVMActualBorelUnivSet =
      ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier
  pointwise_idempotent :
    ∀ s : SpectralMeasurePVMActualBorelCarrierSet,
      SpectralMeasurePVMActualBorelProjectionOperatorPointwiseIdempotent (map s)

/-- The endpoint-seeded actual-Borel projection map is a concrete projection
kernel. -/
def spectralMeasurePVMActualBorelEndpointSeededProjectionKernel :
    SpectralMeasurePVMActualBorelProjectionKernel where
  map := spectralMeasurePVMActualBorelEndpointSeededProjectionMap
  empty_maps_to_zero :=
    spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_empty
  univ_maps_to_identity :=
    spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_univ
  pointwise_idempotent :=
    spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_pointwise_idempotent

/-- Existence of an actual-Borel projection kernel. -/
def SpectralMeasurePVMActualBorelProjectionKernelExistenceTarget : Prop :=
  Nonempty SpectralMeasurePVMActualBorelProjectionKernel

/-- The actual-Borel projection kernel exists. -/
theorem spectral_measure_pvm_actual_borel_projection_kernel_existence_target_ready :
    SpectralMeasurePVMActualBorelProjectionKernelExistenceTarget := by
  exact ⟨spectralMeasurePVMActualBorelEndpointSeededProjectionKernel⟩

/-- Endpoint laws plus pointwise idempotence for the concrete kernel. -/
def SpectralMeasurePVMActualBorelProjectionKernelLawTarget : Prop :=
  spectralMeasurePVMActualBorelEndpointSeededProjectionKernel.map
      spectralMeasurePVMActualBorelEmptySet = 0 ∧
  spectralMeasurePVMActualBorelEndpointSeededProjectionKernel.map
      spectralMeasurePVMActualBorelUnivSet =
        ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier ∧
  (∀ s : SpectralMeasurePVMActualBorelCarrierSet,
    SpectralMeasurePVMActualBorelProjectionOperatorPointwiseIdempotent
      (spectralMeasurePVMActualBorelEndpointSeededProjectionKernel.map s))

/-- The concrete kernel laws are ready. -/
theorem spectral_measure_pvm_actual_borel_projection_kernel_law_target_ready :
    SpectralMeasurePVMActualBorelProjectionKernelLawTarget := by
  exact ⟨
    spectralMeasurePVMActualBorelEndpointSeededProjectionKernel.empty_maps_to_zero,
    spectralMeasurePVMActualBorelEndpointSeededProjectionKernel.univ_maps_to_identity,
    spectralMeasurePVMActualBorelEndpointSeededProjectionKernel.pointwise_idempotent⟩

/-- Actual-Borel projection-kernel bridge.

This closes the first residual step from a shell/interface to a genuine concrete
operator kernel: every actual-Borel carrier set is assigned a continuous linear
operator, the endpoints are fixed, and every assigned operator is pointwise
idempotent.  The remaining residuals are explicitly kept open: this is not yet
operator-topology countable additivity and not yet the full spectral-measure
construction. -/
def SpectralMeasurePVMActualBorelProjectionKernelBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelProjectionValuedMapInterfacePublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelProjectionKernelExistenceTarget ∧
  SpectralMeasurePVMActualBorelProjectionKernelLawTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel projection-kernel bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_projection_kernel_bridge_ready :
    SpectralMeasurePVMActualBorelProjectionKernelBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_projection_valued_map_interface_public_boundary_held,
    spectral_measure_pvm_actual_borel_projection_kernel_existence_target_ready,
    spectral_measure_pvm_actual_borel_projection_kernel_law_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual-Borel projection kernel bridge. -/
def SpectralMeasurePVMActualBorelProjectionKernelPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelProjectionKernelBridgeReady ∧
  SpectralMeasurePVMActualBorelProjectionKernelLawTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual-Borel projection kernel bridge is held. -/
theorem spectral_measure_pvm_actual_borel_projection_kernel_public_boundary_held :
    SpectralMeasurePVMActualBorelProjectionKernelPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_projection_kernel_bridge_ready,
    spectral_measure_pvm_actual_borel_projection_kernel_law_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
