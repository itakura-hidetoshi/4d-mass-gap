import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSetCarrierSigmaBooleanClosureBundle

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Operator assignment on the image of the finite `Set` carrier.

The assignment is indexed by the original local spectral slot, while the slot is
simultaneously realized as a finite `Set` by
`spectralMeasurePVMSpectralSlotToFiniteSetCarrier`.  This avoids pretending that
we have already defined a genuine operator-valued measure on all Borel sets. -/
def spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
    (s : SpectralMeasurePVMSpectralSetSlot) : SpectralMeasurePVMConcreteBoundedOperator :=
  spectralMeasurePVMConcreteNormalizationCandidate
    (spectralMeasurePVMConcreteIndexFromSpectralSetSlot s)

/-- The empty finite-set carrier image is assigned the zero concrete operator. -/
theorem spectral_measure_pvm_finite_set_carrier_empty_image_operator_zero :
    spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
        SpectralMeasurePVMSpectralSetSlot.emptySet =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  rfl

/-- The whole finite-set carrier image is assigned the identity concrete operator. -/
theorem spectral_measure_pvm_finite_set_carrier_whole_image_operator_identity :
    spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
        SpectralMeasurePVMSpectralSetSlot.wholeSet =
      SpectralMeasurePVMConcreteBoundedOperator.identity := by
  rfl

/-- Endpoint operator assignment target on the finite `Set` carrier image. -/
def SpectralMeasurePVMFiniteSetCarrierEndpointOperatorAssignmentTarget : Prop :=
  spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
      SpectralMeasurePVMSpectralSetSlot.emptySet =
    SpectralMeasurePVMConcreteBoundedOperator.zero ∧
  spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
      SpectralMeasurePVMSpectralSetSlot.wholeSet =
    SpectralMeasurePVMConcreteBoundedOperator.identity

/-- Endpoint operator assignment is ready on the finite `Set` carrier image. -/
theorem spectral_measure_pvm_finite_set_carrier_endpoint_operator_assignment_target_ready :
    SpectralMeasurePVMFiniteSetCarrierEndpointOperatorAssignmentTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_empty_image_operator_zero,
    spectral_measure_pvm_finite_set_carrier_whole_image_operator_identity⟩

/-- The finite `Set` carrier image operator assignment is compatible with the
endpoint `Set` realization. -/
def SpectralMeasurePVMFiniteSetCarrierEndpointOperatorSetCompatibilityTarget : Prop :=
  spectralMeasurePVMSpectralSlotToFiniteSetCarrier SpectralMeasurePVMSpectralSetSlot.emptySet =
    spectralMeasurePVMFiniteSetCarrierEmpty ∧
  spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
      SpectralMeasurePVMSpectralSetSlot.emptySet =
    SpectralMeasurePVMConcreteBoundedOperator.zero ∧
  spectralMeasurePVMSpectralSlotToFiniteSetCarrier SpectralMeasurePVMSpectralSetSlot.wholeSet =
    spectralMeasurePVMFiniteSetCarrierWhole ∧
  spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
      SpectralMeasurePVMSpectralSetSlot.wholeSet =
    SpectralMeasurePVMConcreteBoundedOperator.identity

/-- Endpoint `Set`/operator compatibility is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_endpoint_operator_set_compatibility_target_ready :
    SpectralMeasurePVMFiniteSetCarrierEndpointOperatorSetCompatibilityTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_empty_slot_realizes,
    spectral_measure_pvm_finite_set_carrier_empty_image_operator_zero,
    spectral_measure_pvm_finite_set_carrier_whole_slot_realizes,
    spectral_measure_pvm_finite_set_carrier_whole_image_operator_identity⟩

/-- Bridge from the finite `Set` sigma-Boolean host to an endpoint operator-valued
assignment on its slot image.

This is still not a genuine operator-valued measure on all Borel sets. -/
def SpectralMeasurePVMFiniteSetCarrierEndpointOperatorBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSetCarrierSigmaBooleanClosureBundleReady ∧
  SpectralMeasurePVMFiniteSetCarrierEndpointOperatorAssignmentTarget ∧
  SpectralMeasurePVMFiniteSetCarrierEndpointOperatorSetCompatibilityTarget ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite `Set` carrier endpoint operator bridge is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_endpoint_operator_bridge_ready :
    SpectralMeasurePVMFiniteSetCarrierEndpointOperatorBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_sigma_boolean_closure_bundle_ready,
    spectral_measure_pvm_finite_set_carrier_endpoint_operator_assignment_target_ready,
    spectral_measure_pvm_finite_set_carrier_endpoint_operator_set_compatibility_target_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
