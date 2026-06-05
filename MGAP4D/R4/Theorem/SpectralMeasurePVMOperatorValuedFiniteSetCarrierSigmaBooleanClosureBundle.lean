import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSetCarrierCountableUnionBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- A concrete finite `Set`-carrier sigma-Boolean interface.

This uses the explicit `Set`-level countable union introduced for the finite
carrier.  It is still not a genuine Borel sigma algebra. -/
def spectralMeasurePVMFiniteSetCarrierSigmaBooleanClosureInterface :
    SpectralMeasurePVMSigmaBooleanClosureInterface where
  Carrier := SpectralMeasurePVMFiniteSetCarrier
  emptyCarrier := spectralMeasurePVMFiniteSetCarrierEmpty
  wholeCarrier := spectralMeasurePVMFiniteSetCarrierWhole
  countableFamily := Nat → SpectralMeasurePVMFiniteSetCarrier
  countableUnion := spectralMeasurePVMFiniteSetCarrierCountableUnion

/-- Existence target for the finite `Set`-carrier sigma-Boolean interface. -/
def SpectralMeasurePVMFiniteSetCarrierSigmaBooleanInterfaceExistenceTarget : Prop :=
  Nonempty SpectralMeasurePVMSigmaBooleanClosureInterface

/-- The finite `Set`-carrier sigma-Boolean interface exists. -/
theorem spectral_measure_pvm_finite_set_carrier_sigma_boolean_interface_existence_target_ready :
    SpectralMeasurePVMFiniteSetCarrierSigmaBooleanInterfaceExistenceTarget := by
  exact ⟨spectralMeasurePVMFiniteSetCarrierSigmaBooleanClosureInterface⟩

/-- The finite `Set` carrier now has endpoint, Boolean, and explicit countable
union support bundled as a local sigma-Boolean host. -/
def SpectralMeasurePVMFiniteSetCarrierSigmaBooleanLocalHostTarget : Prop :=
  SpectralMeasurePVMFiniteSetCarrierEndpointRealizationTarget ∧
  SpectralMeasurePVMFiniteSetCarrierBooleanOperationRealizationTarget ∧
  SpectralMeasurePVMFiniteSetCarrierCountableUnionTarget ∧
  SpectralMeasurePVMFiniteSetCarrierSigmaBooleanInterfaceExistenceTarget

/-- The finite `Set` carrier local sigma-Boolean host target is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_sigma_boolean_local_host_target_ready :
    SpectralMeasurePVMFiniteSetCarrierSigmaBooleanLocalHostTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_endpoint_realization_target_ready,
    spectral_measure_pvm_finite_set_carrier_boolean_operation_realization_target_ready,
    spectral_measure_pvm_finite_set_carrier_countable_union_target_ready,
    spectral_measure_pvm_finite_set_carrier_sigma_boolean_interface_existence_target_ready⟩

/-- Finite `Set`-carrier sigma-Boolean closure bundle.

This is the strongest local concrete carrier bundle so far: it realizes the
local spectral slots as actual `Set`s, realizes finite Boolean operations as
`Set` operations, and hosts the two explicit countable-union branches.  It still
leaves the genuine Borel/sigma closure theorem open. -/
def SpectralMeasurePVMFiniteSetCarrierSigmaBooleanClosureBundleReady : Prop :=
  SpectralMeasurePVMFiniteSetCarrierRealizationBridgeReady ∧
  SpectralMeasurePVMFiniteSetCarrierBooleanRealizationBridgeReady ∧
  SpectralMeasurePVMFiniteSetCarrierCountableUnionBridgeReady ∧
  SpectralMeasurePVMFiniteSetCarrierSigmaBooleanLocalHostTarget ∧
  SpectralMeasurePVMOperatorValuedGenuineSigmaBooleanClosureBridgeReady ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSigmaBooleanClosureStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite `Set`-carrier sigma-Boolean closure bundle is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_sigma_boolean_closure_bundle_ready :
    SpectralMeasurePVMFiniteSetCarrierSigmaBooleanClosureBundleReady := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_realization_bridge_ready,
    spectral_measure_pvm_finite_set_carrier_boolean_realization_bridge_ready,
    spectral_measure_pvm_finite_set_carrier_countable_union_bridge_ready,
    spectral_measure_pvm_finite_set_carrier_sigma_boolean_local_host_target_ready,
    spectral_measure_pvm_operator_valued_genuine_sigma_boolean_closure_bridge_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_sigma_boolean_closure_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
