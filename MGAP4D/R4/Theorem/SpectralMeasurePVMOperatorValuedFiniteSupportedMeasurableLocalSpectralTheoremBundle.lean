import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableLocalSpectralIntegralInterface
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedGenuineSelfAdjointSpectralTheoremBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Supported measurable local spectral theorem bundle.

This packages the supported measurable local OVM interface, its symbolic
spectral-integral interface, and the global self-adjoint spectral-theorem
transition bridge.  It remains a local supported `{∅, univ}` bundle, not a
genuine Borel spectral theorem. -/
def SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralTheoremBundleReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterfaceBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralInterfaceBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetCountableBranchBridgeReady ∧
  SpectralMeasurePVMOperatorValuedGenuineSelfAdjointSpectralTheoremBridgeReady ∧
  SpectralMeasurePVMActualSpectralIntegralRealizationStillOpen ∧
  SpectralMeasurePVMSpectralIntegralSlotRealizationCompatibilityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported measurable local spectral theorem bundle is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_spectral_theorem_bundle_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralTheoremBundleReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_local_ovm_interface_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_interface_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_set_countable_branch_bridge_ready,
    spectral_measure_pvm_operator_valued_genuine_self_adjoint_spectral_theorem_bridge_ready,
    spectral_measure_pvm_actual_spectral_integral_realization_still_open_ready,
    spectral_measure_pvm_spectral_integral_slot_realization_compatibility_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public frontier after the supported measurable local spectral theorem bundle.

The supported measurable `{∅, univ}` local PVM/OVM/spectral-integral surface is
organized.  The genuine Borel carrier, genuine operator-topology countable
additivity, and genuine self-adjoint spectral theorem realization remain open. -/
def SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralTheoremFrontier : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralTheoremBundleReady ∧
  SpectralMeasurePVMFiniteMeasurableLocalPVMFrontier ∧
  SpectralMeasurePVMOperatorValuedGenuinePVMTransitionCompletionFrontier ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public frontier after the supported measurable local spectral theorem bundle is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_spectral_theorem_frontier_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralTheoremFrontier := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_local_spectral_theorem_bundle_ready,
    spectral_measure_pvm_finite_measurable_local_pvm_frontier_ready,
    spectral_measure_pvm_operator_valued_genuine_pvm_transition_completion_frontier_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
