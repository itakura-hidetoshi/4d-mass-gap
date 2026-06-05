import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableSetCountableBranch

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Local operator-valued-measure interface on the supported measurable-set
surface.  This packages the local measurable class, operator assignment, finite
PVM laws, and the two countable branches. -/
structure SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterface where
  SupportedSet : Type
  toSet : SupportedSet → SpectralMeasurePVMFiniteSetCarrier
  operatorValue : SupportedSet → SpectralMeasurePVMConcreteBoundedOperator
  measurableTarget : Prop
  endpointTarget : Prop
  projectionTarget : Prop
  orthogonalityTarget : Prop
  finiteAdditivityTarget : Prop
  countableBranchTarget : Prop

/-- Concrete supported measurable local OVM interface for the finite R4 surface. -/
def spectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterface :
    SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterface where
  SupportedSet := SpectralMeasurePVMFiniteSupportedMeasurableSet
  toSet := spectralMeasurePVMFiniteSupportedMeasurableSetToSet
  operatorValue := spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
  measurableTarget :=
    ∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
      @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
        spectralMeasurePVMFiniteSetCarrierMeasurableSpace
        (spectralMeasurePVMFiniteSupportedMeasurableSetToSet E)
  endpointTarget := SpectralMeasurePVMFiniteSupportedMeasurableSetEndpointOperatorTarget
  projectionTarget := SpectralMeasurePVMFiniteSupportedMeasurableSetProjectionTarget
  orthogonalityTarget := SpectralMeasurePVMFiniteSupportedMeasurableSetOrthogonalityTarget
  finiteAdditivityTarget := SpectralMeasurePVMFiniteSupportedMeasurableSetFiniteAdditivityTarget
  countableBranchTarget := SpectralMeasurePVMFiniteSupportedMeasurableSetCountableBranchTarget

/-- Existence target for the supported measurable local OVM interface. -/
def SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterfaceExistenceTarget : Prop :=
  Nonempty SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterface

/-- The supported measurable local OVM interface exists. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_ovm_interface_existence_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterfaceExistenceTarget := by
  exact ⟨spectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterface⟩

/-- All law targets in the supported measurable local OVM interface are ready. -/
def SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMLawTarget : Prop :=
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMFiniteSupportedMeasurableSetToSet E)) ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetEndpointOperatorTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetProjectionTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetOrthogonalityTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetFiniteAdditivityTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetCountableBranchTarget

/-- The supported measurable local OVM law target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_ovm_law_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMLawTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_set_measurable,
    spectral_measure_pvm_finite_supported_measurable_set_endpoint_operator_target_ready,
    spectral_measure_pvm_finite_supported_measurable_set_projection_target_ready,
    spectral_measure_pvm_finite_supported_measurable_set_orthogonality_target_ready,
    spectral_measure_pvm_finite_supported_measurable_set_finite_additivity_target_ready,
    spectral_measure_pvm_finite_supported_measurable_set_countable_branch_target_ready⟩

/-- Bridge for the supported measurable local OVM interface. -/
def SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterfaceBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableSetBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetCountableBranchBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterfaceExistenceTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMLawTarget ∧
  SpectralMeasurePVMFiniteMeasurableLocalPVMBundleReady ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported measurable local OVM interface bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_ovm_interface_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterfaceBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_set_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_set_countable_branch_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_local_ovm_interface_existence_target_ready,
    spectral_measure_pvm_finite_supported_measurable_local_ovm_law_target_ready,
    spectral_measure_pvm_finite_measurable_local_pvm_bundle_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
