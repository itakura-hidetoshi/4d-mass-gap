import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableLocalOVMInterface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Symbolic spectral-integral slot associated to a supported measurable set. -/
def spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMSpectralIntegralSlot :=
  spectralMeasurePVMSpectralIntegralSlotFromOperator
    (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)

/-- Empty supported measurable set has the zero symbolic spectral-integral slot. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_empty_slot :
    spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
        SpectralMeasurePVMFiniteSupportedMeasurableSet.empty =
      SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral := by
  rfl

/-- Whole supported measurable set has the identity symbolic spectral-integral slot. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_whole_slot :
    spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
        SpectralMeasurePVMFiniteSupportedMeasurableSet.whole =
      SpectralMeasurePVMSpectralIntegralSlot.identityIntegral := by
  rfl

/-- Indicator compatibility for supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_indicator_compat
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMSpectralIntegralSlotFromFunction
        (spectralMeasurePVMConcreteIndicatorFunction
          (spectralMeasurePVMConcreteIndexFromSpectralSetSlot
            (spectralMeasurePVMFiniteSupportedMeasurableSetToSlot E))) =
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E := by
  cases E <;> rfl

/-- Endpoint target for supported measurable local spectral-integral slots. -/
def SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralEndpointTarget : Prop :=
  spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty =
    SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral ∧
  spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
      SpectralMeasurePVMFiniteSupportedMeasurableSet.whole =
    SpectralMeasurePVMSpectralIntegralSlot.identityIntegral

/-- Indicator target for supported measurable local spectral-integral slots. -/
def SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralIndicatorTarget : Prop :=
  ∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMSpectralIntegralSlotFromFunction
        (spectralMeasurePVMConcreteIndicatorFunction
          (spectralMeasurePVMConcreteIndexFromSpectralSetSlot
            (spectralMeasurePVMFiniteSupportedMeasurableSetToSlot E))) =
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E

/-- Endpoint target is ready for supported measurable local spectral-integral slots. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_endpoint_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralEndpointTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_empty_slot,
    spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_whole_slot⟩

/-- Indicator target is ready for supported measurable local spectral-integral slots. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_indicator_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralIndicatorTarget := by
  exact spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_indicator_compat

/-- Local symbolic spectral-integral interface on supported measurable sets. -/
structure SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralInterface where
  SupportedSet : Type
  integralSlot : SupportedSet → SpectralMeasurePVMSpectralIntegralSlot
  endpointTarget : Prop
  indicatorTarget : Prop
  ovmInterfaceReady : Prop

/-- Concrete supported measurable local spectral-integral interface. -/
def spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralInterface :
    SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralInterface where
  SupportedSet := SpectralMeasurePVMFiniteSupportedMeasurableSet
  integralSlot := spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
  endpointTarget := SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralEndpointTarget
  indicatorTarget := SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralIndicatorTarget
  ovmInterfaceReady := SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterfaceBridgeReady

/-- Existence target for the supported measurable local spectral-integral interface. -/
def SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralInterfaceExistenceTarget : Prop :=
  Nonempty SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralInterface

/-- The supported measurable local spectral-integral interface exists. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_interface_existence_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralInterfaceExistenceTarget := by
  exact ⟨spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralInterface⟩

/-- Bridge from supported measurable local OVM to supported measurable local spectral-integral interface. -/
def SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralInterfaceBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMInterfaceBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralEndpointTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralIndicatorTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralInterfaceExistenceTarget ∧
  SpectralMeasurePVMActualSpectralIntegralRealizationStillOpen ∧
  SpectralMeasurePVMSpectralIntegralSlotRealizationCompatibilityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported measurable local spectral-integral interface bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_interface_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralInterfaceBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_local_ovm_interface_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_endpoint_target_ready,
    spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_indicator_target_ready,
    spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_interface_existence_target_ready,
    spectral_measure_pvm_actual_spectral_integral_realization_still_open_ready,
    spectral_measure_pvm_spectral_integral_slot_realization_compatibility_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
