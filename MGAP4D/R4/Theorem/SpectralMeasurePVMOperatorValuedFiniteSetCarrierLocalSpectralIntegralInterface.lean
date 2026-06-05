import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSetCarrierLocalMeasureInterface
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedSpectralIntegralUpgradeBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Local spectral-integral slot induced by the finite `Set` carrier image operator
candidate. -/
def spectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralSlot
    (s : SpectralMeasurePVMSpectralSetSlot) : SpectralMeasurePVMSpectralIntegralSlot :=
  spectralMeasurePVMSpectralIntegralSlotFromOperator
    (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate s)

/-- The empty local set-carrier image has zero spectral-integral slot. -/
theorem spectral_measure_pvm_finite_set_carrier_local_spectral_integral_empty_slot :
    spectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralSlot
        SpectralMeasurePVMSpectralSetSlot.emptySet =
      SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral := by
  rfl

/-- The whole local set-carrier image has identity spectral-integral slot. -/
theorem spectral_measure_pvm_finite_set_carrier_local_spectral_integral_whole_slot :
    spectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralSlot
        SpectralMeasurePVMSpectralSetSlot.wholeSet =
      SpectralMeasurePVMSpectralIntegralSlot.identityIntegral := by
  rfl

/-- Indicator functions on local slots recover the same symbolic spectral-integral
slot as the local finite `Set` carrier image operator candidate. -/
theorem spectral_measure_pvm_finite_set_carrier_local_spectral_integral_indicator_compat
    (s : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralIntegralSlotFromFunction
        (spectralMeasurePVMConcreteIndicatorFunction
          (spectralMeasurePVMConcreteIndexFromSpectralSetSlot s)) =
      spectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralSlot s := by
  cases s <;> rfl

/-- Endpoint spectral-integral slot target for the local finite `Set` carrier. -/
def SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralEndpointTarget : Prop :=
  spectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralSlot
      SpectralMeasurePVMSpectralSetSlot.emptySet =
    SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral ∧
  spectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralSlot
      SpectralMeasurePVMSpectralSetSlot.wholeSet =
    SpectralMeasurePVMSpectralIntegralSlot.identityIntegral

/-- Indicator compatibility target for the local finite `Set` carrier spectral-integral slots. -/
def SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralIndicatorTarget : Prop :=
  ∀ s : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralIntegralSlotFromFunction
        (spectralMeasurePVMConcreteIndicatorFunction
          (spectralMeasurePVMConcreteIndexFromSpectralSetSlot s)) =
      spectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralSlot s

/-- Endpoint spectral-integral slot target is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_local_spectral_integral_endpoint_target_ready :
    SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralEndpointTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_local_spectral_integral_empty_slot,
    spectral_measure_pvm_finite_set_carrier_local_spectral_integral_whole_slot⟩

/-- Indicator compatibility target is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_local_spectral_integral_indicator_target_ready :
    SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralIndicatorTarget := by
  exact spectral_measure_pvm_finite_set_carrier_local_spectral_integral_indicator_compat

/-- A local spectral-integral interface attached to the finite `Set` carrier local
operator-valued measure interface. -/
structure SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralInterface where
  Carrier : Type
  integralSlot : SpectralMeasurePVMSpectralSetSlot → SpectralMeasurePVMSpectralIntegralSlot
  endpointTarget : Prop
  indicatorTarget : Prop
  spectralIntegralUpgradeReady : Prop

/-- Concrete local spectral-integral interface for the finite `Set` carrier. -/
def spectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralInterface :
    SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralInterface where
  Carrier := SpectralMeasurePVMFiniteSetCarrier
  integralSlot := spectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralSlot
  endpointTarget := SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralEndpointTarget
  indicatorTarget := SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralIndicatorTarget
  spectralIntegralUpgradeReady := SpectralMeasurePVMOperatorValuedSpectralIntegralUpgradeBridgeReady

/-- Existence target for the local finite `Set` carrier spectral-integral interface. -/
def SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralInterfaceExistenceTarget : Prop :=
  Nonempty SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralInterface

/-- The local finite `Set` carrier spectral-integral interface exists. -/
theorem spectral_measure_pvm_finite_set_carrier_local_spectral_integral_interface_existence_target_ready :
    SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralInterfaceExistenceTarget := by
  exact ⟨spectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralInterface⟩

/-- Bridge from the local finite `Set` carrier operator-valued measure interface
to the symbolic spectral-integral interface. -/
def SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralInterfaceBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSetCarrierLocalOperatorValuedMeasureInterfaceBridgeReady ∧
  SpectralMeasurePVMOperatorValuedSpectralIntegralUpgradeBridgeReady ∧
  SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralEndpointTarget ∧
  SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralIndicatorTarget ∧
  SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralInterfaceExistenceTarget ∧
  SpectralMeasurePVMActualSpectralIntegralRealizationStillOpen ∧
  SpectralMeasurePVMSpectralIntegralSlotRealizationCompatibilityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The local finite `Set` carrier spectral-integral interface bridge is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_local_spectral_integral_interface_bridge_ready :
    SpectralMeasurePVMFiniteSetCarrierLocalSpectralIntegralInterfaceBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_local_operator_valued_measure_interface_bridge_ready,
    spectral_measure_pvm_operator_valued_spectral_integral_upgrade_bridge_ready,
    spectral_measure_pvm_finite_set_carrier_local_spectral_integral_endpoint_target_ready,
    spectral_measure_pvm_finite_set_carrier_local_spectral_integral_indicator_target_ready,
    spectral_measure_pvm_finite_set_carrier_local_spectral_integral_interface_existence_target_ready,
    spectral_measure_pvm_actual_spectral_integral_realization_still_open_ready,
    spectral_measure_pvm_spectral_integral_slot_realization_compatibility_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
