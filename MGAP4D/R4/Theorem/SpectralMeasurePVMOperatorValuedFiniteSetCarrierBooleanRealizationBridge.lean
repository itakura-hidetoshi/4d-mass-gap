import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSetCarrierRealizationBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Complement of the local spectral slot is realized as set complement on the
finite `Set` carrier. -/
theorem spectral_measure_pvm_finite_set_carrier_complement_realizes
    (s : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSlotToFiniteSetCarrier
        (spectralMeasurePVMSpectralSetSlotComplement s) =
      (spectralMeasurePVMSpectralSlotToFiniteSetCarrier s)ᶜ := by
  cases s <;> ext a <;>
    simp [spectralMeasurePVMSpectralSlotToFiniteSetCarrier,
      spectralMeasurePVMFiniteSetCarrierEmpty,
      spectralMeasurePVMFiniteSetCarrierWhole,
      spectralMeasurePVMSpectralSetSlotComplement]

/-- Union of local spectral slots is realized as set union on the finite `Set`
carrier. -/
theorem spectral_measure_pvm_finite_set_carrier_union_realizes
    (s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSlotToFiniteSetCarrier
        (spectralMeasurePVMSpectralSetSlotUnion s t) =
      spectralMeasurePVMSpectralSlotToFiniteSetCarrier s ∪
        spectralMeasurePVMSpectralSlotToFiniteSetCarrier t := by
  cases s <;> cases t <;> ext a <;>
    simp [spectralMeasurePVMSpectralSlotToFiniteSetCarrier,
      spectralMeasurePVMFiniteSetCarrierEmpty,
      spectralMeasurePVMFiniteSetCarrierWhole,
      spectralMeasurePVMSpectralSetSlotUnion]

/-- Intersection of local spectral slots is realized as set intersection on the
finite `Set` carrier. -/
theorem spectral_measure_pvm_finite_set_carrier_inter_realizes
    (s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSlotToFiniteSetCarrier
        (spectralMeasurePVMSpectralSetSlotInter s t) =
      spectralMeasurePVMSpectralSlotToFiniteSetCarrier s ∩
        spectralMeasurePVMSpectralSlotToFiniteSetCarrier t := by
  cases s <;> cases t <;> ext a <;>
    simp [spectralMeasurePVMSpectralSlotToFiniteSetCarrier,
      spectralMeasurePVMFiniteSetCarrierEmpty,
      spectralMeasurePVMFiniteSetCarrierWhole,
      spectralMeasurePVMSpectralSetSlotInter]

/-- Empty and whole are realized as the corresponding finite set endpoints. -/
def SpectralMeasurePVMFiniteSetCarrierEndpointRealizationTarget : Prop :=
  spectralMeasurePVMSpectralSlotToFiniteSetCarrier SpectralMeasurePVMSpectralSetSlot.emptySet =
    spectralMeasurePVMFiniteSetCarrierEmpty ∧
  spectralMeasurePVMSpectralSlotToFiniteSetCarrier SpectralMeasurePVMSpectralSetSlot.wholeSet =
    spectralMeasurePVMFiniteSetCarrierWhole

/-- Boolean operations on local spectral slots are realized as Boolean operations
on the finite `Set` carrier. -/
def SpectralMeasurePVMFiniteSetCarrierBooleanOperationRealizationTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSlotToFiniteSetCarrier
        (spectralMeasurePVMSpectralSetSlotComplement s) =
      (spectralMeasurePVMSpectralSlotToFiniteSetCarrier s)ᶜ) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSlotToFiniteSetCarrier
        (spectralMeasurePVMSpectralSetSlotUnion s t) =
      spectralMeasurePVMSpectralSlotToFiniteSetCarrier s ∪
        spectralMeasurePVMSpectralSlotToFiniteSetCarrier t) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSlotToFiniteSetCarrier
        (spectralMeasurePVMSpectralSetSlotInter s t) =
      spectralMeasurePVMSpectralSlotToFiniteSetCarrier s ∩
        spectralMeasurePVMSpectralSlotToFiniteSetCarrier t)

/-- Endpoint realization is ready for the finite `Set` carrier. -/
theorem spectral_measure_pvm_finite_set_carrier_endpoint_realization_target_ready :
    SpectralMeasurePVMFiniteSetCarrierEndpointRealizationTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_empty_slot_realizes,
    spectral_measure_pvm_finite_set_carrier_whole_slot_realizes⟩

/-- Boolean operation realization is ready for the finite `Set` carrier. -/
theorem spectral_measure_pvm_finite_set_carrier_boolean_operation_realization_target_ready :
    SpectralMeasurePVMFiniteSetCarrierBooleanOperationRealizationTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_complement_realizes,
    spectral_measure_pvm_finite_set_carrier_union_realizes,
    spectral_measure_pvm_finite_set_carrier_inter_realizes⟩

/-- The finite `Set` carrier is now a concrete Boolean host for the current
R4-local two-slot spectral algebra.  This is still not a genuine Borel
sigma-algebra realization. -/
def SpectralMeasurePVMFiniteSetCarrierBooleanRealizationBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSetCarrierRealizationBridgeReady ∧
  SpectralMeasurePVMFiniteSetCarrierEndpointRealizationTarget ∧
  SpectralMeasurePVMFiniteSetCarrierBooleanOperationRealizationTarget ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSigmaBooleanClosureStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite `Set` carrier Boolean realization bridge is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_boolean_realization_bridge_ready :
    SpectralMeasurePVMFiniteSetCarrierBooleanRealizationBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_realization_bridge_ready,
    spectral_measure_pvm_finite_set_carrier_endpoint_realization_target_ready,
    spectral_measure_pvm_finite_set_carrier_boolean_operation_realization_target_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_sigma_boolean_closure_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
