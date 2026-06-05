import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedGenuinePVMTransitionCompletionBundle

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- A finite point type used only to realize the current R4-local two-slot carrier
inside mathlib's `Set` universe.

This is deliberately finite/local.  It is not the genuine Borel space of the
self-adjoint operator. -/
abbrev SpectralMeasurePVMFiniteSetCarrierPoint := SpectralMeasurePVMSpectralSetSlot

/-- The finite set-carrier hosting the current local spectral slots. -/
abbrev SpectralMeasurePVMFiniteSetCarrier := Set SpectralMeasurePVMFiniteSetCarrierPoint

/-- Empty finite set-carrier. -/
def spectralMeasurePVMFiniteSetCarrierEmpty : SpectralMeasurePVMFiniteSetCarrier :=
  ∅

/-- Whole finite set-carrier. -/
def spectralMeasurePVMFiniteSetCarrierWhole : SpectralMeasurePVMFiniteSetCarrier :=
  Set.univ

/-- Realize the current two spectral slots as actual `Set`s. -/
def spectralMeasurePVMSpectralSlotToFiniteSetCarrier :
    SpectralMeasurePVMSpectralSetSlot → SpectralMeasurePVMFiniteSetCarrier
  | SpectralMeasurePVMSpectralSetSlot.emptySet => spectralMeasurePVMFiniteSetCarrierEmpty
  | SpectralMeasurePVMSpectralSetSlot.wholeSet => spectralMeasurePVMFiniteSetCarrierWhole

/-- The empty spectral slot realizes as the empty finite set-carrier. -/
theorem spectral_measure_pvm_finite_set_carrier_empty_slot_realizes :
    spectralMeasurePVMSpectralSlotToFiniteSetCarrier SpectralMeasurePVMSpectralSetSlot.emptySet =
      spectralMeasurePVMFiniteSetCarrierEmpty := by
  rfl

/-- The whole spectral slot realizes as the whole finite set-carrier. -/
theorem spectral_measure_pvm_finite_set_carrier_whole_slot_realizes :
    spectralMeasurePVMSpectralSlotToFiniteSetCarrier SpectralMeasurePVMSpectralSetSlot.wholeSet =
      spectralMeasurePVMFiniteSetCarrierWhole := by
  rfl

/-- A concrete `Set`-based carrier interface for the current R4-local two-slot surface. -/
def spectralMeasurePVMFiniteSetBorelIndexedCarrierInterface :
    SpectralMeasurePVMBorelIndexedCarrierInterface where
  Carrier := SpectralMeasurePVMFiniteSetCarrier
  emptyCarrier := spectralMeasurePVMFiniteSetCarrierEmpty
  wholeCarrier := spectralMeasurePVMFiniteSetCarrierWhole
  slotToCarrier := spectralMeasurePVMSpectralSlotToFiniteSetCarrier
  emptySlotRealizes := spectral_measure_pvm_finite_set_carrier_empty_slot_realizes
  wholeSlotRealizes := spectral_measure_pvm_finite_set_carrier_whole_slot_realizes

/-- Existence target for the concrete finite `Set`-carrier realization. -/
def SpectralMeasurePVMFiniteSetCarrierRealizationTarget : Prop :=
  Nonempty SpectralMeasurePVMBorelIndexedCarrierInterface ∧
  spectralMeasurePVMFiniteSetBorelIndexedCarrierInterface.slotToCarrier
      SpectralMeasurePVMSpectralSetSlot.emptySet =
    spectralMeasurePVMFiniteSetBorelIndexedCarrierInterface.emptyCarrier ∧
  spectralMeasurePVMFiniteSetBorelIndexedCarrierInterface.slotToCarrier
      SpectralMeasurePVMSpectralSetSlot.wholeSet =
    spectralMeasurePVMFiniteSetBorelIndexedCarrierInterface.wholeCarrier

/-- The concrete finite `Set`-carrier realization target is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_realization_target_ready :
    SpectralMeasurePVMFiniteSetCarrierRealizationTarget := by
  exact ⟨
    ⟨spectralMeasurePVMFiniteSetBorelIndexedCarrierInterface⟩,
    spectral_measure_pvm_finite_set_carrier_empty_slot_realizes,
    spectral_measure_pvm_finite_set_carrier_whole_slot_realizes⟩

/-- The finite `Set`-carrier realization improves the first transition frontier,
but still does not close the genuine Borel carrier. -/
def SpectralMeasurePVMFiniteSetCarrierRealizationBridgeReady : Prop :=
  SpectralMeasurePVMOperatorValuedGenuinePVMTransitionCompletionBundleReady ∧
  SpectralMeasurePVMOperatorValuedGenuineBorelIndexedCarrierBridgeReady ∧
  SpectralMeasurePVMFiniteSetCarrierRealizationTarget ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite `Set`-carrier realization bridge is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_realization_bridge_ready :
    SpectralMeasurePVMFiniteSetCarrierRealizationBridgeReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_genuine_pvm_transition_completion_bundle_ready,
    spectral_measure_pvm_operator_valued_genuine_borel_indexed_carrier_bridge_ready,
    spectral_measure_pvm_finite_set_carrier_realization_target_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
