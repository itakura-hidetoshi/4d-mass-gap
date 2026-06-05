import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableSpectralIntegralBooleanFinalReceipt

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The concrete `Set` realization of supported measurable sets is faithful. -/
theorem spectral_measure_pvm_finite_supported_measurable_to_set_injective
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (h : spectralMeasurePVMFiniteSupportedMeasurableSetToSet E =
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet F) :
    E = F := by
  cases E <;> cases F
  · rfl
  · have hfalse :
        (SpectralMeasurePVMSpectralSetSlot.emptySet : SpectralMeasurePVMFiniteSetCarrierPoint) ∈
          spectralMeasurePVMFiniteSupportedMeasurableSetToSet
            SpectralMeasurePVMFiniteSupportedMeasurableSet.empty := by
      rw [h]
      simp [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
        spectralMeasurePVMFiniteSetCarrierWhole]
    exact False.elim (by
      simpa [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
        spectralMeasurePVMFiniteSetCarrierEmpty] using hfalse)
  · have hfalse :
        (SpectralMeasurePVMSpectralSetSlot.emptySet : SpectralMeasurePVMFiniteSetCarrierPoint) ∈
          spectralMeasurePVMFiniteSupportedMeasurableSetToSet
            SpectralMeasurePVMFiniteSupportedMeasurableSet.empty := by
      rw [← h]
      simp [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
        spectralMeasurePVMFiniteSetCarrierWhole]
    exact False.elim (by
      simpa [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
        spectralMeasurePVMFiniteSetCarrierEmpty] using hfalse)
  · rfl

/-- The spectral-set-slot realization of supported measurable sets is faithful. -/
theorem spectral_measure_pvm_finite_supported_measurable_to_slot_injective
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (h : spectralMeasurePVMFiniteSupportedMeasurableSetToSlot E =
      spectralMeasurePVMFiniteSupportedMeasurableSetToSlot F) :
    E = F := by
  cases E <;> cases F <;> try rfl <;> cases h

/-- The local operator assignment is faithful on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_candidate_injective
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (h : spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) :
    E = F := by
  cases E <;> cases F
  · rfl
  · have hzid :
        SpectralMeasurePVMConcreteBoundedOperator.zero =
          SpectralMeasurePVMConcreteBoundedOperator.identity := by
      simpa [spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate,
        spectralMeasurePVMFiniteSupportedMeasurableSetToSlot,
        spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate,
        spectralMeasurePVMConcreteNormalizationCandidate,
        spectralMeasurePVMConcreteIndexFromSpectralSetSlot] using h
    cases hzid
  · have hidz :
        SpectralMeasurePVMConcreteBoundedOperator.identity =
          SpectralMeasurePVMConcreteBoundedOperator.zero := by
      simpa [spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate,
        spectralMeasurePVMFiniteSupportedMeasurableSetToSlot,
        spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate,
        spectralMeasurePVMConcreteNormalizationCandidate,
        spectralMeasurePVMConcreteIndexFromSpectralSetSlot] using h
    cases hidz
  · rfl

/-- The symbolic spectral-integral slot assignment is faithful on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_spectral_integral_slot_injective
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (h : spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E =
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F) :
    E = F := by
  cases E <;> cases F
  · rfl
  · have hzid :
        SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral =
          SpectralMeasurePVMSpectralIntegralSlot.identityIntegral := by
      simpa [spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot,
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate,
        spectralMeasurePVMFiniteSupportedMeasurableSetToSlot,
        spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate,
        spectralMeasurePVMConcreteNormalizationCandidate,
        spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
        spectralMeasurePVMSpectralIntegralSlotFromOperator] using h
    cases hzid
  · have hidz :
        SpectralMeasurePVMSpectralIntegralSlot.identityIntegral =
          SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral := by
      simpa [spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot,
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate,
        spectralMeasurePVMFiniteSupportedMeasurableSetToSlot,
        spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate,
        spectralMeasurePVMConcreteNormalizationCandidate,
        spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
        spectralMeasurePVMSpectralIntegralSlotFromOperator] using h
    cases hidz
  · rfl

/-- Faithfulness target for the supported measurable local representations. -/
def SpectralMeasurePVMFiniteSupportedMeasurableRepresentationFaithfulnessTarget : Prop :=
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetToSet E =
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet F → E = F) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetToSlot E =
      spectralMeasurePVMFiniteSupportedMeasurableSetToSlot F → E = F) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F → E = F) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E =
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F → E = F)

/-- The supported measurable local representations are faithful. -/
theorem spectral_measure_pvm_finite_supported_measurable_representation_faithfulness_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableRepresentationFaithfulnessTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_to_set_injective,
    spectral_measure_pvm_finite_supported_measurable_to_slot_injective,
    spectral_measure_pvm_finite_supported_measurable_operator_candidate_injective,
    spectral_measure_pvm_finite_supported_measurable_spectral_integral_slot_injective⟩

/-- Bridge registering faithfulness of the supported measurable local representation. -/
def SpectralMeasurePVMFiniteSupportedMeasurableRepresentationFaithfulnessBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableSpectralIntegralBooleanPublicBoundaryHeld ∧
  SpectralMeasurePVMFiniteSupportedMeasurableRepresentationFaithfulnessTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableBooleanAlgebraLawBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableOperatorBooleanLawBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSpectralIntegralBooleanLawBridgeReady ∧
  SpectralMeasurePVMActualSpectralIntegralRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported measurable local representation faithfulness bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_representation_faithfulness_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableRepresentationFaithfulnessBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_spectral_integral_boolean_public_boundary_held,
    spectral_measure_pvm_finite_supported_measurable_representation_faithfulness_target_ready,
    spectral_measure_pvm_finite_supported_measurable_boolean_algebra_law_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_operator_boolean_law_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_spectral_integral_boolean_law_bridge_ready,
    spectral_measure_pvm_actual_spectral_integral_realization_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
