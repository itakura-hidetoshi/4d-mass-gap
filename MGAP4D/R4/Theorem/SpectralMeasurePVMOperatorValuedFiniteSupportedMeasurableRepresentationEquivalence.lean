import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableRepresentationFaithfulness

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Equality of supported measurable sets is equivalent to equality of their
concrete `Set` realizations. -/
theorem spectral_measure_pvm_finite_supported_measurable_eq_iff_to_set_eq
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    E = F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet E =
        spectralMeasurePVMFiniteSupportedMeasurableSetToSet F := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    exact spectral_measure_pvm_finite_supported_measurable_to_set_injective E F h

/-- Equality of supported measurable sets is equivalent to equality of their
spectral-set slots. -/
theorem spectral_measure_pvm_finite_supported_measurable_eq_iff_to_slot_eq
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    E = F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetToSlot E =
        spectralMeasurePVMFiniteSupportedMeasurableSetToSlot F := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    exact spectral_measure_pvm_finite_supported_measurable_to_slot_injective E F h

/-- Equality of supported measurable sets is equivalent to equality of their
local operator candidates. -/
theorem spectral_measure_pvm_finite_supported_measurable_eq_iff_operator_candidate_eq
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    E = F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E =
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    exact spectral_measure_pvm_finite_supported_measurable_operator_candidate_injective E F h

/-- Equality of supported measurable sets is equivalent to equality of their
symbolic spectral-integral slots. -/
theorem spectral_measure_pvm_finite_supported_measurable_eq_iff_spectral_integral_slot_eq
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    E = F ↔
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E =
        spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    exact spectral_measure_pvm_finite_supported_measurable_spectral_integral_slot_injective E F h

/-- Inclusion is equivalent to intersection collapse. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_iff_inter_eq_left
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetInter E F = E := by
  constructor
  · intro hEF
    exact spectral_measure_pvm_finite_supported_measurable_subset_inter_eq_left E F hEF
  · intro h
    change spectralMeasurePVMFiniteSupportedMeasurableSetToSet E ⊆
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet F
    intro x hx
    have hxInter :
        x ∈ spectralMeasurePVMFiniteSupportedMeasurableSetToSet
          (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) := by
      rw [h]
      exact hx
    rw [spectral_measure_pvm_finite_supported_measurable_set_inter_realizes] at hxInter
    exact hxInter.2

/-- Inclusion is equivalent to union collapse. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_iff_union_eq_right
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F = F := by
  constructor
  · intro hEF
    exact spectral_measure_pvm_finite_supported_measurable_subset_union_eq_right E F hEF
  · intro h
    change spectralMeasurePVMFiniteSupportedMeasurableSetToSet E ⊆
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet F
    intro x hx
    have hxUnion :
        x ∈ spectralMeasurePVMFiniteSupportedMeasurableSetToSet
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) := by
      rw [spectral_measure_pvm_finite_supported_measurable_set_union_realizes]
      exact Or.inl hx
    rw [h] at hxUnion
    exact hxUnion

/-- Inclusion is equivalent to left operator absorption. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_iff_operator_left_absorb
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) =
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E := by
  constructor
  · intro hEF
    exact spectral_measure_pvm_finite_supported_measurable_subset_operator_left_absorb E F hEF
  · intro h
    have hOp :
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
            (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
          spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E := by
      rw [spectral_measure_pvm_finite_supported_measurable_inter_operator_mul]
      exact h
    have hInter : spectralMeasurePVMFiniteSupportedMeasurableSetInter E F = E :=
      spectral_measure_pvm_finite_supported_measurable_operator_candidate_injective
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) E hOp
    exact (spectral_measure_pvm_finite_supported_measurable_subset_iff_inter_eq_left E F).2 hInter

/-- Inclusion is equivalent to right operator absorption. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_iff_operator_right_absorb
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E := by
  constructor
  · intro hEF
    exact spectral_measure_pvm_finite_supported_measurable_subset_operator_right_absorb E F hEF
  · intro h
    have hOp :
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
            (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
          spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E := by
      rw [spectral_measure_pvm_finite_supported_measurable_inter_operator_reversed_mul]
      exact h
    have hInter : spectralMeasurePVMFiniteSupportedMeasurableSetInter E F = E :=
      spectral_measure_pvm_finite_supported_measurable_operator_candidate_injective
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) E hOp
    exact (spectral_measure_pvm_finite_supported_measurable_subset_iff_inter_eq_left E F).2 hInter

/-- Inclusion is equivalent to symbolic spectral-integral intersection absorption. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_iff_spectral_integral_inter_absorb
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
          (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
        spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E := by
  constructor
  · intro hEF
    exact spectral_measure_pvm_finite_supported_measurable_subset_spectral_integral_inter_eq_left E F hEF
  · intro h
    have hInter : spectralMeasurePVMFiniteSupportedMeasurableSetInter E F = E :=
      spectral_measure_pvm_finite_supported_measurable_spectral_integral_slot_injective
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) E h
    exact (spectral_measure_pvm_finite_supported_measurable_subset_iff_inter_eq_left E F).2 hInter

/-- Inclusion is equivalent to symbolic spectral-integral union absorption. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_iff_spectral_integral_union_absorb
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
        spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F := by
  constructor
  · intro hEF
    exact spectral_measure_pvm_finite_supported_measurable_subset_spectral_integral_union_eq_right E F hEF
  · intro h
    have hUnion : spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F = F :=
      spectral_measure_pvm_finite_supported_measurable_spectral_integral_slot_injective
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) F h
    exact (spectral_measure_pvm_finite_supported_measurable_subset_iff_union_eq_right E F).2 hUnion

/-- Representation equivalence target for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableRepresentationEquivalenceTarget : Prop :=
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    E = F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetToSet E =
        spectralMeasurePVMFiniteSupportedMeasurableSetToSet F) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    E = F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetToSlot E =
        spectralMeasurePVMFiniteSupportedMeasurableSetToSlot F) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    E = F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E =
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    E = F ↔
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E =
        spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetInter E F = E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F = F) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) =
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
          (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
        spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) =
        spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot F)

/-- The supported measurable representation equivalence target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_representation_equivalence_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableRepresentationEquivalenceTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_eq_iff_to_set_eq,
    spectral_measure_pvm_finite_supported_measurable_eq_iff_to_slot_eq,
    spectral_measure_pvm_finite_supported_measurable_eq_iff_operator_candidate_eq,
    spectral_measure_pvm_finite_supported_measurable_eq_iff_spectral_integral_slot_eq,
    spectral_measure_pvm_finite_supported_measurable_subset_iff_inter_eq_left,
    spectral_measure_pvm_finite_supported_measurable_subset_iff_union_eq_right,
    spectral_measure_pvm_finite_supported_measurable_subset_iff_operator_left_absorb,
    spectral_measure_pvm_finite_supported_measurable_subset_iff_operator_right_absorb,
    spectral_measure_pvm_finite_supported_measurable_subset_iff_spectral_integral_inter_absorb,
    spectral_measure_pvm_finite_supported_measurable_subset_iff_spectral_integral_union_absorb⟩

/-- Bridge registering equivalence of supported measurable local representations. -/
def SpectralMeasurePVMFiniteSupportedMeasurableRepresentationEquivalenceBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableRepresentationFaithfulnessBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableRepresentationEquivalenceTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableOrderLawBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableOperatorOrderCompatibilityBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSpectralIntegralBooleanPublicBoundaryHeld ∧
  SpectralMeasurePVMActualSpectralIntegralRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported measurable local representation equivalence bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_representation_equivalence_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableRepresentationEquivalenceBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_representation_faithfulness_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_representation_equivalence_target_ready,
    spectral_measure_pvm_finite_supported_measurable_order_law_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_operator_order_compatibility_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_spectral_integral_boolean_public_boundary_held,
    spectral_measure_pvm_actual_spectral_integral_realization_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
