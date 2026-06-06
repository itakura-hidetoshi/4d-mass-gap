import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableBooleanEmbedding

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Disjointness on the supported finite measurable surface.  It is defined by
collapse of the local intersection to the empty supported set. -/
def SpectralMeasurePVMFiniteSupportedMeasurableDisjoint
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) : Prop :=
  spectralMeasurePVMFiniteSupportedMeasurableSetInter E F =
    SpectralMeasurePVMFiniteSupportedMeasurableSet.empty

/-- Disjointness is exactly intersection collapse to empty. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_iff_inter_empty
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetInter E F =
        SpectralMeasurePVMFiniteSupportedMeasurableSet.empty := by
  rfl

/-- Disjointness is symmetric. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_symm
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (h : SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint F E := by
  unfold SpectralMeasurePVMFiniteSupportedMeasurableDisjoint at h ⊢
  rw [spectral_measure_pvm_finite_supported_measurable_inter_comm F E]
  exact h

/-- The empty supported measurable set is disjoint from every supported measurable set. -/
theorem spectral_measure_pvm_finite_supported_measurable_empty_disjoint_left
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty E := by
  cases E <;> rfl

/-- Every supported measurable set is disjoint from the empty supported measurable set. -/
theorem spectral_measure_pvm_finite_supported_measurable_empty_disjoint_right
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty := by
  cases E <;> rfl

/-- A supported measurable set is disjoint from its complement. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_complement_right
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E
      (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E) := by
  cases E <;> rfl

/-- A complement is disjoint from its supported measurable set. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_complement_left
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint
      (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E) E := by
  cases E <;> rfl

/-- Disjointness is equivalent to zero left operator product. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_iff_operator_left_product_zero
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) =
        SpectralMeasurePVMConcreteBoundedOperator.zero := by
  constructor
  · intro h
    unfold SpectralMeasurePVMFiniteSupportedMeasurableDisjoint at h
    rw [← spectral_measure_pvm_finite_supported_measurable_inter_operator_mul E F]
    rw [h]
    rfl
  · intro h
    unfold SpectralMeasurePVMFiniteSupportedMeasurableDisjoint
    exact spectral_measure_pvm_finite_supported_measurable_operator_candidate_injective
      (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F)
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty
      (by
        rw [spectral_measure_pvm_finite_supported_measurable_inter_operator_mul]
        rw [h]
        rfl)

/-- Disjointness is equivalent to zero right operator product. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_iff_operator_right_product_zero
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
        SpectralMeasurePVMConcreteBoundedOperator.zero := by
  constructor
  · intro h
    unfold SpectralMeasurePVMFiniteSupportedMeasurableDisjoint at h
    rw [← spectral_measure_pvm_finite_supported_measurable_inter_operator_reversed_mul E F]
    rw [h]
    rfl
  · intro h
    unfold SpectralMeasurePVMFiniteSupportedMeasurableDisjoint
    exact spectral_measure_pvm_finite_supported_measurable_operator_candidate_injective
      (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F)
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty
      (by
        rw [spectral_measure_pvm_finite_supported_measurable_inter_operator_reversed_mul]
        rw [h]
        rfl)

/-- Disjointness is equivalent to zero symbolic spectral-integral slot for the intersection. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjoint_iff_spectral_integral_inter_zero
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
          (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
        SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral := by
  constructor
  · intro h
    unfold SpectralMeasurePVMFiniteSupportedMeasurableDisjoint at h
    rw [h]
    exact spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_empty_slot
  · intro h
    unfold SpectralMeasurePVMFiniteSupportedMeasurableDisjoint
    exact spectral_measure_pvm_finite_supported_measurable_spectral_integral_slot_injective
      (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F)
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty
      (by
        rw [spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_empty_slot]
        exact h)

/-- Disjointness equivalence target for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableDisjointnessEquivalenceTarget : Prop :=
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableSetInter E F =
        SpectralMeasurePVMFiniteSupportedMeasurableSet.empty) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F →
      SpectralMeasurePVMFiniteSupportedMeasurableDisjoint F E) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty E) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E
      (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint
      (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E) E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) =
        SpectralMeasurePVMConcreteBoundedOperator.zero) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
        SpectralMeasurePVMConcreteBoundedOperator.zero) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableDisjoint E F ↔
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
          (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
        SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral)

/-- The supported measurable disjointness equivalence target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjointness_equivalence_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjointnessEquivalenceTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_disjoint_iff_inter_empty,
    spectral_measure_pvm_finite_supported_measurable_disjoint_symm,
    spectral_measure_pvm_finite_supported_measurable_empty_disjoint_left,
    spectral_measure_pvm_finite_supported_measurable_empty_disjoint_right,
    spectral_measure_pvm_finite_supported_measurable_disjoint_complement_right,
    spectral_measure_pvm_finite_supported_measurable_disjoint_complement_left,
    spectral_measure_pvm_finite_supported_measurable_disjoint_iff_operator_left_product_zero,
    spectral_measure_pvm_finite_supported_measurable_disjoint_iff_operator_right_product_zero,
    spectral_measure_pvm_finite_supported_measurable_disjoint_iff_spectral_integral_inter_zero⟩

/-- Bridge registering disjointness equivalence for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableDisjointnessEquivalenceBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableBooleanEmbeddingPublicBoundaryHeld ∧
  SpectralMeasurePVMFiniteSupportedMeasurableDisjointnessEquivalenceTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableOperatorBooleanEmbeddingTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSpectralIntegralBooleanEmbeddingTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalRepresentationCompletionPublicBoundaryHeld ∧
  SpectralMeasurePVMActualSpectralIntegralRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported measurable disjointness equivalence bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_disjointness_equivalence_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableDisjointnessEquivalenceBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_boolean_embedding_public_boundary_held,
    spectral_measure_pvm_finite_supported_measurable_disjointness_equivalence_target_ready,
    spectral_measure_pvm_finite_supported_measurable_operator_boolean_embedding_target_ready,
    spectral_measure_pvm_finite_supported_measurable_spectral_integral_boolean_embedding_target_ready,
    spectral_measure_pvm_finite_supported_measurable_local_representation_completion_public_boundary_held,
    spectral_measure_pvm_actual_spectral_integral_realization_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
