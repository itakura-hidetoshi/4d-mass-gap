import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableOrderLaws

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Intersection of supported measurable sets is realized by operator
multiplication on the local concrete operator assignment. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_operator_mul
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
      spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) := by
  cases E <;> cases F <;> rfl

/-- Intersection of supported measurable sets is also realized by reversed
operator multiplication. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_operator_reversed_mul
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
      spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) := by
  cases E <;> cases F <;> rfl

/-- If `E ≤ F`, then `P(E)P(F)=P(E)` on the supported measurable local surface. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_operator_left_absorb
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hEF : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E := by
  cases E <;> cases F <;> try rfl
  have hfalse :
      (SpectralMeasurePVMSpectralSetSlot.emptySet : SpectralMeasurePVMFiniteSetCarrierPoint) ∈
        spectralMeasurePVMFiniteSupportedMeasurableSetToSet
          SpectralMeasurePVMFiniteSupportedMeasurableSet.empty := by
    exact hEF (by
      simp [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
        spectralMeasurePVMFiniteSetCarrierWhole])
  exact False.elim (by
    simpa [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
      spectralMeasurePVMFiniteSetCarrierEmpty] using hfalse)

/-- If `E ≤ F`, then `P(F)P(E)=P(E)` on the supported measurable local surface. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_operator_right_absorb
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hEF : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E := by
  cases E <;> cases F <;> try rfl
  have hfalse :
      (SpectralMeasurePVMSpectralSetSlot.emptySet : SpectralMeasurePVMFiniteSetCarrierPoint) ∈
        spectralMeasurePVMFiniteSupportedMeasurableSetToSet
          SpectralMeasurePVMFiniteSupportedMeasurableSet.empty := by
    exact hEF (by
      simp [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
        spectralMeasurePVMFiniteSetCarrierWhole])
  exact False.elim (by
    simpa [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
      spectralMeasurePVMFiniteSetCarrierEmpty] using hfalse)

/-- If `E ≤ F`, the supported measurable intersection collapses to `E`. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_inter_eq_left
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hEF : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F) :
    spectralMeasurePVMFiniteSupportedMeasurableSetInter E F = E := by
  apply spectral_measure_pvm_finite_supported_measurable_subset_antisymm
  · exact spectral_measure_pvm_finite_supported_measurable_inter_subset_left E F
  · exact spectral_measure_pvm_finite_supported_measurable_inter_greatest E F E
      (spectral_measure_pvm_finite_supported_measurable_subset_refl E) hEF

/-- If `E ≤ F`, the supported measurable union collapses to `F`. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_union_eq_right
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hEF : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F) :
    spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F = F := by
  apply spectral_measure_pvm_finite_supported_measurable_subset_antisymm
  · exact spectral_measure_pvm_finite_supported_measurable_union_least E F F hEF
      (spectral_measure_pvm_finite_supported_measurable_subset_refl F)
  · exact spectral_measure_pvm_finite_supported_measurable_subset_union_right E F

/-- Operator/order compatibility target for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableOperatorOrderCompatibilityTarget : Prop :=
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
      spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) =
      spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F →
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) =
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F →
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
          (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F →
      spectralMeasurePVMFiniteSupportedMeasurableSetInter E F = E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F →
      spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F = F)

/-- The supported measurable operator/order compatibility target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_order_compatibility_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableOperatorOrderCompatibilityTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_inter_operator_mul,
    spectral_measure_pvm_finite_supported_measurable_inter_operator_reversed_mul,
    spectral_measure_pvm_finite_supported_measurable_subset_operator_left_absorb,
    spectral_measure_pvm_finite_supported_measurable_subset_operator_right_absorb,
    spectral_measure_pvm_finite_supported_measurable_subset_inter_eq_left,
    spectral_measure_pvm_finite_supported_measurable_subset_union_eq_right⟩

/-- Bridge registering operator/order compatibility for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableOperatorOrderCompatibilityBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableOrderLawBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableOperatorOrderCompatibilityTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalFullAxiomPublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported measurable operator/order compatibility bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_order_compatibility_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableOperatorOrderCompatibilityBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_order_law_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_operator_order_compatibility_target_ready,
    spectral_measure_pvm_finite_supported_measurable_local_full_axiom_public_boundary_held,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
