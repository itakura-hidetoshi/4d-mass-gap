import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableBooleanAlgebraLaws

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Order on supported measurable sets, realized as actual `Set` inclusion on the
finite measurable carrier. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSetSubset
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) : Prop :=
  spectralMeasurePVMFiniteSupportedMeasurableSetToSet E ⊆
    spectralMeasurePVMFiniteSupportedMeasurableSetToSet F

/-- Reflexivity of supported measurable set inclusion. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_refl
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E E := by
  intro x hx
  exact hx

/-- Transitivity of supported measurable set inclusion. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_trans
    (E F G : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hEF : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F)
    (hFG : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset F G) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E G := by
  intro x hx
  exact hFG (hEF hx)

/-- The empty supported measurable set is below every supported measurable set. -/
theorem spectral_measure_pvm_finite_supported_measurable_empty_subset
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty E := by
  intro x hx
  exact False.elim hx

/-- Every supported measurable set is below the whole supported measurable set. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_whole
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E
      SpectralMeasurePVMFiniteSupportedMeasurableSet.whole := by
  intro x hx
  trivial

/-- Antisymmetry of supported measurable set inclusion. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_antisymm
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hEF : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F)
    (hFE : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset F E) :
    E = F := by
  cases E <;> cases F
  · rfl
  · have hfalse :
        (SpectralMeasurePVMSpectralSetSlot.emptySet : SpectralMeasurePVMFiniteSetCarrierPoint) ∈
          spectralMeasurePVMFiniteSupportedMeasurableSetToSet
            SpectralMeasurePVMFiniteSupportedMeasurableSet.empty := by
      exact hFE (by
        simp [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
          spectralMeasurePVMFiniteSetCarrierWhole])
    exact False.elim (by
      simpa [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
        spectralMeasurePVMFiniteSetCarrierEmpty] using hfalse)
  · have hfalse :
        (SpectralMeasurePVMSpectralSetSlot.emptySet : SpectralMeasurePVMFiniteSetCarrierPoint) ∈
          spectralMeasurePVMFiniteSupportedMeasurableSetToSet
            SpectralMeasurePVMFiniteSupportedMeasurableSet.empty := by
      exact hEF (by
        simp [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
          spectralMeasurePVMFiniteSetCarrierWhole])
    exact False.elim (by
      simpa [spectralMeasurePVMFiniteSupportedMeasurableSetToSet,
        spectralMeasurePVMFiniteSetCarrierEmpty] using hfalse)
  · rfl

/-- Left union upper bound. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_union_left
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E
      (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) := by
  intro x hx
  rw [spectral_measure_pvm_finite_supported_measurable_set_union_realizes]
  exact Or.inl hx

/-- Right union upper bound. -/
theorem spectral_measure_pvm_finite_supported_measurable_subset_union_right
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset F
      (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) := by
  intro x hx
  rw [spectral_measure_pvm_finite_supported_measurable_set_union_realizes]
  exact Or.inr hx

/-- Union is the least upper bound on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_union_least
    (E F G : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hEG : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E G)
    (hFG : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset F G) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset
      (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) G := by
  intro x hx
  rw [spectral_measure_pvm_finite_supported_measurable_set_union_realizes] at hx
  rcases hx with hxE | hxF
  · exact hEG hxE
  · exact hFG hxF

/-- Left intersection lower bound. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_subset_left
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset
      (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) E := by
  intro x hx
  rw [spectral_measure_pvm_finite_supported_measurable_set_inter_realizes] at hx
  exact hx.1

/-- Right intersection lower bound. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_subset_right
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset
      (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) F := by
  intro x hx
  rw [spectral_measure_pvm_finite_supported_measurable_set_inter_realizes] at hx
  exact hx.2

/-- Intersection is the greatest lower bound on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_greatest
    (E F G : SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hGE : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset G E)
    (hGF : SpectralMeasurePVMFiniteSupportedMeasurableSetSubset G F) :
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset G
      (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) := by
  intro x hx
  rw [spectral_measure_pvm_finite_supported_measurable_set_inter_realizes]
  exact ⟨hGE hx, hGF hx⟩

/-- Order/lattice law target for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableOrderLawTarget : Prop :=
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E E) ∧
  (∀ E F G : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F →
      SpectralMeasurePVMFiniteSupportedMeasurableSetSubset F G →
        SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E G) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E F →
      SpectralMeasurePVMFiniteSupportedMeasurableSetSubset F E → E = F) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty E) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E
      SpectralMeasurePVMFiniteSupportedMeasurableSet.whole) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E
      (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F)) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset F
      (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F)) ∧
  (∀ E F G : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset E G →
      SpectralMeasurePVMFiniteSupportedMeasurableSetSubset F G →
        SpectralMeasurePVMFiniteSupportedMeasurableSetSubset
          (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E F) G) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset
      (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset
      (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F) F) ∧
  (∀ E F G : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetSubset G E →
      SpectralMeasurePVMFiniteSupportedMeasurableSetSubset G F →
        SpectralMeasurePVMFiniteSupportedMeasurableSetSubset G
          (spectralMeasurePVMFiniteSupportedMeasurableSetInter E F))

/-- The supported measurable order/lattice law target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_order_law_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableOrderLawTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_subset_refl,
    spectral_measure_pvm_finite_supported_measurable_subset_trans,
    spectral_measure_pvm_finite_supported_measurable_subset_antisymm,
    spectral_measure_pvm_finite_supported_measurable_empty_subset,
    spectral_measure_pvm_finite_supported_measurable_subset_whole,
    spectral_measure_pvm_finite_supported_measurable_subset_union_left,
    spectral_measure_pvm_finite_supported_measurable_subset_union_right,
    spectral_measure_pvm_finite_supported_measurable_union_least,
    spectral_measure_pvm_finite_supported_measurable_inter_subset_left,
    spectral_measure_pvm_finite_supported_measurable_inter_subset_right,
    spectral_measure_pvm_finite_supported_measurable_inter_greatest⟩

/-- Bridge registering order/lattice laws for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableOrderLawBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableBooleanAlgebraLawBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableOrderLawTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableBooleanCompatibilityBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalFullAxiomPublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported measurable order/lattice law bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_order_law_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableOrderLawBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_boolean_algebra_law_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_order_law_target_ready,
    spectral_measure_pvm_finite_supported_measurable_boolean_compatibility_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_local_full_axiom_public_boundary_held,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
