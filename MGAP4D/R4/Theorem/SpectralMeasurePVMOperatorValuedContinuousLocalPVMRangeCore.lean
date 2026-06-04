import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMOrderCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Range membership for the R4 local PVM projection attached to a symbolic
spectral-set slot.  This is an existential, pointwise surface; it is not yet a
closed subspace/range theorem in the eventual Hilbert-space PVM. -/
def SpectralMeasurePVMContinuousLocalPVMRangeMember
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) : Prop :=
  ∃ y : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMSpectralSetSlotContinuousProjection s y = x

/-- Zero is in the range of the empty-slot projection. -/
theorem spectral_measure_pvm_continuous_local_pvm_empty_range_zero :
    SpectralMeasurePVMContinuousLocalPVMRangeMember
      SpectralMeasurePVMSpectralSetSlot.emptySet
      (0 : MathlibAnalytic.ConcreteL2R1HilbertCarrier) := by
  exact ⟨0, rfl⟩

/-- Every vector is in the range of the whole-slot projection. -/
theorem spectral_measure_pvm_continuous_local_pvm_whole_range_all
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousLocalPVMRangeMember
      SpectralMeasurePVMSpectralSetSlot.wholeSet x := by
  exact ⟨x, rfl⟩

/-- A vector in the empty-slot range is zero. -/
theorem spectral_measure_pvm_continuous_local_pvm_empty_range_member_eq_zero
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hx : SpectralMeasurePVMContinuousLocalPVMRangeMember
      SpectralMeasurePVMSpectralSetSlot.emptySet x) :
    x = 0 := by
  rcases hx with ⟨y, hy⟩
  exact hy.symm

/-- Range membership is stable under the corresponding projection. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_member_projected
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hx : SpectralMeasurePVMContinuousLocalPVMRangeMember s x) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection s x = x := by
  rcases hx with ⟨y, rfl⟩
  cases s <;> rfl

/-- Every projected vector is in the range of that projection. -/
theorem spectral_measure_pvm_continuous_local_pvm_projected_range_member
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousLocalPVMRangeMember s
      (spectralMeasurePVMSpectralSetSlotContinuousProjection s x) := by
  exact ⟨x, rfl⟩

/-- Order-induced range inclusion: if `s ⊆ t`, then every vector in the range of
`P(s)` is in the range of `P(t)`. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_inclusion_of_subset
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hx : SpectralMeasurePVMContinuousLocalPVMRangeMember s x) :
    SpectralMeasurePVMContinuousLocalPVMRangeMember t x := by
  rcases hx with ⟨y, hy⟩
  refine ⟨spectralMeasurePVMSpectralSetSlotContinuousProjection s y, ?_⟩
  rw [hy]
  exact spectral_measure_pvm_spectral_set_slot_projection_subset_right_absorption_apply s t hst y

/-- If `s ⊆ t`, then the complement range is included in the reverse direction. -/
theorem spectral_measure_pvm_continuous_local_pvm_complement_range_inclusion_of_subset
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hx : SpectralMeasurePVMContinuousLocalPVMRangeMember
      (spectralMeasurePVMSpectralSetSlotComplement t) x) :
    SpectralMeasurePVMContinuousLocalPVMRangeMember
      (spectralMeasurePVMSpectralSetSlotComplement s) x := by
  exact spectral_measure_pvm_continuous_local_pvm_range_inclusion_of_subset
    (spectralMeasurePVMSpectralSetSlotComplement t)
    (spectralMeasurePVMSpectralSetSlotComplement s)
    (spectral_measure_pvm_spectral_set_slot_subset_complement_antitone s t hst)
    x hx

/-- Range membership target for empty and whole slots. -/
def SpectralMeasurePVMContinuousLocalPVMBasicRangeTarget : Prop :=
  SpectralMeasurePVMContinuousLocalPVMRangeMember
    SpectralMeasurePVMSpectralSetSlot.emptySet
    (0 : MathlibAnalytic.ConcreteL2R1HilbertCarrier) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    SpectralMeasurePVMContinuousLocalPVMRangeMember
      SpectralMeasurePVMSpectralSetSlot.wholeSet x) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    SpectralMeasurePVMContinuousLocalPVMRangeMember
      SpectralMeasurePVMSpectralSetSlot.emptySet x → x = 0)

/-- Projection-fixed characterization direction for range members. -/
def SpectralMeasurePVMContinuousLocalPVMRangeProjectionFixedTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousLocalPVMRangeMember s x →
        spectralMeasurePVMSpectralSetSlotContinuousProjection s x = x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousLocalPVMRangeMember s
        (spectralMeasurePVMSpectralSetSlotContinuousProjection s x))

/-- Order-induced range-inclusion target for the R4 local PVM. -/
def SpectralMeasurePVMContinuousLocalPVMRangeInclusionTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        SpectralMeasurePVMContinuousLocalPVMRangeMember s x →
          SpectralMeasurePVMContinuousLocalPVMRangeMember t x

/-- Complement antitone range-inclusion target for the R4 local PVM. -/
def SpectralMeasurePVMContinuousLocalPVMComplementRangeInclusionTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        SpectralMeasurePVMContinuousLocalPVMRangeMember
          (spectralMeasurePVMSpectralSetSlotComplement t) x →
          SpectralMeasurePVMContinuousLocalPVMRangeMember
            (spectralMeasurePVMSpectralSetSlotComplement s) x

/-- Genuine Hilbert closed-range/subspace inclusion theorem remains open. -/
def SpectralMeasurePVMGenuineClosedRangeInclusionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The basic range target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_basic_range_target_ready :
    SpectralMeasurePVMContinuousLocalPVMBasicRangeTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_local_pvm_empty_range_zero,
    spectral_measure_pvm_continuous_local_pvm_whole_range_all,
    spectral_measure_pvm_continuous_local_pvm_empty_range_member_eq_zero⟩

/-- The range projection-fixed target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_projection_fixed_target_ready :
    SpectralMeasurePVMContinuousLocalPVMRangeProjectionFixedTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_local_pvm_range_member_projected,
    spectral_measure_pvm_continuous_local_pvm_projected_range_member⟩

/-- The order-induced range-inclusion target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_inclusion_target_ready :
    SpectralMeasurePVMContinuousLocalPVMRangeInclusionTarget := by
  exact spectral_measure_pvm_continuous_local_pvm_range_inclusion_of_subset

/-- The complement range-inclusion target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_complement_range_inclusion_target_ready :
    SpectralMeasurePVMContinuousLocalPVMComplementRangeInclusionTarget := by
  exact spectral_measure_pvm_continuous_local_pvm_complement_range_inclusion_of_subset

/-- Genuine closed-range inclusion remains explicitly open. -/
theorem spectral_measure_pvm_genuine_closed_range_inclusion_still_open_ready :
    SpectralMeasurePVMGenuineClosedRangeInclusionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM range core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMOrderCoreReady ∧
  SpectralMeasurePVMContinuousLocalPVMBasicRangeTarget ∧
  SpectralMeasurePVMContinuousLocalPVMRangeProjectionFixedTarget ∧
  SpectralMeasurePVMContinuousLocalPVMRangeInclusionTarget ∧
  SpectralMeasurePVMContinuousLocalPVMComplementRangeInclusionTarget ∧
  SpectralMeasurePVMGenuineClosedRangeInclusionStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM range core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_range_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_order_core_ready,
    spectral_measure_pvm_continuous_local_pvm_basic_range_target_ready,
    spectral_measure_pvm_continuous_local_pvm_range_projection_fixed_target_ready,
    spectral_measure_pvm_continuous_local_pvm_range_inclusion_target_ready,
    spectral_measure_pvm_continuous_local_pvm_complement_range_inclusion_target_ready,
    spectral_measure_pvm_genuine_closed_range_inclusion_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 continuous local PVM range core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMOrderBoundaryHeld ∧
  SpectralMeasurePVMGenuineClosedRangeInclusionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM range boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_range_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_range_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_order_boundary_held,
    spectral_measure_pvm_genuine_closed_range_inclusion_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
