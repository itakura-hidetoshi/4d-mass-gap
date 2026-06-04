import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousProjectionCountableBranchCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Continuous projection attached directly to the symbolic spectral-set slots.
This is the two-slot empty/whole surface, not a genuine Borel PVM. -/
def spectralMeasurePVMSpectralSetSlotContinuousProjection :
    SpectralMeasurePVMSpectralSetSlot →
      MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
        MathlibAnalytic.ConcreteL2R1HilbertCarrier
  | SpectralMeasurePVMSpectralSetSlot.emptySet => 0
  | SpectralMeasurePVMSpectralSetSlot.wholeSet =>
      ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier

/-- Empty spectral-set slot acts as the zero continuous projection. -/
theorem spectral_measure_pvm_spectral_set_slot_continuous_projection_empty_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        SpectralMeasurePVMSpectralSetSlot.emptySet x = 0 := by
  rfl

/-- Whole spectral-set slot acts as the identity continuous projection. -/
theorem spectral_measure_pvm_spectral_set_slot_continuous_projection_whole_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        SpectralMeasurePVMSpectralSetSlot.wholeSet x = x := by
  rfl

/-- The spectral-set-slot projection agrees pointwise with the index-based
continuous projection family. -/
theorem spectral_measure_pvm_spectral_set_slot_continuous_projection_from_index_agrees
    (i : SpectralMeasurePVMConcreteIndex)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotFromIndex i) x =
      spectralMeasurePVMContinuousProjectionFamily i x := by
  cases i <;> rfl

/-- Disjointness relation on the two symbolic spectral-set slots.  Only the pair
`wholeSet, wholeSet` is excluded. -/
def SpectralMeasurePVMSpectralSetSlotDisjoint :
    SpectralMeasurePVMSpectralSetSlot → SpectralMeasurePVMSpectralSetSlot → Prop
  | SpectralMeasurePVMSpectralSetSlot.wholeSet,
      SpectralMeasurePVMSpectralSetSlot.wholeSet => False
  | _, _ => True

/-- Disjoint spectral-set-slot projections annihilate pointwise. -/
theorem spectral_measure_pvm_spectral_set_slot_continuous_projection_disjoint_pointwise_zero
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection s
        (spectralMeasurePVMSpectralSetSlotContinuousProjection t x) = 0 := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- Finite additivity of the two symbolic spectral-set-slot projections, stated
pointwise for disjoint slots. -/
theorem spectral_measure_pvm_spectral_set_slot_continuous_projection_binary_additivity_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotUnion s t) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
        spectralMeasurePVMSpectralSetSlotContinuousProjection t x := by
  cases s <;> cases t <;>
    simp [spectralMeasurePVMSpectralSetSlotContinuousProjection,
      spectralMeasurePVMSpectralSetSlotUnion]
  exact False.elim hst

/-- Complement swaps the two symbolic spectral-set-slot projections. -/
def SpectralMeasurePVMSpectralSetSlotComplementProjectionTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement SpectralMeasurePVMSpectralSetSlot.emptySet) x = x) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement SpectralMeasurePVMSpectralSetSlot.wholeSet) x = 0)

/-- Spectral-set-slot projection normalization target. -/
def SpectralMeasurePVMSpectralSetSlotProjectionNormalizationTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMSpectralSetSlotContinuousProjection SpectralMeasurePVMSpectralSetSlot.emptySet x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMSpectralSetSlotContinuousProjection SpectralMeasurePVMSpectralSetSlot.wholeSet x = x)

/-- Compatibility target between symbolic spectral-set slots and concrete indices. -/
def SpectralMeasurePVMSpectralSetSlotProjectionIndexCompatibilityTarget : Prop :=
  ∀ i : SpectralMeasurePVMConcreteIndex,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotFromIndex i) x =
        spectralMeasurePVMContinuousProjectionFamily i x

/-- Orthogonality target for disjoint symbolic spectral-set-slot projections. -/
def SpectralMeasurePVMSpectralSetSlotProjectionOrthogonalityTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMSpectralSetSlotContinuousProjection s
            (spectralMeasurePVMSpectralSetSlotContinuousProjection t x) = 0

/-- Finite additivity target for disjoint symbolic spectral-set-slot projections. -/
def SpectralMeasurePVMSpectralSetSlotProjectionFiniteAdditivityTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMSpectralSetSlotContinuousProjection
            (spectralMeasurePVMSpectralSetSlotUnion s t) x =
          spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
            spectralMeasurePVMSpectralSetSlotContinuousProjection t x

/-- Genuine Borel-set-to-projection compatibility remains open. -/
def SpectralMeasurePVMGenuineBorelProjectionCompatibilityStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- R4 spectral-set-slot projection compatibility core. -/
def SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousProjectionCountableBranchCoreReady ∧
  SpectralMeasurePVMSpectralSetSlotAlgebraLawTarget ∧
  SpectralMeasurePVMSpectralSetSlotProjectionNormalizationTarget ∧
  SpectralMeasurePVMSpectralSetSlotProjectionIndexCompatibilityTarget ∧
  SpectralMeasurePVMSpectralSetSlotProjectionOrthogonalityTarget ∧
  SpectralMeasurePVMSpectralSetSlotProjectionFiniteAdditivityTarget ∧
  SpectralMeasurePVMSpectralSetSlotComplementProjectionTarget ∧
  SpectralMeasurePVMGenuineBorelProjectionCompatibilityStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The complement projection target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_complement_projection_target_ready :
    SpectralMeasurePVMSpectralSetSlotComplementProjectionTarget := by
  exact ⟨fun x => rfl, fun x => rfl⟩

/-- The spectral-set-slot projection normalization target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_normalization_target_ready :
    SpectralMeasurePVMSpectralSetSlotProjectionNormalizationTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_continuous_projection_empty_apply,
    spectral_measure_pvm_spectral_set_slot_continuous_projection_whole_apply⟩

/-- The spectral-set-slot/index projection compatibility target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_index_compatibility_target_ready :
    SpectralMeasurePVMSpectralSetSlotProjectionIndexCompatibilityTarget := by
  exact spectral_measure_pvm_spectral_set_slot_continuous_projection_from_index_agrees

/-- The spectral-set-slot projection orthogonality target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_orthogonality_target_ready :
    SpectralMeasurePVMSpectralSetSlotProjectionOrthogonalityTarget := by
  exact spectral_measure_pvm_spectral_set_slot_continuous_projection_disjoint_pointwise_zero

/-- The spectral-set-slot projection finite-additivity target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_finite_additivity_target_ready :
    SpectralMeasurePVMSpectralSetSlotProjectionFiniteAdditivityTarget := by
  exact spectral_measure_pvm_spectral_set_slot_continuous_projection_binary_additivity_apply

/-- Genuine Borel projection compatibility remains explicitly open. -/
theorem spectral_measure_pvm_genuine_borel_projection_compatibility_still_open_ready :
    SpectralMeasurePVMGenuineBorelProjectionCompatibilityStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The R4 spectral-set projection compatibility core is ready. -/
theorem spectral_measure_pvm_operator_valued_spectral_set_projection_compatibility_core_ready :
    SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_projection_countable_branch_core_ready,
    spectral_measure_pvm_spectral_set_slot_algebra_law_target_ready,
    spectral_measure_pvm_spectral_set_slot_projection_normalization_target_ready,
    spectral_measure_pvm_spectral_set_slot_projection_index_compatibility_target_ready,
    spectral_measure_pvm_spectral_set_slot_projection_orthogonality_target_ready,
    spectral_measure_pvm_spectral_set_slot_projection_finite_additivity_target_ready,
    spectral_measure_pvm_spectral_set_slot_complement_projection_target_ready,
    spectral_measure_pvm_genuine_borel_projection_compatibility_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 spectral-set projection compatibility core. -/
def SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousProjectionCountableBranchBoundaryHeld ∧
  SpectralMeasurePVMGenuineBorelProjectionCompatibilityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-set projection compatibility boundary is held. -/
theorem spectral_measure_pvm_operator_valued_spectral_set_projection_compatibility_boundary_held :
    SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_spectral_set_projection_compatibility_core_ready,
    spectral_measure_pvm_operator_valued_continuous_projection_countable_branch_boundary_held,
    spectral_measure_pvm_genuine_borel_projection_compatibility_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
