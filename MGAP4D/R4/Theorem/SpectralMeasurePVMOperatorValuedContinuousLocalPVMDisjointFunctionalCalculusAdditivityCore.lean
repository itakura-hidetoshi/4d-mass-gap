import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusProjectionAlgebraCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Disjoint symbolic spectral-set slots have empty intersection on the R4
two-slot surface. -/
theorem spectral_measure_pvm_spectral_set_slot_disjoint_inter_empty
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t) :
    spectralMeasurePVMSpectralSetSlotInter s t =
      SpectralMeasurePVMSpectralSetSlot.emptySet := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- For disjoint slots, the functional calculus of the intersection indicator is
zero. -/
theorem spectral_measure_pvm_continuous_functional_calculus_disjoint_inter_zero_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotInter s t)) x = 0 := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- For disjoint slots, the functional calculus of the union indicator is the
sum of the two indicator functional-calculus actions. -/
theorem spectral_measure_pvm_continuous_functional_calculus_disjoint_union_add_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotUnion s t)) x =
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x +
        spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x := by
  cases s <;> cases t <;>
    simp [SpectralMeasurePVMSpectralSetSlotDisjoint,
      spectralMeasurePVMSpectralSetSlotIndicatorFunction,
      spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
      spectralMeasurePVMConcreteIndicatorFunction,
      spectralMeasurePVMContinuousFunctionalCalculus,
      spectralMeasurePVMSpectralSetSlotUnion] at *

/-- For disjoint slots, the two indicator functional-calculus actions compose to
zero. -/
theorem spectral_measure_pvm_continuous_functional_calculus_disjoint_composition_zero_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x) = 0 := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- The reversed disjoint composition is zero as well. -/
theorem spectral_measure_pvm_continuous_functional_calculus_disjoint_reversed_composition_zero_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
        (spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x) = 0 := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- Disjointness/intersection target for indicator functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusDisjointInterTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      spectralMeasurePVMSpectralSetSlotInter s t =
        SpectralMeasurePVMSpectralSetSlot.emptySet) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction
              (spectralMeasurePVMSpectralSetSlotInter s t)) x = 0)

/-- Disjoint finite additivity target through indicator functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusDisjointFiniteAdditivityTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction
              (spectralMeasurePVMSpectralSetSlotUnion s t)) x =
          spectralMeasurePVMContinuousFunctionalCalculus
              (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x +
            spectralMeasurePVMContinuousFunctionalCalculus
              (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x

/-- Disjoint orthogonality target through indicator functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusDisjointOrthogonalityTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
            (spectralMeasurePVMContinuousFunctionalCalculus
              (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x) = 0) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
            (spectralMeasurePVMContinuousFunctionalCalculus
              (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x) = 0)

/-- Genuine finite additivity through bounded-Borel functional calculus remains
open beyond the R4 local two-slot surface. -/
def SpectralMeasurePVMGenuineFunctionalCalculusFiniteAdditivityStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The disjoint-intersection target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_disjoint_inter_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusDisjointInterTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_disjoint_inter_empty,
    spectral_measure_pvm_continuous_functional_calculus_disjoint_inter_zero_apply⟩

/-- The disjoint finite-additivity target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_disjoint_finite_additivity_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusDisjointFiniteAdditivityTarget := by
  exact spectral_measure_pvm_continuous_functional_calculus_disjoint_union_add_apply

/-- The disjoint orthogonality target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_disjoint_orthogonality_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusDisjointOrthogonalityTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_disjoint_composition_zero_apply,
    spectral_measure_pvm_continuous_functional_calculus_disjoint_reversed_composition_zero_apply⟩

/-- Genuine finite additivity through bounded-Borel functional calculus remains
explicitly open. -/
theorem spectral_measure_pvm_genuine_functional_calculus_finite_additivity_still_open_ready :
    SpectralMeasurePVMGenuineFunctionalCalculusFiniteAdditivityStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 disjoint functional-calculus finite-additivity core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMDisjointFunctionalCalculusAdditivityCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusProjectionAlgebraCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusDisjointInterTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusDisjointFiniteAdditivityTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusDisjointOrthogonalityTarget ∧
  SpectralMeasurePVMGenuineFunctionalCalculusFiniteAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 disjoint functional-calculus finite-additivity core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_disjoint_functional_calculus_additivity_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMDisjointFunctionalCalculusAdditivityCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_projection_algebra_core_ready,
    spectral_measure_pvm_continuous_functional_calculus_disjoint_inter_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_disjoint_finite_additivity_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_disjoint_orthogonality_target_ready,
    spectral_measure_pvm_genuine_functional_calculus_finite_additivity_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 disjoint functional-calculus finite-additivity core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMDisjointFunctionalCalculusAdditivityBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMDisjointFunctionalCalculusAdditivityCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusProjectionAlgebraBoundaryHeld ∧
  SpectralMeasurePVMGenuineFunctionalCalculusFiniteAdditivityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 disjoint functional-calculus finite-additivity boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_disjoint_functional_calculus_additivity_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMDisjointFunctionalCalculusAdditivityBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_disjoint_functional_calculus_additivity_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_projection_algebra_boundary_held,
    spectral_measure_pvm_genuine_functional_calculus_finite_additivity_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
