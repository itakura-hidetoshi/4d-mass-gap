import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMIndicatorBooleanCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The continuous functional calculus of a slot indicator is idempotent as an
action.  This is the R4-local two-slot surface, not a genuine bounded Borel
functional-calculus theorem. -/
theorem spectral_measure_pvm_continuous_functional_calculus_slot_indicator_idempotent_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x) =
      spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x := by
  cases s <;> rfl

/-- Composition of two slot-indicator functional-calculus actions is the
intersection indicator action. -/
theorem spectral_measure_pvm_continuous_functional_calculus_slot_indicator_composition_inter_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x) =
      spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotInter s t)) x := by
  cases s <;> cases t <;> rfl

/-- Slot-indicator functional-calculus actions commute on the R4 local surface. -/
theorem spectral_measure_pvm_continuous_functional_calculus_slot_indicator_commute_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x) =
      spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
        (spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x) := by
  cases s <;> cases t <;> rfl

/-- A slot-indicator action followed by its complement-indicator action is zero. -/
theorem spectral_measure_pvm_continuous_functional_calculus_slot_indicator_complement_zero_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction
            (spectralMeasurePVMSpectralSetSlotComplement s)) x) = 0 := by
  cases s <;> rfl

/-- A complement-indicator action followed by the original slot-indicator action
is zero. -/
theorem spectral_measure_pvm_continuous_functional_calculus_slot_indicator_complement_zero_reversed_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotComplement s))
        (spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x) = 0 := by
  cases s <;> rfl

/-- The empty-slot indicator acts as zero through the continuous functional
calculus. -/
theorem spectral_measure_pvm_continuous_functional_calculus_empty_indicator_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          SpectralMeasurePVMSpectralSetSlot.emptySet) x = 0 := by
  rfl

/-- The whole-slot indicator acts as identity through the continuous functional
calculus. -/
theorem spectral_measure_pvm_continuous_functional_calculus_whole_indicator_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          SpectralMeasurePVMSpectralSetSlot.wholeSet) x = x := by
  rfl

/-- Projection-algebra target for indicator functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusIndicatorProjectionAlgebraTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
          (spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x) =
        spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
          (spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x) =
        spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction
            (spectralMeasurePVMSpectralSetSlotInter s t)) x)

/-- Commutativity/orthogonality target for indicator functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusIndicatorCommutingOrthogonalTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
          (spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x) =
        spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
          (spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x)) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
          (spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction
              (spectralMeasurePVMSpectralSetSlotComplement s)) x) = 0) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction
            (spectralMeasurePVMSpectralSetSlotComplement s))
          (spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x) = 0)

/-- Empty/whole identity target for indicator functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusIndicatorNormalizationTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          SpectralMeasurePVMSpectralSetSlot.emptySet) x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          SpectralMeasurePVMSpectralSetSlot.wholeSet) x = x)

/-- Genuine multiplicative bounded-Borel functional calculus remains open. -/
def SpectralMeasurePVMGenuineMultiplicativeFunctionalCalculusStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Indicator projection-algebra target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_indicator_projection_algebra_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusIndicatorProjectionAlgebraTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_slot_indicator_idempotent_apply,
    spectral_measure_pvm_continuous_functional_calculus_slot_indicator_composition_inter_apply⟩

/-- Indicator commuting/orthogonal target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_indicator_commuting_orthogonal_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusIndicatorCommutingOrthogonalTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_slot_indicator_commute_apply,
    spectral_measure_pvm_continuous_functional_calculus_slot_indicator_complement_zero_apply,
    spectral_measure_pvm_continuous_functional_calculus_slot_indicator_complement_zero_reversed_apply⟩

/-- Indicator normalization target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_indicator_normalization_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusIndicatorNormalizationTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_empty_indicator_apply,
    spectral_measure_pvm_continuous_functional_calculus_whole_indicator_apply⟩

/-- Genuine multiplicative bounded-Borel functional calculus remains explicitly open. -/
theorem spectral_measure_pvm_genuine_multiplicative_functional_calculus_still_open_ready :
    SpectralMeasurePVMGenuineMultiplicativeFunctionalCalculusStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM functional-calculus projection algebra core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusProjectionAlgebraCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMIndicatorBooleanCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusIndicatorProjectionAlgebraTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusIndicatorCommutingOrthogonalTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusIndicatorNormalizationTarget ∧
  SpectralMeasurePVMGenuineMultiplicativeFunctionalCalculusStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM functional-calculus projection algebra core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_projection_algebra_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusProjectionAlgebraCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_indicator_boolean_core_ready,
    spectral_measure_pvm_continuous_functional_calculus_indicator_projection_algebra_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_indicator_commuting_orthogonal_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_indicator_normalization_target_ready,
    spectral_measure_pvm_genuine_multiplicative_functional_calculus_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 functional-calculus projection algebra core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusProjectionAlgebraBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusProjectionAlgebraCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMIndicatorBooleanBoundaryHeld ∧
  SpectralMeasurePVMGenuineMultiplicativeFunctionalCalculusStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 functional-calculus projection algebra boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_projection_algebra_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusProjectionAlgebraBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_projection_algebra_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_indicator_boolean_boundary_held,
    spectral_measure_pvm_genuine_multiplicative_functional_calculus_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
