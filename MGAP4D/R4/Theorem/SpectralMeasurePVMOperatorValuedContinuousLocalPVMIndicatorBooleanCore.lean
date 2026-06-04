import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelUniquenessCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Convert the two symbolic spectral-set slots back to the two concrete indices. -/
def spectralMeasurePVMConcreteIndexFromSpectralSetSlot :
    SpectralMeasurePVMSpectralSetSlot → SpectralMeasurePVMConcreteIndex
  | SpectralMeasurePVMSpectralSetSlot.emptySet => SpectralMeasurePVMConcreteIndex.empty
  | SpectralMeasurePVMSpectralSetSlot.wholeSet => SpectralMeasurePVMConcreteIndex.whole

/-- Indicator function attached to a symbolic spectral-set slot. -/
def spectralMeasurePVMSpectralSetSlotIndicatorFunction
    (s : SpectralMeasurePVMSpectralSetSlot) :
    SpectralMeasurePVMConcreteBoundedBorelFunction :=
  spectralMeasurePVMConcreteIndicatorFunction
    (spectralMeasurePVMConcreteIndexFromSpectralSetSlot s)

/-- Boolean complement on the current three-function concrete surface.  Only
`zero` and `one` are used for indicator functions; `identity` is fixed as a
separate non-indicator constructor on this local surface. -/
def spectralMeasurePVMConcreteBoundedBorelFunctionComplement :
    SpectralMeasurePVMConcreteBoundedBorelFunction →
      SpectralMeasurePVMConcreteBoundedBorelFunction
  | SpectralMeasurePVMConcreteBoundedBorelFunction.zero =>
      SpectralMeasurePVMConcreteBoundedBorelFunction.one
  | SpectralMeasurePVMConcreteBoundedBorelFunction.one =>
      SpectralMeasurePVMConcreteBoundedBorelFunction.zero
  | SpectralMeasurePVMConcreteBoundedBorelFunction.identity =>
      SpectralMeasurePVMConcreteBoundedBorelFunction.identity

/-- Boolean union/join on the current indicator sub-surface. -/
def spectralMeasurePVMConcreteBoundedBorelFunctionUnion :
    SpectralMeasurePVMConcreteBoundedBorelFunction →
      SpectralMeasurePVMConcreteBoundedBorelFunction →
        SpectralMeasurePVMConcreteBoundedBorelFunction
  | SpectralMeasurePVMConcreteBoundedBorelFunction.zero,
      SpectralMeasurePVMConcreteBoundedBorelFunction.zero =>
        SpectralMeasurePVMConcreteBoundedBorelFunction.zero
  | _, _ => SpectralMeasurePVMConcreteBoundedBorelFunction.one

/-- Boolean intersection/meet on the current indicator sub-surface. -/
def spectralMeasurePVMConcreteBoundedBorelFunctionInter :
    SpectralMeasurePVMConcreteBoundedBorelFunction →
      SpectralMeasurePVMConcreteBoundedBorelFunction →
        SpectralMeasurePVMConcreteBoundedBorelFunction
  | SpectralMeasurePVMConcreteBoundedBorelFunction.one,
      SpectralMeasurePVMConcreteBoundedBorelFunction.one =>
        SpectralMeasurePVMConcreteBoundedBorelFunction.one
  | _, _ => SpectralMeasurePVMConcreteBoundedBorelFunction.zero

/-- Slot indicators respect complement. -/
theorem spectral_measure_pvm_spectral_set_slot_indicator_complement
    (s : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotIndicatorFunction
        (spectralMeasurePVMSpectralSetSlotComplement s) =
      spectralMeasurePVMConcreteBoundedBorelFunctionComplement
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) := by
  cases s <;> rfl

/-- Slot indicators respect union. -/
theorem spectral_measure_pvm_spectral_set_slot_indicator_union
    (s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotIndicatorFunction
        (spectralMeasurePVMSpectralSetSlotUnion s t) =
      spectralMeasurePVMConcreteBoundedBorelFunctionUnion
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) := by
  cases s <;> cases t <;> rfl

/-- Slot indicators respect intersection. -/
theorem spectral_measure_pvm_spectral_set_slot_indicator_inter
    (s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotIndicatorFunction
        (spectralMeasurePVMSpectralSetSlotInter s t) =
      spectralMeasurePVMConcreteBoundedBorelFunctionInter
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) := by
  cases s <;> cases t <;> rfl

/-- Continuous functional calculus of a slot indicator recovers the slot
projection. -/
theorem spectral_measure_pvm_continuous_functional_calculus_slot_indicator_projection
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection s x := by
  cases s <;> rfl

/-- Continuous functional calculus of a complement indicator recovers the
complement projection. -/
theorem spectral_measure_pvm_continuous_functional_calculus_slot_indicator_complement_projection
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotComplement s)) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement s) x := by
  cases s <;> rfl

/-- Continuous functional calculus of an intersection indicator is pointwise
projection composition. -/
theorem spectral_measure_pvm_continuous_functional_calculus_slot_indicator_inter_composition
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotInter s t)) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection s
        (spectralMeasurePVMSpectralSetSlotContinuousProjection t x) := by
  cases s <;> cases t <;> rfl

/-- Continuous functional calculus of a union/intersection pair satisfies the
finite inclusion-exclusion identity on the two-slot indicator surface. -/
theorem spectral_measure_pvm_continuous_functional_calculus_slot_indicator_union_inter_inclusion_exclusion
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction
            (spectralMeasurePVMSpectralSetSlotUnion s t)) x +
        spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction
            (spectralMeasurePVMSpectralSetSlotInter s t)) x =
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x +
        spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x := by
  cases s <;> cases t <;>
    simp [spectralMeasurePVMSpectralSetSlotIndicatorFunction,
      spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
      spectralMeasurePVMConcreteIndicatorFunction,
      spectralMeasurePVMContinuousFunctionalCalculus,
      spectralMeasurePVMSpectralSetSlotUnion,
      spectralMeasurePVMSpectralSetSlotInter]

/-- Continuous functional calculus of complementary indicators reconstructs the
vector. -/
theorem spectral_measure_pvm_continuous_functional_calculus_slot_indicator_complement_sum
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x +
        spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction
            (spectralMeasurePVMSpectralSetSlotComplement s)) x = x := by
  cases s <;>
    simp [spectralMeasurePVMSpectralSetSlotIndicatorFunction,
      spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
      spectralMeasurePVMConcreteIndicatorFunction,
      spectralMeasurePVMContinuousFunctionalCalculus,
      spectralMeasurePVMSpectralSetSlotComplement]

/-- Boolean compatibility target for slot indicators. -/
def SpectralMeasurePVMSpectralSetSlotIndicatorBooleanLawTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotIndicatorFunction
        (spectralMeasurePVMSpectralSetSlotComplement s) =
      spectralMeasurePVMConcreteBoundedBorelFunctionComplement
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotIndicatorFunction
        (spectralMeasurePVMSpectralSetSlotUnion s t) =
      spectralMeasurePVMConcreteBoundedBorelFunctionUnion
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotIndicatorFunction
        (spectralMeasurePVMSpectralSetSlotInter s t) =
      spectralMeasurePVMConcreteBoundedBorelFunctionInter
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction t))

/-- Continuous functional-calculus compatibility target for slot indicators. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSlotIndicatorTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x =
        spectralMeasurePVMSpectralSetSlotContinuousProjection s x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction
            (spectralMeasurePVMSpectralSetSlotComplement s)) x =
        spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s) x)

/-- Boolean projection identities through the continuous functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusIndicatorBooleanProjectionTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction
            (spectralMeasurePVMSpectralSetSlotInter s t)) x =
        spectralMeasurePVMSpectralSetSlotContinuousProjection s
          (spectralMeasurePVMSpectralSetSlotContinuousProjection t x)) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction
              (spectralMeasurePVMSpectralSetSlotUnion s t)) x +
          spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction
              (spectralMeasurePVMSpectralSetSlotInter s t)) x =
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x +
          spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x +
          spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction
              (spectralMeasurePVMSpectralSetSlotComplement s)) x = x)

/-- Genuine bounded Borel indicator Boolean calculus remains open. -/
def SpectralMeasurePVMGenuineIndicatorBooleanCalculusStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Slot indicator Boolean laws are ready. -/
theorem spectral_measure_pvm_spectral_set_slot_indicator_boolean_law_target_ready :
    SpectralMeasurePVMSpectralSetSlotIndicatorBooleanLawTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_indicator_complement,
    spectral_measure_pvm_spectral_set_slot_indicator_union,
    spectral_measure_pvm_spectral_set_slot_indicator_inter⟩

/-- Continuous functional-calculus slot-indicator target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_slot_indicator_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSlotIndicatorTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_slot_indicator_projection,
    spectral_measure_pvm_continuous_functional_calculus_slot_indicator_complement_projection⟩

/-- Boolean projection identities through continuous functional calculus are ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_indicator_boolean_projection_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusIndicatorBooleanProjectionTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_slot_indicator_inter_composition,
    spectral_measure_pvm_continuous_functional_calculus_slot_indicator_union_inter_inclusion_exclusion,
    spectral_measure_pvm_continuous_functional_calculus_slot_indicator_complement_sum⟩

/-- Genuine indicator Boolean calculus remains explicitly open. -/
theorem spectral_measure_pvm_genuine_indicator_boolean_calculus_still_open_ready :
    SpectralMeasurePVMGenuineIndicatorBooleanCalculusStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM indicator Boolean core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMIndicatorBooleanCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelUniquenessCoreReady ∧
  SpectralMeasurePVMSpectralSetSlotIndicatorBooleanLawTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSlotIndicatorTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusIndicatorBooleanProjectionTarget ∧
  SpectralMeasurePVMGenuineIndicatorBooleanCalculusStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM indicator Boolean core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_indicator_boolean_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMIndicatorBooleanCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_range_kernel_uniqueness_core_ready,
    spectral_measure_pvm_spectral_set_slot_indicator_boolean_law_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_slot_indicator_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_indicator_boolean_projection_target_ready,
    spectral_measure_pvm_genuine_indicator_boolean_calculus_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 indicator Boolean core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMIndicatorBooleanBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMIndicatorBooleanCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelUniquenessBoundaryHeld ∧
  SpectralMeasurePVMGenuineIndicatorBooleanCalculusStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 indicator Boolean boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_indicator_boolean_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMIndicatorBooleanBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_indicator_boolean_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_range_kernel_uniqueness_boundary_held,
    spectral_measure_pvm_genuine_indicator_boolean_calculus_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
