import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMDisjointFunctionalCalculusAdditivityCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- If `s ⊆ t`, then `FC(χ_t) FC(χ_s) = FC(χ_s)` pointwise on the R4 local surface. -/
theorem spectral_measure_pvm_continuous_functional_calculus_subset_right_absorption_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
        (spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x) =
      spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- If `s ⊆ t`, then `FC(χ_s) FC(χ_t) = FC(χ_s)` pointwise on the R4 local surface. -/
theorem spectral_measure_pvm_continuous_functional_calculus_subset_left_absorption_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x) =
      spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- If `s ⊆ t`, then the union indicator functional calculus is the `t` indicator action. -/
theorem spectral_measure_pvm_continuous_functional_calculus_subset_union_right_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotUnion s t)) x =
      spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- If `s ⊆ t`, then the intersection indicator functional calculus is the `s` indicator action. -/
theorem spectral_measure_pvm_continuous_functional_calculus_subset_inter_left_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotInter s t)) x =
      spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- If `s ⊆ t`, then complement indicators absorb in the reversed order. -/
theorem spectral_measure_pvm_continuous_functional_calculus_subset_complement_absorption_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotComplement s))
        (spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction
            (spectralMeasurePVMSpectralSetSlotComplement t)) x) =
      spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotComplement t)) x := by
  exact spectral_measure_pvm_continuous_functional_calculus_subset_right_absorption_apply
    (spectralMeasurePVMSpectralSetSlotComplement t)
    (spectralMeasurePVMSpectralSetSlotComplement s)
    (spectral_measure_pvm_spectral_set_slot_subset_complement_antitone s t hst)
    x

/-- Order absorption target through indicator functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusOrderAbsorptionTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
            (spectralMeasurePVMContinuousFunctionalCalculus
              (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x) =
          spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
            (spectralMeasurePVMContinuousFunctionalCalculus
              (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x) =
          spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x)

/-- Order/lattice compatibility target through indicator functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusOrderLatticeTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction
              (spectralMeasurePVMSpectralSetSlotUnion s t)) x =
          spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction t) x) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction
              (spectralMeasurePVMSpectralSetSlotInter s t)) x =
          spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x)

/-- Complement order absorption target through indicator functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusComplementOrderAbsorptionTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction
              (spectralMeasurePVMSpectralSetSlotComplement s))
            (spectralMeasurePVMContinuousFunctionalCalculus
              (spectralMeasurePVMSpectralSetSlotIndicatorFunction
                (spectralMeasurePVMSpectralSetSlotComplement t)) x) =
          spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction
              (spectralMeasurePVMSpectralSetSlotComplement t)) x

/-- Genuine monotone bounded-Borel functional calculus remains open. -/
def SpectralMeasurePVMGenuineMonotoneFunctionalCalculusStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The order absorption target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_order_absorption_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusOrderAbsorptionTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_subset_right_absorption_apply,
    spectral_measure_pvm_continuous_functional_calculus_subset_left_absorption_apply⟩

/-- The order/lattice target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_order_lattice_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusOrderLatticeTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_subset_union_right_apply,
    spectral_measure_pvm_continuous_functional_calculus_subset_inter_left_apply⟩

/-- The complement order absorption target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_complement_order_absorption_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusComplementOrderAbsorptionTarget := by
  exact spectral_measure_pvm_continuous_functional_calculus_subset_complement_absorption_apply

/-- Genuine monotone bounded-Borel functional calculus remains explicitly open. -/
theorem spectral_measure_pvm_genuine_monotone_functional_calculus_still_open_ready :
    SpectralMeasurePVMGenuineMonotoneFunctionalCalculusStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 functional-calculus order absorption core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusOrderCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMDisjointFunctionalCalculusAdditivityCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusOrderAbsorptionTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusOrderLatticeTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusComplementOrderAbsorptionTarget ∧
  SpectralMeasurePVMGenuineMonotoneFunctionalCalculusStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 functional-calculus order absorption core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_order_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusOrderCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_disjoint_functional_calculus_additivity_core_ready,
    spectral_measure_pvm_continuous_functional_calculus_order_absorption_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_order_lattice_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_complement_order_absorption_target_ready,
    spectral_measure_pvm_genuine_monotone_functional_calculus_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 functional-calculus order absorption core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusOrderBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusOrderCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMDisjointFunctionalCalculusAdditivityBoundaryHeld ∧
  SpectralMeasurePVMGenuineMonotoneFunctionalCalculusStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 functional-calculus order absorption boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_order_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusOrderBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_order_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_disjoint_functional_calculus_additivity_boundary_held,
    spectral_measure_pvm_genuine_monotone_functional_calculus_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
