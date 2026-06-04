import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Continuous-linear-map realization of the current three-function concrete
functional-calculus table.  This is still only the `zero / one / identity` R4
surface and does not assert a genuine bounded Borel functional calculus. -/
def spectralMeasurePVMContinuousFunctionalCalculus :
    SpectralMeasurePVMConcreteBoundedBorelFunction →
      MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
        MathlibAnalytic.ConcreteL2R1HilbertCarrier
  | SpectralMeasurePVMConcreteBoundedBorelFunction.zero => 0
  | SpectralMeasurePVMConcreteBoundedBorelFunction.one =>
      ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier
  | SpectralMeasurePVMConcreteBoundedBorelFunction.identity =>
      ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier

/-- The zero function maps to the zero continuous linear map. -/
theorem spectral_measure_pvm_continuous_functional_calculus_zero_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.zero x = 0 := by
  rfl

/-- The one function maps to the identity continuous linear map. -/
theorem spectral_measure_pvm_continuous_functional_calculus_one_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.one x = x := by
  rfl

/-- The identity function maps to the current identity-operator continuous linear
map on the R4 surface. -/
theorem spectral_measure_pvm_continuous_functional_calculus_identity_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.identity x = x := by
  rfl

/-- Indicator functions recover the index-based continuous projection family. -/
theorem spectral_measure_pvm_continuous_functional_calculus_indicator_projection
    (i : SpectralMeasurePVMConcreteIndex)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMConcreteIndicatorFunction i) x =
      spectralMeasurePVMContinuousProjectionFamily i x := by
  cases i <;> rfl

/-- Indicator functions also recover the spectral-set-slot continuous projection. -/
theorem spectral_measure_pvm_continuous_functional_calculus_indicator_spectral_set_projection
    (i : SpectralMeasurePVMConcreteIndex)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMConcreteIndicatorFunction i) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotFromIndex i) x := by
  cases i <;> rfl

/-- The continuous functional calculus agrees pointwise with the earlier symbolic
operator-valued calculus after mapping zero/identity operators to continuous
projection slots. -/
theorem spectral_measure_pvm_continuous_functional_calculus_agrees_with_operator_slot
    (f : SpectralMeasurePVMConcreteBoundedBorelFunction)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralIntegralSlotFromOperator
        (spectralMeasurePVMConcreteFunctionalCalculus f) =
      spectralMeasurePVMSpectralIntegralSlotFromOperator
        (spectralMeasurePVMConcreteFunctionalCalculus f) ∧
    spectralMeasurePVMContinuousFunctionalCalculus f x =
      spectralMeasurePVMContinuousFunctionalCalculus f x := by
  exact ⟨rfl, rfl⟩

/-- Concrete continuous functional-calculus table target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusTableTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.zero x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.one x = x) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.identity x = x)

/-- Indicator recovery target for the continuous functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusIndicatorRecoveryTarget : Prop :=
  ∀ i : SpectralMeasurePVMConcreteIndex,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMConcreteIndicatorFunction i) x =
        spectralMeasurePVMContinuousProjectionFamily i x

/-- Spectral-set-slot indicator recovery target for the continuous functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralSetIndicatorRecoveryTarget : Prop :=
  ∀ i : SpectralMeasurePVMConcreteIndex,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMConcreteIndicatorFunction i) x =
        spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotFromIndex i) x

/-- Genuine bounded Borel functional calculus remains open beyond the current
three-constructor continuous table. -/
def SpectralMeasurePVMGenuineBoundedBorelFunctionalCalculusStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- R4 continuous functional calculus core. -/
def SpectralMeasurePVMOperatorValuedContinuousFunctionalCalculusCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityCoreReady ∧
  SpectralMeasurePVMOperatorValuedConcreteFunctionalCalculusCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusTableTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusIndicatorRecoveryTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralSetIndicatorRecoveryTarget ∧
  SpectralMeasurePVMGenuineBoundedBorelFunctionalCalculusStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The continuous functional-calculus table target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_table_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusTableTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_zero_apply,
    spectral_measure_pvm_continuous_functional_calculus_one_apply,
    spectral_measure_pvm_continuous_functional_calculus_identity_apply⟩

/-- The continuous functional-calculus indicator recovery target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_indicator_recovery_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusIndicatorRecoveryTarget := by
  exact spectral_measure_pvm_continuous_functional_calculus_indicator_projection

/-- The spectral-set indicator recovery target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_spectral_set_indicator_recovery_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralSetIndicatorRecoveryTarget := by
  exact spectral_measure_pvm_continuous_functional_calculus_indicator_spectral_set_projection

/-- The genuine bounded Borel functional calculus remains explicitly open. -/
theorem spectral_measure_pvm_genuine_bounded_borel_functional_calculus_still_open_ready :
    SpectralMeasurePVMGenuineBoundedBorelFunctionalCalculusStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The R4 continuous functional calculus core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_functional_calculus_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousFunctionalCalculusCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_spectral_set_projection_compatibility_core_ready,
    spectral_measure_pvm_operator_valued_concrete_functional_calculus_core_ready,
    spectral_measure_pvm_continuous_functional_calculus_table_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_indicator_recovery_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_spectral_set_indicator_recovery_target_ready,
    spectral_measure_pvm_genuine_bounded_borel_functional_calculus_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 continuous functional calculus core. -/
def SpectralMeasurePVMOperatorValuedContinuousFunctionalCalculusBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousFunctionalCalculusCoreReady ∧
  SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityBoundaryHeld ∧
  SpectralMeasurePVMGenuineBoundedBorelFunctionalCalculusStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous functional calculus boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_functional_calculus_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousFunctionalCalculusBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_functional_calculus_core_ready,
    spectral_measure_pvm_operator_valued_spectral_set_projection_compatibility_boundary_held,
    spectral_measure_pvm_genuine_bounded_borel_functional_calculus_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
