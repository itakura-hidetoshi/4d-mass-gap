import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousFunctionalCalculusCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R4 continuous-operator candidate projection family.  This is the assembled
continuous-linear-map version of the current empty/whole PVM surface. -/
def spectralMeasurePVMContinuousSpectralMeasureCandidateProjection
    (i : SpectralMeasurePVMConcreteIndex) :
    MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
      MathlibAnalytic.ConcreteL2R1HilbertCarrier :=
  spectralMeasurePVMContinuousProjectionFamily i

/-- R4 continuous-operator candidate indexed by symbolic spectral-set slots. -/
def spectralMeasurePVMContinuousSpectralMeasureCandidateSetProjection
    (s : SpectralMeasurePVMSpectralSetSlot) :
    MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
      MathlibAnalytic.ConcreteL2R1HilbertCarrier :=
  spectralMeasurePVMSpectralSetSlotContinuousProjection s

/-- R4 continuous-operator candidate functional-calculus table. -/
def spectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculus
    (f : SpectralMeasurePVMConcreteBoundedBorelFunction) :
    MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
      MathlibAnalytic.ConcreteL2R1HilbertCarrier :=
  spectralMeasurePVMContinuousFunctionalCalculus f

/-- The candidate sends the empty index to the zero continuous projection. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_empty_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousSpectralMeasureCandidateProjection
        SpectralMeasurePVMConcreteIndex.empty x = 0 := by
  rfl

/-- The candidate sends the whole index to the identity continuous projection. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_whole_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousSpectralMeasureCandidateProjection
        SpectralMeasurePVMConcreteIndex.whole x = x := by
  rfl

/-- The candidate's index projection agrees with its spectral-set-slot projection. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_set_projection_agrees
    (i : SpectralMeasurePVMConcreteIndex)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousSpectralMeasureCandidateSetProjection
        (spectralMeasurePVMSpectralSetSlotFromIndex i) x =
      spectralMeasurePVMContinuousSpectralMeasureCandidateProjection i x := by
  cases i <;> rfl

/-- Indicator functions recover the candidate projection. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_indicator_recovers_projection
    (i : SpectralMeasurePVMConcreteIndex)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculus
        (spectralMeasurePVMConcreteIndicatorFunction i) x =
      spectralMeasurePVMContinuousSpectralMeasureCandidateProjection i x := by
  cases i <;> rfl

/-- The candidate's zero function acts as zero. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_zero_function_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.zero x = 0 := by
  rfl

/-- The candidate's one function acts as identity. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_one_function_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.one x = x := by
  rfl

/-- The candidate's identity function acts as identity on the current R4 surface. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_identity_function_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.identity x = x := by
  rfl

/-- Normalization target for the assembled continuous spectral-measure candidate. -/
def SpectralMeasurePVMContinuousSpectralMeasureCandidateNormalizationTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousSpectralMeasureCandidateProjection
        SpectralMeasurePVMConcreteIndex.empty x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousSpectralMeasureCandidateProjection
        SpectralMeasurePVMConcreteIndex.whole x = x)

/-- Spectral-set-slot compatibility target for the assembled candidate. -/
def SpectralMeasurePVMContinuousSpectralMeasureCandidateSetCompatibilityTarget : Prop :=
  ∀ i : SpectralMeasurePVMConcreteIndex,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousSpectralMeasureCandidateSetProjection
          (spectralMeasurePVMSpectralSetSlotFromIndex i) x =
        spectralMeasurePVMContinuousSpectralMeasureCandidateProjection i x

/-- Functional-calculus table target for the assembled candidate. -/
def SpectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculusTableTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.zero x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.one x = x) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculus
        SpectralMeasurePVMConcreteBoundedBorelFunction.identity x = x)

/-- Indicator recovery target for the assembled candidate. -/
def SpectralMeasurePVMContinuousSpectralMeasureCandidateIndicatorRecoveryTarget : Prop :=
  ∀ i : SpectralMeasurePVMConcreteIndex,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculus
          (spectralMeasurePVMConcreteIndicatorFunction i) x =
        spectralMeasurePVMContinuousSpectralMeasureCandidateProjection i x

/-- Countable branch handoff target for the assembled candidate. -/
def SpectralMeasurePVMContinuousSpectralMeasureCandidateCountableBranchHandoffTarget : Prop :=
  SpectralMeasurePVMContinuousProjectionCountableBranchTarget ∧
  SpectralMeasurePVMContinuousProjectionGenuineCountableAdditivityStillOpen

/-- Genuine spectral measure construction remains open beyond the assembled R4
continuous candidate. -/
def SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- R4 assembled continuous spectral-measure candidate core. -/
def SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousFunctionalCalculusCoreReady ∧
  SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousProjectionCountableBranchCoreReady ∧
  SpectralMeasurePVMContinuousSpectralMeasureCandidateNormalizationTarget ∧
  SpectralMeasurePVMContinuousSpectralMeasureCandidateSetCompatibilityTarget ∧
  SpectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculusTableTarget ∧
  SpectralMeasurePVMContinuousSpectralMeasureCandidateIndicatorRecoveryTarget ∧
  SpectralMeasurePVMContinuousSpectralMeasureCandidateCountableBranchHandoffTarget ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The candidate normalization target is ready. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_normalization_target_ready :
    SpectralMeasurePVMContinuousSpectralMeasureCandidateNormalizationTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_spectral_measure_candidate_empty_apply,
    spectral_measure_pvm_continuous_spectral_measure_candidate_whole_apply⟩

/-- The candidate spectral-set compatibility target is ready. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_set_compatibility_target_ready :
    SpectralMeasurePVMContinuousSpectralMeasureCandidateSetCompatibilityTarget := by
  exact spectral_measure_pvm_continuous_spectral_measure_candidate_set_projection_agrees

/-- The candidate functional-calculus table target is ready. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_functional_calculus_table_target_ready :
    SpectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculusTableTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_spectral_measure_candidate_zero_function_apply,
    spectral_measure_pvm_continuous_spectral_measure_candidate_one_function_apply,
    spectral_measure_pvm_continuous_spectral_measure_candidate_identity_function_apply⟩

/-- The candidate indicator recovery target is ready. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_indicator_recovery_target_ready :
    SpectralMeasurePVMContinuousSpectralMeasureCandidateIndicatorRecoveryTarget := by
  exact spectral_measure_pvm_continuous_spectral_measure_candidate_indicator_recovers_projection

/-- The candidate countable-branch handoff target is ready. -/
theorem spectral_measure_pvm_continuous_spectral_measure_candidate_countable_branch_handoff_target_ready :
    SpectralMeasurePVMContinuousSpectralMeasureCandidateCountableBranchHandoffTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_projection_countable_branch_target_ready,
    spectral_measure_pvm_continuous_projection_genuine_countable_additivity_still_open_ready⟩

/-- The genuine spectral-measure construction remains explicitly open. -/
theorem spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready :
    SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The assembled R4 continuous spectral-measure candidate core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_spectral_measure_candidate_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_functional_calculus_core_ready,
    spectral_measure_pvm_operator_valued_spectral_set_projection_compatibility_core_ready,
    spectral_measure_pvm_operator_valued_continuous_projection_countable_branch_core_ready,
    spectral_measure_pvm_continuous_spectral_measure_candidate_normalization_target_ready,
    spectral_measure_pvm_continuous_spectral_measure_candidate_set_compatibility_target_ready,
    spectral_measure_pvm_continuous_spectral_measure_candidate_functional_calculus_table_target_ready,
    spectral_measure_pvm_continuous_spectral_measure_candidate_indicator_recovery_target_ready,
    spectral_measure_pvm_continuous_spectral_measure_candidate_countable_branch_handoff_target_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the assembled R4 continuous spectral-measure candidate. -/
def SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousFunctionalCalculusBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The assembled R4 continuous spectral-measure candidate boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_spectral_measure_candidate_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_spectral_measure_candidate_core_ready,
    spectral_measure_pvm_operator_valued_continuous_functional_calculus_boundary_held,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
