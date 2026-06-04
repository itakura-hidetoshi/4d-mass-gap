import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedR4CompletionBoundaryCertificate

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R4-local continuous PVM-like object on the current two-index surface.

This is the strongest R4-local concrete object so far: it bundles the
empty/whole continuous projection family, the spectral-set-slot projection view,
and the zero/one/identity continuous functional-calculus table together with the
closed R4-local laws.

It is intentionally not named as a genuine mathlib spectral measure.  The full
Borel/PVM/spectral theorem construction remains an explicit open boundary. -/
structure SpectralMeasurePVMContinuousLocalPVM where
  projection : SpectralMeasurePVMConcreteIndex →
    MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
      MathlibAnalytic.ConcreteL2R1HilbertCarrier
  setProjection : SpectralMeasurePVMSpectralSetSlot →
    MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
      MathlibAnalytic.ConcreteL2R1HilbertCarrier
  functionalCalculus : SpectralMeasurePVMConcreteBoundedBorelFunction →
    MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
      MathlibAnalytic.ConcreteL2R1HilbertCarrier
  normalization : SpectralMeasurePVMContinuousSpectralMeasureCandidateNormalizationTarget
  projectionValuedness : SpectralMeasurePVMContinuousProjectionFamilyProjectionValuednessTarget
  orthogonality : SpectralMeasurePVMContinuousProjectionFamilyOrthogonalityTarget
  finiteAdditivity : SpectralMeasurePVMContinuousProjectionFamilyFiniteAdditivityTarget
  countableBranch : SpectralMeasurePVMContinuousProjectionCountableBranchTarget
  finitePartialAllEmpty : SpectralMeasurePVMContinuousProjectionFinitePartialAllEmptyTarget
  spectralSetCompatibility : SpectralMeasurePVMContinuousSpectralMeasureCandidateSetCompatibilityTarget
  spectralSetProjectionLaws : SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityCoreReady
  functionalCalculusTable : SpectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculusTableTarget
  indicatorRecovery : SpectralMeasurePVMContinuousSpectralMeasureCandidateIndicatorRecoveryTarget
  genuineSpectralMeasureStillOpen : SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen
  compactPlaquetteObservableNotConsumed : SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable
  atom3320DerivationDeferredToLaterStage :
    SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage
  positiveSpectralWeightDeferredToLaterStage :
    SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage
  noShellCollapsePreserved : SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Canonical R4-local continuous PVM-like object assembled from the concrete
candidate surface. -/
def spectralMeasurePVMContinuousLocalPVM :
    SpectralMeasurePVMContinuousLocalPVM :=
  { projection := spectralMeasurePVMContinuousSpectralMeasureCandidateProjection
    setProjection := spectralMeasurePVMContinuousSpectralMeasureCandidateSetProjection
    functionalCalculus := spectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculus
    normalization :=
      spectral_measure_pvm_continuous_spectral_measure_candidate_normalization_target_ready
    projectionValuedness :=
      spectral_measure_pvm_continuous_projection_family_projection_valuedness_target_ready
    orthogonality :=
      spectral_measure_pvm_continuous_projection_family_orthogonality_target_ready
    finiteAdditivity :=
      spectral_measure_pvm_continuous_projection_family_finite_additivity_target_ready
    countableBranch :=
      spectral_measure_pvm_continuous_projection_countable_branch_target_ready
    finitePartialAllEmpty :=
      spectral_measure_pvm_continuous_projection_finite_partial_all_empty_target_ready
    spectralSetCompatibility :=
      spectral_measure_pvm_continuous_spectral_measure_candidate_set_compatibility_target_ready
    spectralSetProjectionLaws :=
      spectral_measure_pvm_operator_valued_spectral_set_projection_compatibility_core_ready
    functionalCalculusTable :=
      spectral_measure_pvm_continuous_spectral_measure_candidate_functional_calculus_table_target_ready
    indicatorRecovery :=
      spectral_measure_pvm_continuous_spectral_measure_candidate_indicator_recovery_target_ready
    genuineSpectralMeasureStillOpen :=
      spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready
    compactPlaquetteObservableNotConsumed :=
      spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready
    atom3320DerivationDeferredToLaterStage :=
      spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready
    positiveSpectralWeightDeferredToLaterStage :=
      spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready
    noShellCollapsePreserved :=
      spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready }

/-- Direct normalization law exposed from the canonical R4-local PVM-like object. -/
theorem spectral_measure_pvm_continuous_local_pvm_empty_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousLocalPVM.projection SpectralMeasurePVMConcreteIndex.empty x = 0 := by
  rfl

/-- Direct whole-space law exposed from the canonical R4-local PVM-like object. -/
theorem spectral_measure_pvm_continuous_local_pvm_whole_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousLocalPVM.projection SpectralMeasurePVMConcreteIndex.whole x = x := by
  rfl

/-- Direct indicator-recovery law exposed from the canonical R4-local PVM-like object. -/
theorem spectral_measure_pvm_continuous_local_pvm_indicator_recovers_projection
    (i : SpectralMeasurePVMConcreteIndex)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousLocalPVM.functionalCalculus
        (spectralMeasurePVMConcreteIndicatorFunction i) x =
      spectralMeasurePVMContinuousLocalPVM.projection i x := by
  cases i <;> rfl

/-- Direct spectral-set compatibility law exposed from the canonical R4-local
PVM-like object. -/
theorem spectral_measure_pvm_continuous_local_pvm_set_projection_agrees
    (i : SpectralMeasurePVMConcreteIndex)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousLocalPVM.setProjection
        (spectralMeasurePVMSpectralSetSlotFromIndex i) x =
      spectralMeasurePVMContinuousLocalPVM.projection i x := by
  cases i <;> rfl

/-- Local PVM axiom packet readiness. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMAxiomPacketReady : Prop :=
  SpectralMeasurePVMOperatorValuedR4CompletionBoundaryCertificateReady ∧
  SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateCoreReady ∧
  SpectralMeasurePVMContinuousSpectralMeasureCandidateNormalizationTarget ∧
  SpectralMeasurePVMContinuousProjectionFamilyProjectionValuednessTarget ∧
  SpectralMeasurePVMContinuousProjectionFamilyOrthogonalityTarget ∧
  SpectralMeasurePVMContinuousProjectionFamilyFiniteAdditivityTarget ∧
  SpectralMeasurePVMContinuousProjectionCountableBranchTarget ∧
  SpectralMeasurePVMContinuousProjectionFinitePartialAllEmptyTarget ∧
  SpectralMeasurePVMContinuousSpectralMeasureCandidateSetCompatibilityTarget ∧
  SpectralMeasurePVMContinuousSpectralMeasureCandidateFunctionalCalculusTableTarget ∧
  SpectralMeasurePVMContinuousSpectralMeasureCandidateIndicatorRecoveryTarget ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4-local continuous PVM axiom packet is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_axiom_packet_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMAxiomPacketReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_r4_completion_boundary_certificate_ready,
    spectral_measure_pvm_operator_valued_continuous_spectral_measure_candidate_core_ready,
    spectral_measure_pvm_continuous_spectral_measure_candidate_normalization_target_ready,
    spectral_measure_pvm_continuous_projection_family_projection_valuedness_target_ready,
    spectral_measure_pvm_continuous_projection_family_orthogonality_target_ready,
    spectral_measure_pvm_continuous_projection_family_finite_additivity_target_ready,
    spectral_measure_pvm_continuous_projection_countable_branch_target_ready,
    spectral_measure_pvm_continuous_projection_finite_partial_all_empty_target_ready,
    spectral_measure_pvm_continuous_spectral_measure_candidate_set_compatibility_target_ready,
    spectral_measure_pvm_continuous_spectral_measure_candidate_functional_calculus_table_target_ready,
    spectral_measure_pvm_continuous_spectral_measure_candidate_indicator_recovery_target_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4-local PVM core readiness: a concrete continuous PVM-like object exists on
the two-index R4 surface, but the genuine spectral measure is still open. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMAxiomPacketReady ∧
  SpectralMeasurePVMOperatorValuedR4CompletionBoundaryCertificateReady ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4-local continuous PVM core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_axiom_packet_ready,
    spectral_measure_pvm_operator_valued_r4_completion_boundary_certificate_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4-local continuous PVM core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMCoreReady ∧
  SpectralMeasurePVMOperatorValuedR4CompletionBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4-local continuous PVM boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_core_ready,
    spectral_measure_pvm_operator_valued_r4_completion_boundary_held,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
