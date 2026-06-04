import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Final R4 completion-boundary certificate.

This is the intended R4 stopping certificate: the concrete/continuous
spectral-measure candidate has been assembled from the R4-local ingredients, but
no later compact plaquette observable, `33/20` atom derivation, or positive
spectral-weight theorem is consumed.  The genuine spectral-measure/PVM theorem is
still explicitly open. -/
structure SpectralMeasurePVMOperatorValuedR4CompletionBoundaryCertificate where
  continuousCandidateCoreReady :
    SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateCoreReady
  continuousCandidateBoundaryHeld :
    SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateBoundaryHeld
  continuousFunctionalCalculusBoundaryHeld :
    SpectralMeasurePVMOperatorValuedContinuousFunctionalCalculusBoundaryHeld
  spectralSetProjectionCompatibilityBoundaryHeld :
    SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityBoundaryHeld
  continuousProjectionCountableBranchBoundaryHeld :
    SpectralMeasurePVMOperatorValuedContinuousProjectionCountableBranchBoundaryHeld
  continuousProjectionFamilyBoundaryHeld :
    SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyBoundaryHeld
  pvmConstructionLiftSpineReady :
    SpectralMeasurePVMOperatorValuedPVMConstructionLiftSpineReady
  originalR4BoundaryHeld :
    SpectralMeasurePVMOperatorValuedR4BoundaryHeld
  genuineSpectralMeasureConstructionStillOpen :
    SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen
  genuineBoundedBorelFunctionalCalculusStillOpen :
    SpectralMeasurePVMGenuineBoundedBorelFunctionalCalculusStillOpen
  genuineBorelProjectionCompatibilityStillOpen :
    SpectralMeasurePVMGenuineBorelProjectionCompatibilityStillOpen
  genuineCountableAdditivityStillOpen :
    SpectralMeasurePVMContinuousProjectionGenuineCountableAdditivityStillOpen
  compactPlaquetteObservableNotConsumed :
    SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable
  atom3320DerivationDeferredToLaterStage :
    SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage
  positiveSpectralWeightDeferredToLaterStage :
    SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage
  noShellCollapsePreserved :
    SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Canonical R4 completion-boundary certificate packet. -/
def spectralMeasurePVMOperatorValuedR4CompletionBoundaryCertificate :
    SpectralMeasurePVMOperatorValuedR4CompletionBoundaryCertificate :=
  { continuousCandidateCoreReady :=
      spectral_measure_pvm_operator_valued_continuous_spectral_measure_candidate_core_ready
    continuousCandidateBoundaryHeld :=
      spectral_measure_pvm_operator_valued_continuous_spectral_measure_candidate_boundary_held
    continuousFunctionalCalculusBoundaryHeld :=
      spectral_measure_pvm_operator_valued_continuous_functional_calculus_boundary_held
    spectralSetProjectionCompatibilityBoundaryHeld :=
      spectral_measure_pvm_operator_valued_spectral_set_projection_compatibility_boundary_held
    continuousProjectionCountableBranchBoundaryHeld :=
      spectral_measure_pvm_operator_valued_continuous_projection_countable_branch_boundary_held
    continuousProjectionFamilyBoundaryHeld :=
      spectral_measure_pvm_operator_valued_continuous_projection_family_boundary_held
    pvmConstructionLiftSpineReady :=
      spectral_measure_pvm_operator_valued_pvm_construction_lift_spine_ready
    originalR4BoundaryHeld :=
      spectral_measure_pvm_operator_valued_r4_boundary_held
    genuineSpectralMeasureConstructionStillOpen :=
      spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready
    genuineBoundedBorelFunctionalCalculusStillOpen :=
      spectral_measure_pvm_genuine_bounded_borel_functional_calculus_still_open_ready
    genuineBorelProjectionCompatibilityStillOpen :=
      spectral_measure_pvm_genuine_borel_projection_compatibility_still_open_ready
    genuineCountableAdditivityStillOpen :=
      spectral_measure_pvm_continuous_projection_genuine_countable_additivity_still_open_ready
    compactPlaquetteObservableNotConsumed :=
      spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready
    atom3320DerivationDeferredToLaterStage :=
      spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready
    positiveSpectralWeightDeferredToLaterStage :=
      spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready
    noShellCollapsePreserved :=
      spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready }

/-- Readiness predicate for the final R4 completion-boundary certificate. -/
def SpectralMeasurePVMOperatorValuedR4CompletionBoundaryCertificateReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateBoundaryHeld ∧
  SpectralMeasurePVMOperatorValuedContinuousFunctionalCalculusBoundaryHeld ∧
  SpectralMeasurePVMOperatorValuedSpectralSetProjectionCompatibilityBoundaryHeld ∧
  SpectralMeasurePVMOperatorValuedContinuousProjectionCountableBranchBoundaryHeld ∧
  SpectralMeasurePVMOperatorValuedContinuousProjectionFamilyBoundaryHeld ∧
  SpectralMeasurePVMOperatorValuedPVMConstructionLiftSpineReady ∧
  SpectralMeasurePVMOperatorValuedR4BoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMGenuineBoundedBorelFunctionalCalculusStillOpen ∧
  SpectralMeasurePVMGenuineBorelProjectionCompatibilityStillOpen ∧
  SpectralMeasurePVMContinuousProjectionGenuineCountableAdditivityStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The final R4 completion-boundary certificate is ready. -/
theorem spectral_measure_pvm_operator_valued_r4_completion_boundary_certificate_ready :
    SpectralMeasurePVMOperatorValuedR4CompletionBoundaryCertificateReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_spectral_measure_candidate_core_ready,
    spectral_measure_pvm_operator_valued_continuous_spectral_measure_candidate_boundary_held,
    spectral_measure_pvm_operator_valued_continuous_functional_calculus_boundary_held,
    spectral_measure_pvm_operator_valued_spectral_set_projection_compatibility_boundary_held,
    spectral_measure_pvm_operator_valued_continuous_projection_countable_branch_boundary_held,
    spectral_measure_pvm_operator_valued_continuous_projection_family_boundary_held,
    spectral_measure_pvm_operator_valued_pvm_construction_lift_spine_ready,
    spectral_measure_pvm_operator_valued_r4_boundary_held,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_genuine_bounded_borel_functional_calculus_still_open_ready,
    spectral_measure_pvm_genuine_borel_projection_compatibility_still_open_ready,
    spectral_measure_pvm_continuous_projection_genuine_countable_additivity_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Final visible R4 boundary after candidate assembly.  This is not the genuine
PVM theorem; it is the certificate that R4's candidate construction surface is
assembled and correctly bounded away from R5/R6/R7. -/
def SpectralMeasurePVMOperatorValuedR4CompletionBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedR4CompletionBoundaryCertificateReady ∧
  SpectralMeasurePVMOperatorValuedContinuousSpectralMeasureCandidateBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The final visible R4 completion boundary is held. -/
theorem spectral_measure_pvm_operator_valued_r4_completion_boundary_held :
    SpectralMeasurePVMOperatorValuedR4CompletionBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_r4_completion_boundary_certificate_ready,
    spectral_measure_pvm_operator_valued_continuous_spectral_measure_candidate_boundary_held,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
