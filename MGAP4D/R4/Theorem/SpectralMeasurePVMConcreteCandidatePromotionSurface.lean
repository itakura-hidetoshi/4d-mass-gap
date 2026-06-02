import MGAP4D.R4.Theorem.SpectralMeasurePVMSpectralCompatibilityPromotionSurface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The current R4 shell carries a concrete spectral-measure candidate map. -/
theorem spectral_measure_pvm_target_api_concrete_spectral_measure_candidate_exists :
    ∃ f : spectralMeasurePVMTargetAPI.setIndex → spectralMeasurePVMTargetAPI.projectionTarget,
      f = spectralMeasurePVMTargetAPI.spectralMeasureCandidate := by
  exact spectral_measure_pvm_target_api_has_spectral_measure_candidate

/-- The current R4 shell carries a concrete PVM candidate map. -/
theorem spectral_measure_pvm_target_api_concrete_pvm_candidate_exists :
    ∃ f : spectralMeasurePVMTargetAPI.setIndex → spectralMeasurePVMTargetAPI.projectionTarget,
      f = spectralMeasurePVMTargetAPI.pvmCandidate := by
  exact spectral_measure_pvm_target_api_has_pvm_candidate

/-- Shell-level promotion boundary for the concrete spectral-measure candidate.

This proves existence and target alignment for the current `PUnit` skeleton.  It
does not prove that the candidate is a genuine countably additive spectral
measure. -/
def SpectralMeasurePVMConcreteSpectralMeasureCandidateReady : Prop :=
  SpectralMeasurePVMSpectralCompatibilityPromotionBoundary ∧
  spectralMeasurePVMFullAxiomsProofTarget.concreteSpectralMeasureTarget =
    SpectralMeasurePVMObligationTag.concreteSpectralMeasure ∧
  spectralMeasurePVMCandidateConstruction.concreteSpectralMeasureObligation =
    spectralMeasurePVMFullAxiomsProofTarget.concreteSpectralMeasureTarget ∧
  (∃ f : spectralMeasurePVMTargetAPI.setIndex → spectralMeasurePVMTargetAPI.projectionTarget,
    f = spectralMeasurePVMTargetAPI.spectralMeasureCandidate) ∧
  spectralMeasurePVMTargetAPI.ready

/-- The concrete spectral-measure candidate shell is ready. -/
theorem spectral_measure_pvm_concrete_spectral_measure_candidate_ready :
    SpectralMeasurePVMConcreteSpectralMeasureCandidateReady := by
  exact ⟨
    spectral_measure_pvm_spectral_compatibility_promotion_boundary_ready,
    rfl,
    rfl,
    spectral_measure_pvm_target_api_concrete_spectral_measure_candidate_exists,
    spectral_measure_pvm_target_api_ready⟩

/-- Shell-level promotion boundary for the concrete PVM candidate.

This proves existence and target alignment for the current `PUnit` skeleton.  It
does not prove that the candidate is a genuine projection-valued measure. -/
def SpectralMeasurePVMConcretePVMCandidateReady : Prop :=
  SpectralMeasurePVMConcreteSpectralMeasureCandidateReady ∧
  spectralMeasurePVMFullAxiomsProofTarget.concretePVMTarget =
    SpectralMeasurePVMObligationTag.concretePVM ∧
  spectralMeasurePVMCandidateConstruction.concretePVMObligation =
    spectralMeasurePVMFullAxiomsProofTarget.concretePVMTarget ∧
  (∃ f : spectralMeasurePVMTargetAPI.setIndex → spectralMeasurePVMTargetAPI.projectionTarget,
    f = spectralMeasurePVMTargetAPI.pvmCandidate) ∧
  spectralMeasurePVMTargetAPI.ready

/-- The concrete PVM candidate shell is ready. -/
theorem spectral_measure_pvm_concrete_pvm_candidate_ready :
    SpectralMeasurePVMConcretePVMCandidateReady := by
  exact ⟨
    spectral_measure_pvm_concrete_spectral_measure_candidate_ready,
    rfl,
    rfl,
    spectral_measure_pvm_target_api_concrete_pvm_candidate_exists,
    spectral_measure_pvm_target_api_ready⟩

/-- Final R4 shell-candidate boundary.

All six full-axiom targets have now been connected to the current skeleton:
normalization, projection-valuedness, countable-additivity, spectral
compatibility, concrete spectral-measure candidate, and concrete PVM candidate.
The full operator-theoretic axioms remain open. -/
def SpectralMeasurePVMConcreteCandidatePromotionBoundary : Prop :=
  SpectralMeasurePVMConcretePVMCandidateReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMFullAxiomsCandidateTargetAligned

/-- The final R4 shell-candidate boundary is ready. -/
theorem spectral_measure_pvm_concrete_candidate_promotion_boundary_ready :
    SpectralMeasurePVMConcreteCandidatePromotionBoundary := by
  exact ⟨
    spectral_measure_pvm_concrete_pvm_candidate_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_full_axioms_candidate_target_aligned⟩

end

end Theorem
end R4
end MGAP4D