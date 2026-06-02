import MGAP4D.R4.Theorem.SpectralMeasurePVMNormalizationPromotionSurface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Every current R4 PVM candidate value lies in the shell-level projection-like
prototype.

Since the current target is `PUnit`, this is not the full operator-theoretic
projection-valuedness axiom. -/
theorem spectral_measure_pvm_target_api_all_pvm_candidates_projection_like :
    ∀ s : Set ℝ,
      ProjectionLikeShell (spectralMeasurePVMTargetAPI.pvmCandidate s) := by
  intro s
  exact spectral_measure_pvm_target_api_pvm_candidate_projection_shell s

/-- Every current R4 spectral-measure candidate value lies in the shell-level
projection-like prototype.

Since the current target is `PUnit`, this is not the full operator-theoretic
projection-valuedness axiom. -/
theorem spectral_measure_pvm_target_api_all_spectral_candidates_projection_like :
    ∀ s : Set ℝ,
      ProjectionLikeShell (spectralMeasurePVMTargetAPI.spectralMeasureCandidate s) := by
  intro s
  exact spectral_measure_pvm_target_api_spectral_candidate_projection_shell s

/-- The current R4 shell has a prototype projection-valuedness axiom.

This records that all current candidate values are projection-like shell values
and that the full projection-valuedness target is correctly registered. -/
def SpectralMeasurePVMProjectionValuednessPrototypeAxiomReady : Prop :=
  SpectralMeasurePVMNormalizationPromotionBoundary ∧
  spectralMeasurePVMFullAxiomsProofTarget.projectionValuednessTarget =
    SpectralMeasurePVMObligationTag.projectionValuedness ∧
  spectralMeasurePVMCandidateConstruction.projectionValuednessObligation =
    spectralMeasurePVMFullAxiomsProofTarget.projectionValuednessTarget ∧
  spectralMeasurePVMTargetAPI.projectionValuednessTag =
    SpectralMeasurePVMObligationTag.projectionValuedness ∧
  (∀ s : Set ℝ,
    ProjectionLikeShell (spectralMeasurePVMTargetAPI.pvmCandidate s)) ∧
  (∀ s : Set ℝ,
    ProjectionLikeShell (spectralMeasurePVMTargetAPI.spectralMeasureCandidate s)) ∧
  SpectralMeasurePVMProjectionShellReady

/-- The R4 shell-level projection-valuedness prototype is ready. -/
theorem spectral_measure_pvm_projection_valuedness_prototype_axiom_ready :
    SpectralMeasurePVMProjectionValuednessPrototypeAxiomReady := by
  exact ⟨
    spectral_measure_pvm_normalization_promotion_boundary_ready,
    rfl,
    rfl,
    rfl,
    spectral_measure_pvm_target_api_all_pvm_candidates_projection_like,
    spectral_measure_pvm_target_api_all_spectral_candidates_projection_like,
    spectral_measure_pvm_projection_shell_ready⟩

/-- Boundary after the projection-valuedness promotion surface.

The projection-valuedness prototype is proved for the current `PUnit` shell
target, but full operator-theoretic projection-valuedness remains in the
full-axioms obligation list. -/
def SpectralMeasurePVMProjectionValuednessPromotionBoundary : Prop :=
  SpectralMeasurePVMProjectionValuednessPrototypeAxiomReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  spectralMeasurePVMFullAxiomsProofTarget.projectionValuednessTarget =
    SpectralMeasurePVMObligationTag.projectionValuedness

/-- The R4 projection-valuedness-promotion boundary is ready. -/
theorem spectral_measure_pvm_projection_valuedness_promotion_boundary_ready :
    SpectralMeasurePVMProjectionValuednessPromotionBoundary := by
  exact ⟨
    spectral_measure_pvm_projection_valuedness_prototype_axiom_ready,
    spectral_measure_pvm_full_axioms_still_open,
    rfl⟩

end

end Theorem
end R4
end MGAP4D