import MGAP4D.R4.Theorem.SpectralMeasurePVMProjectionValuednessPromotionSurface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Candidate-map tag coherence at countable-union inputs for the current shell API. -/
theorem spectral_measure_pvm_target_api_all_countable_union_candidates_agree :
    ∀ A : ℕ → Set ℝ,
      (spectralMeasurePVMTargetAPI.pvmCandidate (⋃ n, A n)).obligationTag =
          SpectralMeasurePVMObligationTag.projectionValuedness ∧
        (spectralMeasurePVMTargetAPI.spectralMeasureCandidate (⋃ n, A n)).obligationTag =
          SpectralMeasurePVMObligationTag.spectralTheoremCompatibility := by
  intro A
  exact spectral_measure_pvm_target_api_countable_union_candidate_maps_agree A

/-- PVM candidate values at countable-union inputs lie in the current shell-level
projection-like prototype. -/
theorem spectral_measure_pvm_target_api_all_countable_union_pvm_candidates_projection_like :
    ∀ A : ℕ → Set ℝ,
      ProjectionLikeShell (spectralMeasurePVMTargetAPI.pvmCandidate (⋃ n, A n)) := by
  intro A
  exact spectral_measure_pvm_target_api_countable_union_pvm_projection_shell A

/-- Spectral-measure candidate values at countable-union inputs lie in the current
shell-level projection-like prototype. -/
theorem spectral_measure_pvm_target_api_all_countable_union_spectral_candidates_projection_like :
    ∀ A : ℕ → Set ℝ,
      ProjectionLikeShell
        (spectralMeasurePVMTargetAPI.spectralMeasureCandidate (⋃ n, A n)) := by
  intro A
  exact spectral_measure_pvm_target_api_countable_union_spectral_projection_shell A

/-- The current R4 shell has a prototype countable-additivity axiom.

This records countable-union shell coherence and the correct registration of the
full countable-additivity target.  It is not countable additivity of a true PVM
in an operator topology. -/
def SpectralMeasurePVMCountableAdditivityPrototypeAxiomReady : Prop :=
  SpectralMeasurePVMProjectionValuednessPromotionBoundary ∧
  spectralMeasurePVMFullAxiomsProofTarget.countableAdditivityTarget =
    SpectralMeasurePVMObligationTag.countableAdditivity ∧
  spectralMeasurePVMCandidateConstruction.countableAdditivityObligation =
    spectralMeasurePVMFullAxiomsProofTarget.countableAdditivityTarget ∧
  spectralMeasurePVMTargetAPI.countableAdditivityTag =
    SpectralMeasurePVMObligationTag.countableAdditivity ∧
  (∀ A : ℕ → Set ℝ,
    (spectralMeasurePVMTargetAPI.pvmCandidate (⋃ n, A n)).obligationTag =
        SpectralMeasurePVMObligationTag.projectionValuedness ∧
      (spectralMeasurePVMTargetAPI.spectralMeasureCandidate (⋃ n, A n)).obligationTag =
        SpectralMeasurePVMObligationTag.spectralTheoremCompatibility) ∧
  (∀ A : ℕ → Set ℝ,
    ProjectionLikeShell (spectralMeasurePVMTargetAPI.pvmCandidate (⋃ n, A n))) ∧
  (∀ A : ℕ → Set ℝ,
    ProjectionLikeShell
      (spectralMeasurePVMTargetAPI.spectralMeasureCandidate (⋃ n, A n))) ∧
  SpectralMeasurePVMCountableAdditivityShellReady

/-- The R4 shell-level countable-additivity prototype is ready. -/
theorem spectral_measure_pvm_countable_additivity_prototype_axiom_ready :
    SpectralMeasurePVMCountableAdditivityPrototypeAxiomReady := by
  exact ⟨
    spectral_measure_pvm_projection_valuedness_promotion_boundary_ready,
    rfl,
    rfl,
    rfl,
    spectral_measure_pvm_target_api_all_countable_union_candidates_agree,
    spectral_measure_pvm_target_api_all_countable_union_pvm_candidates_projection_like,
    spectral_measure_pvm_target_api_all_countable_union_spectral_candidates_projection_like,
    spectral_measure_pvm_countable_additivity_shell_ready⟩

/-- Boundary after the countable-additivity promotion surface.

The countable-additivity prototype is proved for the current typed shell target,
but full operator-theoretic countable additivity remains in the full-axioms
obligation list. -/
def SpectralMeasurePVMCountableAdditivityPromotionBoundary : Prop :=
  SpectralMeasurePVMCountableAdditivityPrototypeAxiomReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  spectralMeasurePVMFullAxiomsProofTarget.countableAdditivityTarget =
    SpectralMeasurePVMObligationTag.countableAdditivity

/-- The R4 countable-additivity-promotion boundary is ready. -/
theorem spectral_measure_pvm_countable_additivity_promotion_boundary_ready :
    SpectralMeasurePVMCountableAdditivityPromotionBoundary := by
  exact ⟨
    spectral_measure_pvm_countable_additivity_prototype_axiom_ready,
    spectral_measure_pvm_full_axioms_still_open,
    rfl⟩

end

end Theorem
end R4
end MGAP4D
