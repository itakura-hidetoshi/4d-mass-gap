import MGAP4D.R4.Theorem.SpectralMeasurePVMFullAxiomsObligationSurface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- In the current R4 target-API skeleton, the PVM candidate at the universal set
is the registered PVM candidate shell.

This is a prototype normalization theorem for the shell API.  It is not the full
operator identity `E(ℝ) = I`. -/
theorem spectral_measure_pvm_target_api_pvm_candidate_univ_eq_shell :
    spectralMeasurePVMTargetAPI.pvmCandidate (Set.univ : Set ℝ) =
      spectralMeasurePVMTargetAPIPVMCandidate := by
  rfl

/-- In the current R4 target-API skeleton, the spectral-measure candidate at the
universal set is the registered spectral-measure candidate shell.

This is a prototype normalization theorem for the shell API.  It is not the full
operator identity `E(ℝ) = I`. -/
theorem spectral_measure_pvm_target_api_spectral_measure_candidate_univ_eq_shell :
    spectralMeasurePVMTargetAPI.spectralMeasureCandidate (Set.univ : Set ℝ) =
      spectralMeasurePVMTargetAPISpectralMeasureCandidate := by
  rfl

/-- The current R4 shell has a prototype normalization axiom at `Set.univ`.

The target is typed by separate candidate shells, so this records shell-level tag
coherence rather than equality of the PVM and spectral-measure candidates.
Promotion to a true projection-valued operator identity remains a separate
full-axioms obligation. -/
def SpectralMeasurePVMNormalizationPrototypeAxiomReady : Prop :=
  SpectralMeasurePVMFullAxiomsObligationSurfaceReady ∧
  spectralMeasurePVMFullAxiomsProofTarget.normalizationTarget =
    SpectralMeasurePVMObligationTag.normalization ∧
  spectralMeasurePVMCandidateConstruction.normalizationObligation =
    spectralMeasurePVMFullAxiomsProofTarget.normalizationTarget ∧
  spectralMeasurePVMTargetAPI.normalizationTag =
    SpectralMeasurePVMObligationTag.normalization ∧
  spectralMeasurePVMTargetAPI.pvmCandidate (Set.univ : Set ℝ) =
    spectralMeasurePVMTargetAPIPVMCandidate ∧
  spectralMeasurePVMTargetAPI.spectralMeasureCandidate (Set.univ : Set ℝ) =
    spectralMeasurePVMTargetAPISpectralMeasureCandidate ∧
  (spectralMeasurePVMTargetAPI.pvmCandidate (Set.univ : Set ℝ)).obligationTag =
    SpectralMeasurePVMObligationTag.projectionValuedness ∧
  (spectralMeasurePVMTargetAPI.spectralMeasureCandidate (Set.univ : Set ℝ)).obligationTag =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility

/-- The R4 shell-level normalization prototype is ready. -/
theorem spectral_measure_pvm_normalization_prototype_axiom_ready :
    SpectralMeasurePVMNormalizationPrototypeAxiomReady := by
  exact ⟨
    spectral_measure_pvm_full_axioms_obligation_surface_ready,
    rfl,
    rfl,
    rfl,
    spectral_measure_pvm_target_api_pvm_candidate_univ_eq_shell,
    spectral_measure_pvm_target_api_spectral_measure_candidate_univ_eq_shell,
    (spectral_measure_pvm_target_api_univ_candidate_maps_agree).1,
    (spectral_measure_pvm_target_api_univ_candidate_maps_agree).2⟩

/-- Boundary after the normalization-promotion surface.

The normalization prototype is proved for the current typed shell target, but
full PVM normalization remains in the full-axioms obligation list. -/
def SpectralMeasurePVMNormalizationPromotionBoundary : Prop :=
  SpectralMeasurePVMNormalizationPrototypeAxiomReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  spectralMeasurePVMFullAxiomsProofTarget.normalizationTarget =
    SpectralMeasurePVMObligationTag.normalization

/-- The R4 normalization-promotion boundary is ready. -/
theorem spectral_measure_pvm_normalization_promotion_boundary_ready :
    SpectralMeasurePVMNormalizationPromotionBoundary := by
  exact ⟨
    spectral_measure_pvm_normalization_prototype_axiom_ready,
    spectral_measure_pvm_full_axioms_still_open,
    rfl⟩

end

end Theorem
end R4
end MGAP4D
