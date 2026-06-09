import MGAP4D.R4.Theorem.SpectralMeasurePVMTargetAPICoverage

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The R4 target API candidate maps carry their own registered obligation tags
on every real set.

This is only a shell theorem for the current typed target API.  It deliberately
does not state that the PVM candidate and spectral-measure candidate are the same
value. -/
theorem spectral_measure_pvm_target_api_candidate_maps_agree
    (s : Set ℝ) :
    (spectralMeasurePVMTargetAPI.pvmCandidate s).obligationTag =
        SpectralMeasurePVMObligationTag.projectionValuedness ∧
      (spectralMeasurePVMTargetAPI.spectralMeasureCandidate s).obligationTag =
        SpectralMeasurePVMObligationTag.spectralTheoremCompatibility := by
  exact ⟨rfl, rfl⟩

/-- The R4 target API candidate maps carry their expected tags on the universal set.

This is the minimal normalization shell: `Set.univ` is registered on both routes.
Full normalization as an identity-operator theorem remains open. -/
theorem spectral_measure_pvm_target_api_univ_candidate_maps_agree :
    (spectralMeasurePVMTargetAPI.pvmCandidate (Set.univ : Set ℝ)).obligationTag =
        SpectralMeasurePVMObligationTag.projectionValuedness ∧
      (spectralMeasurePVMTargetAPI.spectralMeasureCandidate (Set.univ : Set ℝ)).obligationTag =
        SpectralMeasurePVMObligationTag.spectralTheoremCompatibility := by
  exact spectral_measure_pvm_target_api_candidate_maps_agree (Set.univ : Set ℝ)

/-- R4 normalization shell readiness.

This closes only the target-API coherence shell for normalization.  The actual
PVM normalization obligation remains registered in the R4 obligation map. -/
def SpectralMeasurePVMNormalizationShellReady : Prop :=
  SpectralMeasurePVMTargetAPICoverageReady ∧
  spectralMeasurePVMTargetAPI.normalizationTag =
    SpectralMeasurePVMObligationTag.normalization ∧
  (spectralMeasurePVMTargetAPI.pvmCandidate (Set.univ : Set ℝ)).obligationTag =
    SpectralMeasurePVMObligationTag.projectionValuedness ∧
  (spectralMeasurePVMTargetAPI.spectralMeasureCandidate (Set.univ : Set ℝ)).obligationTag =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility ∧
  (∀ s : Set ℝ,
    (spectralMeasurePVMTargetAPI.pvmCandidate s).obligationTag =
      SpectralMeasurePVMObligationTag.projectionValuedness ∧
    (spectralMeasurePVMTargetAPI.spectralMeasureCandidate s).obligationTag =
      SpectralMeasurePVMObligationTag.spectralTheoremCompatibility) ∧
  spectralMeasurePVMCandidateConstruction.normalizationObligation =
    SpectralMeasurePVMObligationTag.normalization

/-- The R4 normalization shell is ready. -/
theorem spectral_measure_pvm_normalization_shell_ready :
    SpectralMeasurePVMNormalizationShellReady := by
  exact ⟨
    spectral_measure_pvm_target_api_coverage_ready,
    rfl,
    (spectral_measure_pvm_target_api_univ_candidate_maps_agree).1,
    (spectral_measure_pvm_target_api_univ_candidate_maps_agree).2,
    spectral_measure_pvm_target_api_candidate_maps_agree,
    rfl⟩

/-- Boundary for the R4 normalization shell.

The shell proof is available, but the full PVM normalization axiom is still only
registered as an R4 obligation. -/
def SpectralMeasurePVMNormalizationShellBoundary : Prop :=
  SpectralMeasurePVMNormalizationShellReady ∧
  spectralMeasurePVMCandidateConstruction.normalizationObligation =
    SpectralMeasurePVMObligationTag.normalization ∧
  SpectralMeasurePVMObligationMapReady

/-- The R4 normalization shell boundary is ready. -/
theorem spectral_measure_pvm_normalization_shell_boundary_ready :
    SpectralMeasurePVMNormalizationShellBoundary := by
  exact ⟨
    spectral_measure_pvm_normalization_shell_ready,
    rfl,
    spectral_measure_pvm_obligation_map_ready⟩

end

end Theorem
end R4
end MGAP4D
