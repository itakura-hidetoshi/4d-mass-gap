import MGAP4D.R4.Theorem.SpectralMeasurePVMTargetAPICoverage

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The R4 target API candidate maps agree on every registered real set.

This is only a shell theorem for the current `PUnit` target API.  It does not
state the full PVM normalization axiom `E(ℝ) = I`. -/
theorem spectral_measure_pvm_target_api_candidate_maps_agree
    (s : Set ℝ) :
    spectralMeasurePVMTargetAPI.pvmCandidate s =
      spectralMeasurePVMTargetAPI.spectralMeasureCandidate s := by
  rfl

/-- The R4 target API candidate maps agree on the universal set.

This is the minimal normalization shell: agreement of the two candidate maps at
`Set.univ`.  Full normalization as an identity-operator theorem remains open. -/
theorem spectral_measure_pvm_target_api_univ_candidate_maps_agree :
    spectralMeasurePVMTargetAPI.pvmCandidate (Set.univ : Set ℝ) =
      spectralMeasurePVMTargetAPI.spectralMeasureCandidate (Set.univ : Set ℝ) := by
  rfl

/-- R4 normalization shell readiness.

This closes only the target-API coherence shell for normalization.  The actual
PVM normalization obligation remains registered in the R4 obligation map. -/
def SpectralMeasurePVMNormalizationShellReady : Prop :=
  SpectralMeasurePVMTargetAPICoverageReady ∧
  spectralMeasurePVMTargetAPI.normalizationTag =
    SpectralMeasurePVMObligationTag.normalization ∧
  spectralMeasurePVMTargetAPI.pvmCandidate (Set.univ : Set ℝ) =
    spectralMeasurePVMTargetAPI.spectralMeasureCandidate (Set.univ : Set ℝ) ∧
  (∀ s : Set ℝ,
    spectralMeasurePVMTargetAPI.pvmCandidate s =
      spectralMeasurePVMTargetAPI.spectralMeasureCandidate s) ∧
  spectralMeasurePVMCandidateConstruction.normalizationObligation =
    SpectralMeasurePVMObligationTag.normalization

/-- The R4 normalization shell is ready. -/
theorem spectral_measure_pvm_normalization_shell_ready :
    SpectralMeasurePVMNormalizationShellReady := by
  exact ⟨
    spectral_measure_pvm_target_api_coverage_ready,
    rfl,
    spectral_measure_pvm_target_api_univ_candidate_maps_agree,
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