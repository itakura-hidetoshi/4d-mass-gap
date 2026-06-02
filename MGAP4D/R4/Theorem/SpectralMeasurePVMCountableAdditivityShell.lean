import MGAP4D.R4.Theorem.SpectralMeasurePVMProjectionShell

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Candidate-map agreement on countable unions in the current skeleton API.

This is not the full PVM countable-additivity theorem.  It only states that the
current PVM candidate and spectral-measure candidate agree on a countable union
input. -/
theorem spectral_measure_pvm_target_api_countable_union_candidate_maps_agree
    (A : ℕ → Set ℝ) :
    spectralMeasurePVMTargetAPI.pvmCandidate (⋃ n, A n) =
      spectralMeasurePVMTargetAPI.spectralMeasureCandidate (⋃ n, A n) := by
  rfl

/-- The PVM candidate value on a countable union is projection-like in the shell. -/
theorem spectral_measure_pvm_target_api_countable_union_pvm_projection_shell
    (A : ℕ → Set ℝ) :
    ProjectionLikeShell (spectralMeasurePVMTargetAPI.pvmCandidate (⋃ n, A n)) := by
  rfl

/-- The spectral-measure candidate value on a countable union is projection-like
in the shell. -/
theorem spectral_measure_pvm_target_api_countable_union_spectral_projection_shell
    (A : ℕ → Set ℝ) :
    ProjectionLikeShell
      (spectralMeasurePVMTargetAPI.spectralMeasureCandidate (⋃ n, A n)) := by
  rfl

/-- R4 countable-additivity shell readiness.

This closes only the skeleton coherence at countable-union inputs.  It does not
state additivity of projection operators, orthogonality, strong operator
convergence, or countable additivity of a true PVM. -/
def SpectralMeasurePVMCountableAdditivityShellReady : Prop :=
  SpectralMeasurePVMProjectionShellReady ∧
  spectralMeasurePVMTargetAPI.countableAdditivityTag =
    SpectralMeasurePVMObligationTag.countableAdditivity ∧
  (∀ A : ℕ → Set ℝ,
    spectralMeasurePVMTargetAPI.pvmCandidate (⋃ n, A n) =
      spectralMeasurePVMTargetAPI.spectralMeasureCandidate (⋃ n, A n)) ∧
  (∀ A : ℕ → Set ℝ,
    ProjectionLikeShell (spectralMeasurePVMTargetAPI.pvmCandidate (⋃ n, A n))) ∧
  (∀ A : ℕ → Set ℝ,
    ProjectionLikeShell
      (spectralMeasurePVMTargetAPI.spectralMeasureCandidate (⋃ n, A n))) ∧
  spectralMeasurePVMCandidateConstruction.countableAdditivityObligation =
    SpectralMeasurePVMObligationTag.countableAdditivity

/-- The R4 countable-additivity shell is ready. -/
theorem spectral_measure_pvm_countable_additivity_shell_ready :
    SpectralMeasurePVMCountableAdditivityShellReady := by
  exact ⟨
    spectral_measure_pvm_projection_shell_ready,
    rfl,
    spectral_measure_pvm_target_api_countable_union_candidate_maps_agree,
    spectral_measure_pvm_target_api_countable_union_pvm_projection_shell,
    spectral_measure_pvm_target_api_countable_union_spectral_projection_shell,
    rfl⟩

/-- Boundary for the R4 countable-additivity shell.

The countable-union skeleton is available, but full countable additivity remains
registered as an R4 obligation. -/
def SpectralMeasurePVMCountableAdditivityShellBoundary : Prop :=
  SpectralMeasurePVMCountableAdditivityShellReady ∧
  spectralMeasurePVMCandidateConstruction.countableAdditivityObligation =
    SpectralMeasurePVMObligationTag.countableAdditivity ∧
  SpectralMeasurePVMObligationMapReady

/-- The R4 countable-additivity shell boundary is ready. -/
theorem spectral_measure_pvm_countable_additivity_shell_boundary_ready :
    SpectralMeasurePVMCountableAdditivityShellBoundary := by
  exact ⟨
    spectral_measure_pvm_countable_additivity_shell_ready,
    rfl,
    spectral_measure_pvm_obligation_map_ready⟩

end

end Theorem
end R4
end MGAP4D