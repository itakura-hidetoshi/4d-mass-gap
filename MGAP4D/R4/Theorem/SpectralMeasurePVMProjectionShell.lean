import MGAP4D.R4.Theorem.SpectralMeasurePVMNormalizationShell

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Trivial projection-like shell for the current `PUnit` target.

This is not the full operator-theoretic idempotence/self-adjointness proof for a
projection.  It only says that every current target value is the unique skeleton
point. -/
def ProjectionLikeShell
    (p : spectralMeasurePVMTargetAPI.projectionTarget) : Prop :=
  p = PUnit.unit

/-- The PVM candidate value lies in the projection-like shell. -/
theorem spectral_measure_pvm_target_api_pvm_candidate_projection_shell
    (s : Set ℝ) :
    ProjectionLikeShell (spectralMeasurePVMTargetAPI.pvmCandidate s) := by
  rfl

/-- The spectral-measure candidate value lies in the projection-like shell. -/
theorem spectral_measure_pvm_target_api_spectral_candidate_projection_shell
    (s : Set ℝ) :
    ProjectionLikeShell (spectralMeasurePVMTargetAPI.spectralMeasureCandidate s) := by
  rfl

/-- PVM and spectral-measure candidate values are projection-like shell values. -/
def SpectralMeasurePVMProjectionShellReady : Prop :=
  SpectralMeasurePVMNormalizationShellReady ∧
  spectralMeasurePVMTargetAPI.projectionValuednessTag =
    SpectralMeasurePVMObligationTag.projectionValuedness ∧
  (∀ s : Set ℝ,
    ProjectionLikeShell (spectralMeasurePVMTargetAPI.pvmCandidate s)) ∧
  (∀ s : Set ℝ,
    ProjectionLikeShell (spectralMeasurePVMTargetAPI.spectralMeasureCandidate s)) ∧
  spectralMeasurePVMCandidateConstruction.projectionValuednessObligation =
    SpectralMeasurePVMObligationTag.projectionValuedness

/-- The R4 projection-valuedness shell is ready. -/
theorem spectral_measure_pvm_projection_shell_ready :
    SpectralMeasurePVMProjectionShellReady := by
  exact ⟨
    spectral_measure_pvm_normalization_shell_ready,
    rfl,
    spectral_measure_pvm_target_api_pvm_candidate_projection_shell,
    spectral_measure_pvm_target_api_spectral_candidate_projection_shell,
    rfl⟩

/-- Boundary for the R4 projection shell.

The skeleton target values are projection-like in the minimal `PUnit` shell.  The
full operator-theoretic projection-valuedness axiom remains registered as an R4
obligation. -/
def SpectralMeasurePVMProjectionShellBoundary : Prop :=
  SpectralMeasurePVMProjectionShellReady ∧
  spectralMeasurePVMCandidateConstruction.projectionValuednessObligation =
    SpectralMeasurePVMObligationTag.projectionValuedness ∧
  SpectralMeasurePVMObligationMapReady

/-- The R4 projection shell boundary is ready. -/
theorem spectral_measure_pvm_projection_shell_boundary_ready :
    SpectralMeasurePVMProjectionShellBoundary := by
  exact ⟨
    spectral_measure_pvm_projection_shell_ready,
    rfl,
    spectral_measure_pvm_obligation_map_ready⟩

end

end Theorem
end R4
end MGAP4D