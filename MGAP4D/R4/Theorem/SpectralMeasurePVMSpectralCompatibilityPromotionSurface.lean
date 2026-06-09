import MGAP4D.R4.Theorem.SpectralMeasurePVMCountableAdditivityPromotionSurface
import MGAP4D.R4.Theorem.SpectralMeasurePVMSpectralCompatibilityShell

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Candidate-map tag coherence for all measurable-set placeholders in the current
R4 shell API.  This is shell coherence, not a spectral-resolution theorem. -/
theorem spectral_measure_pvm_target_api_all_candidates_spectrally_compatible :
    ∀ s : Set ℝ,
      (spectralMeasurePVMTargetAPI.pvmCandidate s).obligationTag =
          SpectralMeasurePVMObligationTag.projectionValuedness ∧
        (spectralMeasurePVMTargetAPI.spectralMeasureCandidate s).obligationTag =
          SpectralMeasurePVMObligationTag.spectralTheoremCompatibility := by
  intro s
  exact spectral_measure_pvm_target_api_candidate_maps_agree s

/-- The current R4 shell has a prototype spectral-compatibility theorem.

This connects the self-adjoint operator input to the shell target API and aligns
that shell with the remaining spectral-compatibility target.  It is not a full
spectral theorem, spectral resolution, or functional calculus. -/
def SpectralMeasurePVMSpectralCompatibilityPrototypeReady : Prop :=
  SpectralMeasurePVMCountableAdditivityPromotionBoundary ∧
  spectralMeasurePVMFullAxiomsProofTarget.spectralTheoremCompatibilityTarget =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility ∧
  spectralMeasurePVMCandidateConstruction.spectralTheoremCompatibilityObligation =
    spectralMeasurePVMFullAxiomsProofTarget.spectralTheoremCompatibilityTarget ∧
  spectralMeasurePVMTargetAPI.spectralCompatibilityTag =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility ∧
  IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  (∀ s : Set ℝ,
    (spectralMeasurePVMTargetAPI.pvmCandidate s).obligationTag =
        SpectralMeasurePVMObligationTag.projectionValuedness ∧
      (spectralMeasurePVMTargetAPI.spectralMeasureCandidate s).obligationTag =
        SpectralMeasurePVMObligationTag.spectralTheoremCompatibility) ∧
  SpectralMeasurePVMSpectralCompatibilityShellReady

/-- The R4 shell-level spectral-compatibility prototype is ready. -/
theorem spectral_measure_pvm_spectral_compatibility_prototype_ready :
    SpectralMeasurePVMSpectralCompatibilityPrototypeReady := by
  exact ⟨
    spectral_measure_pvm_countable_additivity_promotion_boundary_ready,
    rfl,
    rfl,
    rfl,
    spectral_measure_pvm_target_api_self_adjoint_operator_compatible,
    spectral_measure_pvm_target_api_all_candidates_spectrally_compatible,
    spectral_measure_pvm_spectral_compatibility_shell_ready⟩

/-- Boundary after the spectral-compatibility promotion surface.

The self-adjoint input is connected to the shell target API, while the true
spectral theorem remains separated from the shell. -/
def SpectralMeasurePVMSpectralCompatibilityPromotionBoundary : Prop :=
  SpectralMeasurePVMSpectralCompatibilityPrototypeReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  spectralMeasurePVMFullAxiomsProofTarget.spectralTheoremCompatibilityTarget =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility

/-- The R4 spectral-compatibility-promotion boundary is ready. -/
theorem spectral_measure_pvm_spectral_compatibility_promotion_boundary_ready :
    SpectralMeasurePVMSpectralCompatibilityPromotionBoundary := by
  exact ⟨
    spectral_measure_pvm_spectral_compatibility_prototype_ready,
    spectral_measure_pvm_full_axioms_still_open,
    rfl⟩

end

end Theorem
end R4
end MGAP4D
