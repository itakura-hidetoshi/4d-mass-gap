import MGAP4D.R4.Theorem.SpectralMeasurePVMCountableAdditivityShell

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The R4 target API is attached to the same self-adjoint operator input used to
start the spectral-measure/PVM stage.

This is a compatibility shell.  It does not construct a spectral resolution or a
functional calculus. -/
theorem spectral_measure_pvm_target_api_self_adjoint_operator_compatible :
    IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact r4_self_adjoint_operator_input_ready

/-- The R4 target API is available together with the self-adjoint input. -/
def SpectralMeasurePVMOperatorTargetCompatibilityReady : Prop :=
  SpectralMeasurePVMCountableAdditivityShellReady ∧
  spectralMeasurePVMTargetAPI.ready ∧
  IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  spectralMeasurePVMTargetAPI.spectralCompatibilityTag =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility

/-- The operator-target compatibility shell is ready. -/
theorem spectral_measure_pvm_operator_target_compatibility_ready :
    SpectralMeasurePVMOperatorTargetCompatibilityReady := by
  exact ⟨
    spectral_measure_pvm_countable_additivity_shell_ready,
    spectral_measure_pvm_target_api_ready,
    spectral_measure_pvm_target_api_self_adjoint_operator_compatible,
    rfl⟩

/-- Candidate-map compatibility with the operator input, at the shell level. -/
def SpectralMeasurePVMSpectralCompatibilityShellReady : Prop :=
  SpectralMeasurePVMOperatorTargetCompatibilityReady ∧
  spectralMeasurePVMCandidateConstruction.spectralTheoremCompatibilityObligation =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility ∧
  (∀ s : Set ℝ,
    spectralMeasurePVMTargetAPI.pvmCandidate s =
      spectralMeasurePVMTargetAPI.spectralMeasureCandidate s) ∧
  IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap

/-- The R4 spectral-compatibility shell is ready. -/
theorem spectral_measure_pvm_spectral_compatibility_shell_ready :
    SpectralMeasurePVMSpectralCompatibilityShellReady := by
  exact ⟨
    spectral_measure_pvm_operator_target_compatibility_ready,
    rfl,
    spectral_measure_pvm_target_api_candidate_maps_agree,
    spectral_measure_pvm_target_api_self_adjoint_operator_compatible⟩

/-- Boundary for the R4 spectral-compatibility shell.

The shell connects the R3 self-adjoint operator input to the R4 target API.  A
true spectral-measure/PVM construction remains a later R4 task. -/
def SpectralMeasurePVMSpectralCompatibilityShellBoundary : Prop :=
  SpectralMeasurePVMSpectralCompatibilityShellReady ∧
  SpectralMeasurePVMObligationMapReady ∧
  spectralMeasurePVMCandidateConstruction.spectralTheoremCompatibilityObligation =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility

/-- The R4 spectral-compatibility shell boundary is ready. -/
theorem spectral_measure_pvm_spectral_compatibility_shell_boundary_ready :
    SpectralMeasurePVMSpectralCompatibilityShellBoundary := by
  exact ⟨
    spectral_measure_pvm_spectral_compatibility_shell_ready,
    spectral_measure_pvm_obligation_map_ready,
    rfl⟩

end

end Theorem
end R4
end MGAP4D