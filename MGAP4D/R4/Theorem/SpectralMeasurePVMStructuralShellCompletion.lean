import MGAP4D.R4.Theorem.SpectralMeasurePVMSpectralCompatibilityShell

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R4 structural shell completion for the spectral-measure/PVM stage.

This bundles the four structural shells currently proved in R4:
normalization shell, projection-valuedness shell, countable-union shell, and
spectral-compatibility shell.  It is intentionally not the full spectral theorem
or a true operator-valued PVM construction. -/
def SpectralMeasurePVMStructuralShellCompleted : Prop :=
  SpectralMeasurePVMInputReady ∧
  spectralMeasurePVMCandidateConstruction.ready ∧
  SpectralMeasurePVMObligationMapReady ∧
  spectralMeasurePVMTargetAPI.ready ∧
  SpectralMeasurePVMTargetAPICoverageReady ∧
  SpectralMeasurePVMNormalizationShellReady ∧
  SpectralMeasurePVMProjectionShellReady ∧
  SpectralMeasurePVMCountableAdditivityShellReady ∧
  SpectralMeasurePVMSpectralCompatibilityShellReady

/-- The R4 structural shell is completed. -/
theorem spectral_measure_pvm_structural_shell_completed :
    SpectralMeasurePVMStructuralShellCompleted := by
  exact ⟨
    spectral_measure_pvm_input_ready,
    spectral_measure_pvm_candidate_construction_ready,
    spectral_measure_pvm_obligation_map_ready,
    spectral_measure_pvm_target_api_ready,
    spectral_measure_pvm_target_api_coverage_ready,
    spectral_measure_pvm_normalization_shell_ready,
    spectral_measure_pvm_projection_shell_ready,
    spectral_measure_pvm_countable_additivity_shell_ready,
    spectral_measure_pvm_spectral_compatibility_shell_ready⟩

/-- The full R4 PVM theorem is still separated from the structural shell.

The structural shell does not claim the full axioms.  The remaining obligations
are kept visible as tags, not silently discharged. -/
def SpectralMeasurePVMFullAxiomsStillOpen : Prop :=
  spectralMeasurePVMCandidateConstruction.normalizationObligation =
    SpectralMeasurePVMObligationTag.normalization ∧
  spectralMeasurePVMCandidateConstruction.projectionValuednessObligation =
    SpectralMeasurePVMObligationTag.projectionValuedness ∧
  spectralMeasurePVMCandidateConstruction.countableAdditivityObligation =
    SpectralMeasurePVMObligationTag.countableAdditivity ∧
  spectralMeasurePVMCandidateConstruction.spectralTheoremCompatibilityObligation =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility ∧
  spectralMeasurePVMCandidateConstruction.concreteSpectralMeasureObligation =
    SpectralMeasurePVMObligationTag.concreteSpectralMeasure ∧
  spectralMeasurePVMCandidateConstruction.concretePVMObligation =
    SpectralMeasurePVMObligationTag.concretePVM

/-- The full R4 PVM axioms remain explicitly open after the structural shell. -/
theorem spectral_measure_pvm_full_axioms_still_open :
    SpectralMeasurePVMFullAxiomsStillOpen := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- R4 public shell boundary.

This is the safe public boundary for the current R4 stage: the structural shell
is complete, while full PVM axioms remain open obligations. -/
def SpectralMeasurePVMPublicShellBoundary : Prop :=
  SpectralMeasurePVMStructuralShellCompleted ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMObligationMapReady

/-- The R4 public shell boundary is ready. -/
theorem spectral_measure_pvm_public_shell_boundary_ready :
    SpectralMeasurePVMPublicShellBoundary := by
  exact ⟨
    spectral_measure_pvm_structural_shell_completed,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_obligation_map_ready⟩

end

end Theorem
end R4
end MGAP4D