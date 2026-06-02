import MGAP4D.R4.Theorem.SpectralMeasurePVMStructuralShellCompletion

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Ordered proof targets for promoting the R4 structural shell to a genuine
spectral-measure/PVM theorem.

These are proof targets, not completed axioms.  The point of this surface is to
make the remaining R4 proof order explicit after the structural shell has been
completed. -/
structure SpectralMeasurePVMFullAxiomsProofTarget where
  normalizationTarget : SpectralMeasurePVMObligationTag
  projectionValuednessTarget : SpectralMeasurePVMObligationTag
  countableAdditivityTarget : SpectralMeasurePVMObligationTag
  spectralTheoremCompatibilityTarget : SpectralMeasurePVMObligationTag
  concreteSpectralMeasureTarget : SpectralMeasurePVMObligationTag
  concretePVMTarget : SpectralMeasurePVMObligationTag

/-- The R4 full-axioms proof target map. -/
def spectralMeasurePVMFullAxiomsProofTarget :
    SpectralMeasurePVMFullAxiomsProofTarget :=
  { normalizationTarget := SpectralMeasurePVMObligationTag.normalization
    projectionValuednessTarget := SpectralMeasurePVMObligationTag.projectionValuedness
    countableAdditivityTarget := SpectralMeasurePVMObligationTag.countableAdditivity
    spectralTheoremCompatibilityTarget :=
      SpectralMeasurePVMObligationTag.spectralTheoremCompatibility
    concreteSpectralMeasureTarget :=
      SpectralMeasurePVMObligationTag.concreteSpectralMeasure
    concretePVMTarget := SpectralMeasurePVMObligationTag.concretePVM }

/-- Readiness of the full-axioms proof target map.

This proves only that the remaining targets are correctly registered and ordered
on top of the completed structural shell. -/
def SpectralMeasurePVMFullAxiomsProofTargetReady : Prop :=
  SpectralMeasurePVMPublicShellBoundary ∧
  spectralMeasurePVMFullAxiomsProofTarget.normalizationTarget =
    SpectralMeasurePVMObligationTag.normalization ∧
  spectralMeasurePVMFullAxiomsProofTarget.projectionValuednessTarget =
    SpectralMeasurePVMObligationTag.projectionValuedness ∧
  spectralMeasurePVMFullAxiomsProofTarget.countableAdditivityTarget =
    SpectralMeasurePVMObligationTag.countableAdditivity ∧
  spectralMeasurePVMFullAxiomsProofTarget.spectralTheoremCompatibilityTarget =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility ∧
  spectralMeasurePVMFullAxiomsProofTarget.concreteSpectralMeasureTarget =
    SpectralMeasurePVMObligationTag.concreteSpectralMeasure ∧
  spectralMeasurePVMFullAxiomsProofTarget.concretePVMTarget =
    SpectralMeasurePVMObligationTag.concretePVM

/-- The full-axioms proof target map is ready. -/
theorem spectral_measure_pvm_full_axioms_proof_target_ready :
    SpectralMeasurePVMFullAxiomsProofTargetReady := by
  exact ⟨
    spectral_measure_pvm_public_shell_boundary_ready,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl⟩

/-- The full-axioms proof target map is aligned with the candidate construction
obligation tags. -/
def SpectralMeasurePVMFullAxiomsCandidateTargetAligned : Prop :=
  SpectralMeasurePVMFullAxiomsProofTargetReady ∧
  spectralMeasurePVMCandidateConstruction.normalizationObligation =
    spectralMeasurePVMFullAxiomsProofTarget.normalizationTarget ∧
  spectralMeasurePVMCandidateConstruction.projectionValuednessObligation =
    spectralMeasurePVMFullAxiomsProofTarget.projectionValuednessTarget ∧
  spectralMeasurePVMCandidateConstruction.countableAdditivityObligation =
    spectralMeasurePVMFullAxiomsProofTarget.countableAdditivityTarget ∧
  spectralMeasurePVMCandidateConstruction.spectralTheoremCompatibilityObligation =
    spectralMeasurePVMFullAxiomsProofTarget.spectralTheoremCompatibilityTarget ∧
  spectralMeasurePVMCandidateConstruction.concreteSpectralMeasureObligation =
    spectralMeasurePVMFullAxiomsProofTarget.concreteSpectralMeasureTarget ∧
  spectralMeasurePVMCandidateConstruction.concretePVMObligation =
    spectralMeasurePVMFullAxiomsProofTarget.concretePVMTarget

/-- The full-axioms proof target map is aligned with the candidate construction. -/
theorem spectral_measure_pvm_full_axioms_candidate_target_aligned :
    SpectralMeasurePVMFullAxiomsCandidateTargetAligned := by
  exact ⟨
    spectral_measure_pvm_full_axioms_proof_target_ready,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl⟩

/-- R4 full-axioms obligation surface.

This is the handoff from the completed structural shell to the remaining full
PVM/spectral-measure proof obligations. -/
def SpectralMeasurePVMFullAxiomsObligationSurfaceReady : Prop :=
  SpectralMeasurePVMStructuralShellCompleted ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMFullAxiomsCandidateTargetAligned

/-- The R4 full-axioms obligation surface is ready. -/
theorem spectral_measure_pvm_full_axioms_obligation_surface_ready :
    SpectralMeasurePVMFullAxiomsObligationSurfaceReady := by
  exact ⟨
    spectral_measure_pvm_structural_shell_completed,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_full_axioms_candidate_target_aligned⟩

end

end Theorem
end R4
end MGAP4D