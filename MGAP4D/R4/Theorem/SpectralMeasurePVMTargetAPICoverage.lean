import MGAP4D.R4.Theorem.SpectralMeasurePVMTargetAPI

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R4 target API coverage predicate.

The target API covers the four structural PVM/spectral-measure obligations,
while the candidate-construction surface keeps the two concrete realization
obligations.  This is a coverage theorem only; it does not discharge the
obligations. -/
def SpectralMeasurePVMTargetAPICoverageReady : Prop :=
  spectralMeasurePVMTargetAPI.ready ∧
  spectralMeasurePVMTargetAPI.normalizationTag =
    SpectralMeasurePVMObligationTag.normalization ∧
  spectralMeasurePVMTargetAPI.projectionValuednessTag =
    SpectralMeasurePVMObligationTag.projectionValuedness ∧
  spectralMeasurePVMTargetAPI.countableAdditivityTag =
    SpectralMeasurePVMObligationTag.countableAdditivity ∧
  spectralMeasurePVMTargetAPI.spectralCompatibilityTag =
    SpectralMeasurePVMObligationTag.spectralTheoremCompatibility ∧
  spectralMeasurePVMCandidateConstruction.concreteSpectralMeasureObligation =
    SpectralMeasurePVMObligationTag.concreteSpectralMeasure ∧
  spectralMeasurePVMCandidateConstruction.concretePVMObligation =
    SpectralMeasurePVMObligationTag.concretePVM ∧
  SpectralMeasurePVMObligationMapReady

/-- The R4 target API coverage theorem is ready. -/
theorem spectral_measure_pvm_target_api_coverage_ready :
    SpectralMeasurePVMTargetAPICoverageReady := by
  exact ⟨
    spectral_measure_pvm_target_api_ready,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    spectral_measure_pvm_obligation_map_ready⟩

/-- The target API covers the normalization obligation tag. -/
theorem spectral_measure_pvm_target_api_covers_normalization :
    spectralMeasurePVMTargetAPI.normalizationTag =
      SpectralMeasurePVMObligationTag.normalization := by
  rfl

/-- The target API covers the projection-valuedness obligation tag. -/
theorem spectral_measure_pvm_target_api_covers_projection_valuedness :
    spectralMeasurePVMTargetAPI.projectionValuednessTag =
      SpectralMeasurePVMObligationTag.projectionValuedness := by
  rfl

/-- The target API covers the countable-additivity obligation tag. -/
theorem spectral_measure_pvm_target_api_covers_countable_additivity :
    spectralMeasurePVMTargetAPI.countableAdditivityTag =
      SpectralMeasurePVMObligationTag.countableAdditivity := by
  rfl

/-- The target API covers the spectral-theorem compatibility obligation tag. -/
theorem spectral_measure_pvm_target_api_covers_spectral_compatibility :
    spectralMeasurePVMTargetAPI.spectralCompatibilityTag =
      SpectralMeasurePVMObligationTag.spectralTheoremCompatibility := by
  rfl

/-- The candidate-construction surface carries the concrete spectral-measure obligation. -/
theorem spectral_measure_pvm_candidate_carries_concrete_spectral_measure_obligation :
    spectralMeasurePVMCandidateConstruction.concreteSpectralMeasureObligation =
      SpectralMeasurePVMObligationTag.concreteSpectralMeasure := by
  rfl

/-- The candidate-construction surface carries the concrete PVM obligation. -/
theorem spectral_measure_pvm_candidate_carries_concrete_pvm_obligation :
    spectralMeasurePVMCandidateConstruction.concretePVMObligation =
      SpectralMeasurePVMObligationTag.concretePVM := by
  rfl

/-- R4 target API coverage boundary.

All six R4 obligations are accounted for between the target API and the candidate
construction surface.  They remain registered obligations, not discharged PVM
axioms. -/
def SpectralMeasurePVMTargetAPICoverageBoundary : Prop :=
  SpectralMeasurePVMTargetAPICoverageReady ∧
  spectralMeasurePVMCandidateConstruction.ready ∧
  spectralMeasurePVMTargetAPI.ready

/-- The R4 target API coverage boundary is ready. -/
theorem spectral_measure_pvm_target_api_coverage_boundary_ready :
    SpectralMeasurePVMTargetAPICoverageBoundary := by
  exact ⟨
    spectral_measure_pvm_target_api_coverage_ready,
    spectral_measure_pvm_candidate_construction_ready,
    spectral_measure_pvm_target_api_ready⟩

end

end Theorem
end R4
end MGAP4D