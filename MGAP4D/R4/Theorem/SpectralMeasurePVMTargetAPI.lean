import MGAP4D.R4.Theorem.SpectralMeasurePVMObligationMap

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Minimal R4 target API for the spectral-measure/PVM stage.

This is an API skeleton for a set-indexed spectral-measure/PVM target.  It does
not assert exact atoms, positive weights, countable additivity, or full
projection-valuedness.  Those remain obligations recorded by the R4 obligation
map or later R6/R7 stages. -/
structure SpectralMeasurePVMTargetAPI where
  setIndex : Type
  projectionTarget : Type
  spectralMeasureCandidate : setIndex → projectionTarget
  pvmCandidate : setIndex → projectionTarget
  sourceIsRealBorelLike : Prop
  targetIsProjectionLike : Prop
  normalizationTag : SpectralMeasurePVMObligationTag
  projectionValuednessTag : SpectralMeasurePVMObligationTag
  countableAdditivityTag : SpectralMeasurePVMObligationTag
  spectralCompatibilityTag : SpectralMeasurePVMObligationTag

/-- Concrete R4 target API skeleton.

The projection target is deliberately `PUnit`; this witnesses only the existence
of a target API shell, not a mathematical PVM. -/
def spectralMeasurePVMTargetAPI : SpectralMeasurePVMTargetAPI :=
  { setIndex := Set ℝ
    projectionTarget := PUnit
    spectralMeasureCandidate := fun _ => PUnit.unit
    pvmCandidate := fun _ => PUnit.unit
    sourceIsRealBorelLike := True
    targetIsProjectionLike := True
    normalizationTag := SpectralMeasurePVMObligationTag.normalization
    projectionValuednessTag := SpectralMeasurePVMObligationTag.projectionValuedness
    countableAdditivityTag := SpectralMeasurePVMObligationTag.countableAdditivity
    spectralCompatibilityTag := SpectralMeasurePVMObligationTag.spectralTheoremCompatibility }

/-- Readiness predicate for the R4 target API skeleton. -/
def SpectralMeasurePVMTargetAPI.ready (A : SpectralMeasurePVMTargetAPI) : Prop :=
  SpectralMeasurePVMObligationMapReady ∧
  A.setIndex = Set ℝ ∧
  A.sourceIsRealBorelLike ∧
  A.targetIsProjectionLike ∧
  A.normalizationTag = SpectralMeasurePVMObligationTag.normalization ∧
  A.projectionValuednessTag = SpectralMeasurePVMObligationTag.projectionValuedness ∧
  A.countableAdditivityTag = SpectralMeasurePVMObligationTag.countableAdditivity ∧
  A.spectralCompatibilityTag = SpectralMeasurePVMObligationTag.spectralTheoremCompatibility

/-- The R4 target API skeleton is ready. -/
theorem spectral_measure_pvm_target_api_ready :
    spectralMeasurePVMTargetAPI.ready := by
  exact ⟨
    spectral_measure_pvm_obligation_map_ready,
    rfl,
    trivial,
    trivial,
    rfl,
    rfl,
    rfl,
    rfl⟩

/-- The R4 target API uses real-set indexing. -/
theorem spectral_measure_pvm_target_api_set_index :
    spectralMeasurePVMTargetAPI.setIndex = Set ℝ := by
  rfl

/-- The R4 target API carries a spectral-measure candidate map. -/
theorem spectral_measure_pvm_target_api_has_spectral_measure_candidate :
    ∃ f : spectralMeasurePVMTargetAPI.setIndex → spectralMeasurePVMTargetAPI.projectionTarget,
      f = spectralMeasurePVMTargetAPI.spectralMeasureCandidate := by
  exact ⟨spectralMeasurePVMTargetAPI.spectralMeasureCandidate, rfl⟩

/-- The R4 target API carries a PVM candidate map. -/
theorem spectral_measure_pvm_target_api_has_pvm_candidate :
    ∃ f : spectralMeasurePVMTargetAPI.setIndex → spectralMeasurePVMTargetAPI.projectionTarget,
      f = spectralMeasurePVMTargetAPI.pvmCandidate := by
  exact ⟨spectralMeasurePVMTargetAPI.pvmCandidate, rfl⟩

/-- R4 target API boundary.

The target API exists and is aligned with the R4 obligation map.  It remains an
API skeleton rather than a full PVM theorem. -/
def SpectralMeasurePVMTargetAPIBoundary : Prop :=
  spectralMeasurePVMTargetAPI.ready ∧
  SpectralMeasurePVMObligationMapReady

/-- The R4 target API boundary is ready. -/
theorem spectral_measure_pvm_target_api_boundary_ready :
    SpectralMeasurePVMTargetAPIBoundary := by
  exact ⟨spectral_measure_pvm_target_api_ready, spectral_measure_pvm_obligation_map_ready⟩

end

end Theorem
end R4
end MGAP4D