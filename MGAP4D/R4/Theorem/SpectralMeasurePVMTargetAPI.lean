import MGAP4D.R4.Theorem.SpectralMeasurePVMObligationMap

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Explicit skeletal projection target for the R4 target API.

This replaces the old unit carrier with a named target shell.  It is still not a
mathematical PVM, but it is no longer an anonymous `PUnit` placeholder. -/
structure SpectralMeasurePVMProjectionTargetSkeleton where
  obligationTag : SpectralMeasurePVMObligationTag
  stageLabel : String

/-- The source index used by the R4 target API. -/
abbrev SpectralMeasurePVMTargetSetIndex : Type := Set ℝ

/-- The projection target type used by the R4 target API shell. -/
abbrev SpectralMeasurePVMTargetProjectionType : Type :=
  SpectralMeasurePVMProjectionTargetSkeleton

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
  sourceIsRealBorelLike : setIndex = SpectralMeasurePVMTargetSetIndex
  targetIsProjectionShell : projectionTarget = SpectralMeasurePVMTargetProjectionType
  normalizationTag : SpectralMeasurePVMObligationTag
  projectionValuednessTag : SpectralMeasurePVMObligationTag
  countableAdditivityTag : SpectralMeasurePVMObligationTag
  spectralCompatibilityTag : SpectralMeasurePVMObligationTag

/-- Candidate object for the spectral-measure slot of the target API shell. -/
def spectralMeasurePVMTargetAPISpectralMeasureCandidate :
    SpectralMeasurePVMTargetProjectionType :=
  { obligationTag := SpectralMeasurePVMObligationTag.spectralTheoremCompatibility
    stageLabel := "spectral-measure-candidate-shell" }

/-- Candidate object for the PVM slot of the target API shell. -/
def spectralMeasurePVMTargetAPIPVMCandidate :
    SpectralMeasurePVMTargetProjectionType :=
  { obligationTag := SpectralMeasurePVMObligationTag.projectionValuedness
    stageLabel := "pvm-candidate-shell" }

/-- Concrete R4 target API skeleton.

The projection target is a named skeletal target shell.  This witnesses only the
existence of a target API shell, not a mathematical PVM. -/
def spectralMeasurePVMTargetAPI : SpectralMeasurePVMTargetAPI :=
  { setIndex := SpectralMeasurePVMTargetSetIndex
    projectionTarget := SpectralMeasurePVMTargetProjectionType
    spectralMeasureCandidate := fun _ => spectralMeasurePVMTargetAPISpectralMeasureCandidate
    pvmCandidate := fun _ => spectralMeasurePVMTargetAPIPVMCandidate
    sourceIsRealBorelLike := rfl
    targetIsProjectionShell := rfl
    normalizationTag := SpectralMeasurePVMObligationTag.normalization
    projectionValuednessTag := SpectralMeasurePVMObligationTag.projectionValuedness
    countableAdditivityTag := SpectralMeasurePVMObligationTag.countableAdditivity
    spectralCompatibilityTag := SpectralMeasurePVMObligationTag.spectralTheoremCompatibility }

/-- Readiness predicate for the R4 target API skeleton. -/
def SpectralMeasurePVMTargetAPI.ready (A : SpectralMeasurePVMTargetAPI) : Prop :=
  SpectralMeasurePVMObligationMapReady ∧
  A.setIndex = SpectralMeasurePVMTargetSetIndex ∧
  A.projectionTarget = SpectralMeasurePVMTargetProjectionType ∧
  A.sourceIsRealBorelLike = (by rfl) ∧
  A.targetIsProjectionShell = (by rfl) ∧
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
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl⟩

/-- The R4 target API uses real-set indexing. -/
theorem spectral_measure_pvm_target_api_set_index :
    spectralMeasurePVMTargetAPI.setIndex = SpectralMeasurePVMTargetSetIndex := by
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
