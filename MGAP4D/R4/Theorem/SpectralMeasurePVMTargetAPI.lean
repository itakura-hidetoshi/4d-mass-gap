import MGAP4D.R4.Theorem.SpectralMeasurePVMObligationMap

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

structure SpectralMeasurePVMProjectionTargetSkeleton where
  obligationTag : SpectralMeasurePVMObligationTag
  stageLabel : String

abbrev SpectralMeasurePVMTargetSetIndex : Type := Set ℝ

abbrev SpectralMeasurePVMTargetProjectionType : Type :=
  SpectralMeasurePVMProjectionTargetSkeleton

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

def spectralMeasurePVMTargetAPISpectralMeasureCandidate :
    SpectralMeasurePVMTargetProjectionType :=
  { obligationTag := SpectralMeasurePVMObligationTag.spectralTheoremCompatibility
    stageLabel := "spectral-measure-candidate-shell" }

def spectralMeasurePVMTargetAPIPVMCandidate :
    SpectralMeasurePVMTargetProjectionType :=
  { obligationTag := SpectralMeasurePVMObligationTag.projectionValuedness
    stageLabel := "pvm-candidate-shell" }

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

def SpectralMeasurePVMTargetAPI.ready (A : SpectralMeasurePVMTargetAPI) : Prop :=
  SpectralMeasurePVMObligationMapReady ∧
  A.setIndex = SpectralMeasurePVMTargetSetIndex ∧
  A.projectionTarget = SpectralMeasurePVMTargetProjectionType ∧
  A.sourceIsRealBorelLike ∧
  A.targetIsProjectionShell ∧
  A.normalizationTag = SpectralMeasurePVMObligationTag.normalization ∧
  A.projectionValuednessTag = SpectralMeasurePVMObligationTag.projectionValuedness ∧
  A.countableAdditivityTag = SpectralMeasurePVMObligationTag.countableAdditivity ∧
  A.spectralCompatibilityTag = SpectralMeasurePVMObligationTag.spectralTheoremCompatibility

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

theorem spectral_measure_pvm_target_api_set_index :
    spectralMeasurePVMTargetAPI.setIndex = SpectralMeasurePVMTargetSetIndex := by
  rfl

theorem spectral_measure_pvm_target_api_has_spectral_measure_candidate :
    ∃ f : spectralMeasurePVMTargetAPI.setIndex → spectralMeasurePVMTargetAPI.projectionTarget,
      f = spectralMeasurePVMTargetAPI.spectralMeasureCandidate := by
  exact ⟨spectralMeasurePVMTargetAPI.spectralMeasureCandidate, rfl⟩

theorem spectral_measure_pvm_target_api_has_pvm_candidate :
    ∃ f : spectralMeasurePVMTargetAPI.setIndex → spectralMeasurePVMTargetAPI.projectionTarget,
      f = spectralMeasurePVMTargetAPI.pvmCandidate := by
  exact ⟨spectralMeasurePVMTargetAPI.pvmCandidate, rfl⟩

def SpectralMeasurePVMTargetAPIBoundary : Prop :=
  spectralMeasurePVMTargetAPI.ready ∧
  SpectralMeasurePVMObligationMapReady

theorem spectral_measure_pvm_target_api_boundary_ready :
    SpectralMeasurePVMTargetAPIBoundary := by
  exact ⟨spectral_measure_pvm_target_api_ready, spectral_measure_pvm_obligation_map_ready⟩

end

end Theorem
end R4
end MGAP4D
