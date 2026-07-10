import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparation
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedPublicConsumerAccessors
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Exact identification of the model first excitation for the complete
Yang--Mills direct bounded construction route.

The reconstructed model stores `firstExcitation` as the infimum of the nonzero
energy spectrum.  The exact-gap interval package proves that the same infimum
is the attained value `exactGapValueReal`.  This file identifies the two values,
transports the existing spectral-PVM witness to the exact-gap singleton, and
records the resulting unique least nonzero spectral energy.

All statements remain parametrized by the existing complete construction spine.
They do not assert an unconditional Yang--Mills construction or a final Clay
mass-gap theorem.
-/

/-- The model first excitation is exactly the repository exact-gap value. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_eq_exactGapValueReal
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.firstExcitation = exactGapValueReal := by
  calc
    S.definitionBridge.spine.model.firstExcitation =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) :=
      S.definitionBridge.spine.model.firstExcitation_is_sInf_nonvacuum
    _ = exactGapValueReal :=
      euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_sInf_eq_exactGap S

/-- The model first excitation belongs to the nonzero energy spectrum. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_mem_nonzeroSpectrum
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.firstExcitation ∈
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) := by
  exact ⟨
    S.definitionBridge.spine.model.firstExcitation_mem,
    by
      simpa using
        ne_of_gt S.definitionBridge.spine.model.firstExcitation_pos⟩

/-- The model first excitation is the least nonzero spectral energy. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_isLeast_nonzeroSpectrum
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    IsLeast
      (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
      S.definitionBridge.spine.model.firstExcitation := by
  rw [euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_eq_exactGapValueReal S]
  exact
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_isLeast_nonzeroSpectrum S

/-- The least nonzero spectral energy is unique and is the model first excitation. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_uniqueLeast
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃! E : ℝ,
      IsLeast
        (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) E := by
  let E₁ := S.definitionBridge.spine.model.firstExcitation
  have hE₁ :
      IsLeast
        (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) E₁ :=
    euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_isLeast_nonzeroSpectrum S
  refine ⟨E₁, hE₁, ?_⟩
  intro E hE
  exact le_antisymm (hE.2 hE₁.1) (hE₁.2 hE.1)

/-- The existing first-excitation PVM witness is supported at the exact gap. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactGapPVMWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({exactGapValueReal} : Set ℝ) := by
  rcases
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_firstExcitationWitness S with
    ⟨ψ, hψ⟩
  refine ⟨ψ, ?_⟩
  rw [euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_eq_exactGapValueReal S]
    at hψ
  exact hψ

/-- Strictly below the model first excitation, the spectrum is the vacuum only. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iio_firstExcitation
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.energySpectrum ∩
        Set.Iio S.definitionBridge.spine.model.firstExcitation =
      ({0} : Set ℝ) := by
  simpa [
    euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_eq_exactGapValueReal S] using
    euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iio_exactGap S

/-- At or below the model first excitation, the spectrum is exactly the vacuum
and first-excitation pair. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iic_firstExcitation
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.energySpectrum ∩
        Set.Iic S.definitionBridge.spine.model.firstExcitation =
      ({0, S.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  simpa [
    euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_eq_exactGapValueReal S] using
    euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iic_exactGap S

end

end MathlibAnalytic
end MGAP4D
