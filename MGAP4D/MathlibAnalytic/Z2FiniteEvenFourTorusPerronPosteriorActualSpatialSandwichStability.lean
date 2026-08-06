import MGAP4D.MathlibAnalytic.FinitePositiveWeightParallelSpatialSandwichStability
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualParallelHammingContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace Z2PerronPosteriorActualHighTemperatureContinuationData

/-- Actual finite-volume spatial-sandwich stability.  When two hidden input
slices share common exterior data outside a finite interior set, the canonical
correct-marginal parallel posterior coupling has total coordinate disagreement
bounded by the interior volume times one half of the common actual row/column
barrier. -/
theorem parallelSpatialSandwichStability
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment leftHidden rightHidden :
      FiniteEvenFourTorusZ2SliceConfiguration H)
    (interior : Finset (FiniteEvenFourTorusSpatialLink H))
    (hOutside : FiniteProductAgreeOutside
      leftHidden rightHidden interior) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        (C.posteriorWeight_pos β hβ hβCutoff H environment)
        leftHidden rightHidden ≤
      ((2 : ℝ)⁻¹ *
        (C.continuationFamily β hβ hβCutoff).barrier) *
          (interior.card : ℝ) := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have hStability :=
    B.parallelSpatialSandwichStability
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      leftHidden rightHidden interior hOutside
  simpa [B] using hStability

/-- The actual spatial-sandwich factor is nonnegative. -/
theorem parallelSpatialSandwichFactor_nonneg
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff) :
    0 ≤ (2 : ℝ)⁻¹ *
      (C.continuationFamily β hβ hβCutoff).barrier :=
  C.parallelHammingContractionFactor_nonneg β hβ hβCutoff

/-- The actual spatial-sandwich factor is strictly below one. -/
theorem parallelSpatialSandwichFactor_lt_one
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff) :
    (2 : ℝ)⁻¹ *
      (C.continuationFamily β hβ hβCutoff).barrier < 1 :=
  C.parallelHammingContractionFactor_lt_one β hβ hβCutoff

end Z2PerronPosteriorActualHighTemperatureContinuationData

/-- Canonical all-volume actual spatial-sandwich stability throughout the
common high-temperature interval. -/
theorem finiteEvenFourTorusZ2PerronPosteriorActualSpatialSandwichStability
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤
        (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).couplingCutoff)
    (H : ℕ)
    (environment leftHidden rightHidden :
      FiniteEvenFourTorusZ2SliceConfiguration H)
    (interior : Finset (FiniteEvenFourTorusSpatialLink H))
    (hOutside : FiniteProductAgreeOutside
      leftHidden rightHidden interior) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        ((finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).posteriorWeight_pos
            β hβ hβCutoff H environment)
        leftHidden rightHidden ≤
      ((2 : ℝ)⁻¹ *
        ((finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).continuationFamily
            β hβ hβCutoff).barrier) *
          (interior.card : ℝ) := by
  exact
    Z2PerronPosteriorActualHighTemperatureContinuationData.parallelSpatialSandwichStability
      (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
        energyIdentity energyNontrivial hEnergy)
      β hβ hβCutoff H environment leftHidden rightHidden interior hOutside

end

end MathlibAnalytic
end MGAP4D
