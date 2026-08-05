import MGAP4D.MathlibAnalytic.FinitePositiveWeightParallelSpatialSandwichStability
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualParallelHammingContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace Z2PerronPosteriorActualHighTemperatureContinuationData

/-- Actual spatial-sandwich stability under common exterior data.  If two
hidden slices agree outside a declared finite interior region, their canonical
correct-marginal parallel posterior coupling has total coordinate disagreement
bounded by the interior cardinality times one half of the common actual
row/column barrier. -/
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
    (hOutside : FiniteProductAgreeOutside leftHidden rightHidden interior) :
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

/-- The multiplier in the actual spatial-sandwich estimate is a strict
contraction factor, uniformly over the finite side, observed environment and
interior region. -/
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

/-- Top-level canonical actual spatial-sandwich estimate throughout the common
high-temperature interval constructed in PR #1390. -/
theorem finiteEvenFourTorusZ2PerronPosteriorActualParallelSpatialSandwichStability
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
    (hOutside : FiniteProductAgreeOutside leftHidden rightHidden interior) :
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
  exact parallelSpatialSandwichStability
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    β hβ hβCutoff H environment leftHidden rightHidden interior hOutside

end Z2PerronPosteriorActualHighTemperatureContinuationData

end

end MathlibAnalytic
end MGAP4D
