import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanHammingContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Canonical all-volume actual Perron-smoothed posterior common-target
random-scan overlap coupling. -/
noncomputable def
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanOverlapCouplingData
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
      FiniteEvenFourTorusZ2SliceConfiguration H) :=
  (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanOverlapCouplingData
    β hβ hβCutoff H environment leftHidden rightHidden

/-- Canonical all-volume actual random-scan Hamming contraction rate.  This
heat-bath coupling rate remains distinct from the geometric one-slab transfer
rate. -/
def finiteEvenFourTorusZ2PerronPosteriorActualRandomScanHammingRate
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤
        (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).couplingCutoff)
    (H : ℕ) : ℝ :=
  (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanHammingRate
    β hβ hβCutoff H

/-- The canonical all-volume actual random-scan Hamming rate is nonnegative. -/
theorem finiteEvenFourTorusZ2PerronPosteriorActualRandomScanHammingRate_nonneg
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤
        (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorActualRandomScanHammingRate
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanHammingRate_nonneg
        β hβ hβCutoff H environment

/-- The canonical all-volume actual random-scan Hamming rate is strictly below
one. -/
theorem finiteEvenFourTorusZ2PerronPosteriorActualRandomScanHammingRate_lt_one
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤
        (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanHammingRate
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H < 1 := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanHammingRate_lt_one
        β hβ hβCutoff H environment

/-- Canonical all-volume actual Perron-smoothed posterior random-scan overlap
coupling contracts expected Hamming distance at its explicit heat-bath rate. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanExpectedHamming_le
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
      FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2PerronPosteriorActualRandomScanOverlapCouplingData
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
      environment leftHidden rightHidden).expectedCost
        finiteProductHammingDistanceReal ≤
      finiteEvenFourTorusZ2PerronPosteriorActualRandomScanHammingRate
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H *
        finiteProductHammingDistanceReal leftHidden rightHidden := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanOverlapCoupling_expectedHamming_le_rate_mul
        β hβ hβCutoff H environment leftHidden rightHidden

end
end MathlibAnalytic
end MGAP4D
