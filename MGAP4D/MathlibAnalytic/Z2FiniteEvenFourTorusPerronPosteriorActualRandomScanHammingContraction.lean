import MGAP4D.MathlibAnalytic.FinitePositiveWeightBidirectionalRandomScanHammingContraction
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualParallelHammingContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForActualRandomScanCoupling
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

/-- The finite even-four-torus spatial-link coordinate set used by the actual
random-scan coupling is nonempty at every volume. -/
theorem finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan
    (H : ℕ) :
    0 < Fintype.card (FiniteEvenFourTorusSpatialLink H) :=
  Fintype.card_pos_iff.mpr inferInstance

namespace Z2PerronPosteriorActualHighTemperatureContinuationData

/-- Canonical correct-marginal common-target random-scan coupling for the
actual Perron-smoothed posterior at fixed observed boundary environment. -/
noncomputable def randomScanOverlapCouplingData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment leftHidden rightHidden :
      FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteRealCouplingData
      (finitePositiveWeightRandomScanProbabilityData
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        (C.posteriorWeight_pos β hβ hβCutoff H environment)
        (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
        leftHidden)
      (finitePositiveWeightRandomScanProbabilityData
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        (C.posteriorWeight_pos β hβ hβCutoff H environment)
        (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
        rightHidden) :=
  finitePositiveWeightRandomScanOverlapCouplingData
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
    (C.posteriorWeight_pos β hβ hβCutoff H environment)
    (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
    leftHidden rightHidden

/-- Actual common-target random-scan Hamming contraction rate.  This rate is
built from the overlap-coupling heat-bath margin and remains distinct from the
geometric one-slab transfer rate. -/
def randomScanHammingRate
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ) : ℝ :=
  1 -
    (1 - (2 : ℝ)⁻¹ *
      (C.continuationFamily β hβ hβCutoff).barrier) /
      (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ)

/-- The actual common-target random-scan Hamming rate is nonnegative. -/
theorem randomScanHammingRate_nonneg
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 ≤ C.randomScanHammingRate β hβ hβCutoff H := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    finitePositiveWeightBidirectionalRandomScanHammingRate_nonneg
      B (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
  simpa [randomScanHammingRate,
    finitePositiveWeightBidirectionalRandomScanHammingRate,
    finitePositiveWeightBidirectionalCouplingHeatBathGap, B] using h

/-- The actual common-target random-scan Hamming rate is strictly below one. -/
theorem randomScanHammingRate_lt_one
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    C.randomScanHammingRate β hβ hβCutoff H < 1 := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    finitePositiveWeightBidirectionalRandomScanHammingRate_lt_one
      B (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
  simpa [randomScanHammingRate,
    finitePositiveWeightBidirectionalRandomScanHammingRate,
    finitePositiveWeightBidirectionalCouplingHeatBathGap, B] using h

/-- Actual Perron-smoothed posterior random-scan overlap coupling contracts
expected Hamming distance at its explicit normalized heat-bath rate.  This is
not an identification with the geometric one-slab transfer gap. -/
theorem randomScanOverlapCoupling_expectedHamming_le_rate_mul
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment leftHidden rightHidden :
      FiniteEvenFourTorusZ2SliceConfiguration H) :
    (C.randomScanOverlapCouplingData
        β hβ hβCutoff H environment leftHidden rightHidden).expectedCost
      finiteProductHammingDistanceReal ≤
      C.randomScanHammingRate β hβ hβCutoff H *
        finiteProductHammingDistanceReal leftHidden rightHidden := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    B.randomScanOverlapCoupling_expectedHamming_le_rate_mul
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
      leftHidden rightHidden
  simpa [randomScanOverlapCouplingData, randomScanHammingRate,
    finitePositiveWeightBidirectionalRandomScanHammingRate,
    finitePositiveWeightBidirectionalCouplingHeatBathGap, B] using h

end Z2PerronPosteriorActualHighTemperatureContinuationData

end
end MathlibAnalytic
end MGAP4D
