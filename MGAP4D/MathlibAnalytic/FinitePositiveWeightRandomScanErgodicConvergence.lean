import MGAP4D.MathlibAnalytic.FiniteRealProbabilityCouplingTotalVariation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Under strict bidirectional random-scan contraction, the unhalved `L¹`
distance from every finite initial law to the stationary normalized Gibbs law
tends to zero.  This is an auxiliary heat-bath ergodic convergence theorem and
does not identify its rate with a geometric one-slab transfer gap. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScanIterate_l1Distance_stationary_tendsto_zero
    {ι A : Type} [DecidableEq ι] [DecidableEq A]
    [Fintype ι] [Fintype A] [Nonempty A]
    {weight : (ι → A) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ X : ι → A, 0 < weight X)
    (hCard : 0 < Fintype.card ι)
    (initialLaw : FiniteRealProbabilityData (ι → A)) :
    Tendsto
      (fun n : ℕ =>
        (finiteRealProbabilityKernelIterateData
          (finitePositiveWeightRandomScanProbabilityData
            weight hweight hCard)
          n initialLaw).l1Distance
            (finitePositiveWeightGlobalProbabilityData weight hweight))
      atTop (nhds 0) := by
  let rate := finitePositiveWeightBidirectionalRandomScanHammingRate B
  have hRateNonneg : 0 ≤ rate := by
    simpa [rate] using
      finitePositiveWeightBidirectionalRandomScanHammingRate_nonneg B hCard
  have hRateLtOne : rate < 1 := by
    simpa [rate] using
      finitePositiveWeightBidirectionalRandomScanHammingRate_lt_one B hCard
  have hPow :
      Tendsto (fun n : ℕ => rate ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hRateNonneg hRateLtOne
  have hCardEnvelope :
      Tendsto
        (fun n : ℕ => rate ^ n * (Fintype.card ι : ℝ))
        atTop (nhds 0) := by
    simpa using hPow.mul_const (Fintype.card ι : ℝ)
  have hTwo :
      Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hEnvelope :
      Tendsto
        (fun n : ℕ => 2 *
          (rate ^ n * (Fintype.card ι : ℝ)))
        atTop (nhds 0) := by
    simpa using hTwo.mul hCardEnvelope
  exact squeeze_zero_norm
    (fun n => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · simpa [rate] using
          B.randomScanIterate_l1Distance_stationary_le_two_mul_pow_mul_card
            hweight hCard initialLaw n
      · exact FiniteRealProbabilityData.l1Distance_nonneg _ _)
    hEnvelope

/-- Under strict bidirectional random-scan contraction, the standard
total-variation distance from every finite initial law to the stationary
normalized Gibbs law tends to zero. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScanIterate_totalVariationDistance_stationary_tendsto_zero
    {ι A : Type} [DecidableEq ι] [DecidableEq A]
    [Fintype ι] [Fintype A] [Nonempty A]
    {weight : (ι → A) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ X : ι → A, 0 < weight X)
    (hCard : 0 < Fintype.card ι)
    (initialLaw : FiniteRealProbabilityData (ι → A)) :
    Tendsto
      (fun n : ℕ =>
        (finiteRealProbabilityKernelIterateData
          (finitePositiveWeightRandomScanProbabilityData
            weight hweight hCard)
          n initialLaw).totalVariationDistance
            (finitePositiveWeightGlobalProbabilityData weight hweight))
      atTop (nhds 0) := by
  let rate := finitePositiveWeightBidirectionalRandomScanHammingRate B
  have hRateNonneg : 0 ≤ rate := by
    simpa [rate] using
      finitePositiveWeightBidirectionalRandomScanHammingRate_nonneg B hCard
  have hRateLtOne : rate < 1 := by
    simpa [rate] using
      finitePositiveWeightBidirectionalRandomScanHammingRate_lt_one B hCard
  have hPow :
      Tendsto (fun n : ℕ => rate ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hRateNonneg hRateLtOne
  have hEnvelope :
      Tendsto
        (fun n : ℕ => rate ^ n * (Fintype.card ι : ℝ))
        atTop (nhds 0) := by
    simpa using hPow.mul_const (Fintype.card ι : ℝ)
  exact squeeze_zero_norm
    (fun n => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · simpa [rate] using
          B.randomScanIterate_totalVariationDistance_stationary_le_pow_mul_card
            hweight hCard initialLaw n
      · exact FiniteRealProbabilityData.totalVariationDistance_nonneg _ _)
    hEnvelope

end
end MathlibAnalytic
end MGAP4D
