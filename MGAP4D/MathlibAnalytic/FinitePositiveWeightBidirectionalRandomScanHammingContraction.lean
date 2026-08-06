import MGAP4D.MathlibAnalytic.FiniteProductHammingAwayAverage
import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalL1Telescoping
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- Same-weight specialization of the common-target exact random-scan
coupling. -/
noncomputable def finitePositiveWeightRandomScanOverlapCouplingData
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (leftInput rightInput : ι → G) :
    FiniteRealCouplingData
      (finitePositiveWeightRandomScanProbabilityData
        weight hweight hCard leftInput)
      (finitePositiveWeightRandomScanProbabilityData
        weight hweight hCard rightInput) :=
  finitePositiveWeightsRandomScanJointCouplingData
    weight weight hweight hweight hCard leftInput rightInput

/-- Strict one-update margin of the overlap-coupling Hamming estimate.  This
is a random-scan coupling quantity and is not the geometric one-slab transfer
gap. -/
def finitePositiveWeightBidirectionalCouplingHeatBathGap
    {ι G : Type} [DecidableEq ι] [Fintype ι] [Fintype G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight) : ℝ :=
  1 - (2 : ℝ)⁻¹ * B.coefficient

/-- The overlap-coupling heat-bath margin is positive. -/
theorem finitePositiveWeightBidirectionalCouplingHeatBathGap_pos
    {ι G : Type} [DecidableEq ι] [Fintype ι] [Fintype G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight) :
    0 < finitePositiveWeightBidirectionalCouplingHeatBathGap B := by
  exact sub_pos.mpr B.halfCoefficient_lt_one

/-- Normalized common-target random-scan Hamming rate. -/
def finitePositiveWeightBidirectionalRandomScanHammingRate
    {ι G : Type} [DecidableEq ι] [Fintype ι] [Fintype G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight) : ℝ :=
  1 - finitePositiveWeightBidirectionalCouplingHeatBathGap B /
    (Fintype.card ι : ℝ)

/-- For a nonempty coordinate type, the coupling random-scan rate is
nonnegative. -/
theorem finitePositiveWeightBidirectionalRandomScanHammingRate_nonneg
    {ι G : Type} [DecidableEq ι] [Fintype ι] [Fintype G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι) :
    0 ≤ finitePositiveWeightBidirectionalRandomScanHammingRate B := by
  have hCardPos : (0 : ℝ) < (Fintype.card ι : ℝ) :=
    Nat.cast_pos.mpr hCard
  have hCardOne : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hCard
  have hGapLeOne :
      finitePositiveWeightBidirectionalCouplingHeatBathGap B ≤ 1 := by
    unfold finitePositiveWeightBidirectionalCouplingHeatBathGap
    linarith [B.halfCoefficient_nonneg]
  have hGapLeCard :
      finitePositiveWeightBidirectionalCouplingHeatBathGap B ≤
        (Fintype.card ι : ℝ) :=
    le_trans hGapLeOne hCardOne
  have hDivLeOne :
      finitePositiveWeightBidirectionalCouplingHeatBathGap B /
          (Fintype.card ι : ℝ) ≤ 1 :=
    (div_le_one hCardPos).2 hGapLeCard
  unfold finitePositiveWeightBidirectionalRandomScanHammingRate
  linarith

/-- For a nonempty coordinate type, the coupling random-scan rate is strictly
below one. -/
theorem finitePositiveWeightBidirectionalRandomScanHammingRate_lt_one
    {ι G : Type} [DecidableEq ι] [Fintype ι] [Fintype G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι) :
    finitePositiveWeightBidirectionalRandomScanHammingRate B < 1 := by
  have hCardPos : (0 : ℝ) < (Fintype.card ι : ℝ) :=
    Nat.cast_pos.mpr hCard
  have hQuotPos :
      0 < finitePositiveWeightBidirectionalCouplingHeatBathGap B /
        (Fintype.card ι : ℝ) :=
    div_pos
      (finitePositiveWeightBidirectionalCouplingHeatBathGap_pos B)
      hCardPos
  unfold finitePositiveWeightBidirectionalRandomScanHammingRate
  linarith

/-- Exact expected-Hamming decomposition of the same-weight common-target
random-scan coupling into the deterministic Hamming-away average and the
parallel overlap disagreement. -/
theorem finitePositiveWeightRandomScanOverlapCoupling_expectedHamming_eq
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (leftInput rightInput : ι → G) :
    (finitePositiveWeightRandomScanOverlapCouplingData
        weight hweight hCard leftInput rightInput).expectedCost
      finiteProductHammingDistanceReal =
      (1 - (Fintype.card ι : ℝ)⁻¹) *
          finiteProductHammingDistanceReal leftInput rightInput +
        (Fintype.card ι : ℝ)⁻¹ *
          finitePositiveWeightParallelTotalCoordinateDisagreement
            weight hweight leftInput rightInput := by
  have h :=
    finitePositiveWeightsRandomScanJointCoupling_expectedHamming_eq
      weight weight hweight hweight hCard leftInput rightInput
  rw [Finset.sum_add_distrib, mul_add] at h
  rw [finiteProductHammingAwayReal_average_eq_one_sub_inv_mul_hamming
    hCard leftInput rightInput] at h
  simpa [finitePositiveWeightRandomScanOverlapCouplingData,
    finitePositiveWeightParallelTotalCoordinateDisagreement,
    finitePositiveWeightParallelDisagreementProfile,
    finitePositiveWeightsSingleSiteOverlapCouplingData,
    finitePositiveWeightSingleSiteOverlapCouplingData] using h

/-- Bidirectional Dobrushin contraction of expected Hamming distance under the
canonical same-target random-scan overlap coupling.  The rate is the
random-scan coupling rate, not the geometric one-slab transfer rate. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScanOverlapCoupling_expectedHamming_le_rate_mul
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (leftInput rightInput : ι → G) :
    (finitePositiveWeightRandomScanOverlapCouplingData
        weight hweight hCard leftInput rightInput).expectedCost
      finiteProductHammingDistanceReal ≤
      finitePositiveWeightBidirectionalRandomScanHammingRate B *
        finiteProductHammingDistanceReal leftInput rightInput := by
  have hParallel :=
    B.parallelTotalCoordinateDisagreement_le_halfCoefficient_mul_hamming
      hweight leftInput rightInput
  have hInvNonneg :
      0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hCard)
  rw [finitePositiveWeightRandomScanOverlapCoupling_expectedHamming_eq]
  calc
    (1 - (Fintype.card ι : ℝ)⁻¹) *
          finiteProductHammingDistanceReal leftInput rightInput +
        (Fintype.card ι : ℝ)⁻¹ *
          finitePositiveWeightParallelTotalCoordinateDisagreement
            weight hweight leftInput rightInput ≤
      (1 - (Fintype.card ι : ℝ)⁻¹) *
          finiteProductHammingDistanceReal leftInput rightInput +
        (Fintype.card ι : ℝ)⁻¹ *
          (((2 : ℝ)⁻¹ * B.coefficient) *
            finiteProductHammingDistanceReal leftInput rightInput) :=
      add_le_add_left
        (mul_le_mul_of_nonneg_left hParallel hInvNonneg) _
    _ = finitePositiveWeightBidirectionalRandomScanHammingRate B *
        finiteProductHammingDistanceReal leftInput rightInput := by
      unfold finitePositiveWeightBidirectionalRandomScanHammingRate
        finitePositiveWeightBidirectionalCouplingHeatBathGap
      field_simp [hn]
      ring

end
end MathlibAnalytic
end MGAP4D
