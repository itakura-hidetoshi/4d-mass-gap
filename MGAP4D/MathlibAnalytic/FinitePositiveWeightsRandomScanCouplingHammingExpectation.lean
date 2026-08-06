import MGAP4D.MathlibAnalytic.FinitePositiveWeightsSingleSiteJointUpdateHammingCost
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- Expected cost of the common-target random-scan coupling is the uniform
average of the corresponding one-site joint-update expected costs. -/
theorem finitePositiveWeightsRandomScanJointCoupling_expectedCost_eq_average
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (hCard : 0 < Fintype.card ι)
    (leftInput rightInput : ι → G)
    (cost : (ι → G) → (ι → G) → ℝ) :
    (finitePositiveWeightsRandomScanJointCouplingData
        leftWeight rightWeight hLeftWeight hRightWeight hCard
        leftInput rightInput).expectedCost cost =
      (Fintype.card ι : ℝ)⁻¹ * ∑ target : ι,
        (finitePositiveWeightsSingleSiteJointUpdateCouplingData
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target).expectedCost cost := by
  classical
  let a : ℝ := (Fintype.card ι : ℝ)⁻¹
  unfold FiniteRealCouplingData.expectedCost
    finitePositiveWeightsRandomScanJointCouplingData
    finitePositiveWeightsRandomScanJointKernel
  change
    (∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
      (a * ∑ target : ι,
        finitePositiveWeightsSingleSiteJointUpdateKernel
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target leftOutput rightOutput) *
        cost leftOutput rightOutput) = _
  calc
    (∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
      (a * ∑ target : ι,
        finitePositiveWeightsSingleSiteJointUpdateKernel
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target leftOutput rightOutput) *
        cost leftOutput rightOutput) =
      ∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
        a * ((∑ target : ι,
          finitePositiveWeightsSingleSiteJointUpdateKernel
            leftWeight rightWeight hLeftWeight hRightWeight
            leftInput rightInput target leftOutput rightOutput) *
          cost leftOutput rightOutput) := by
      apply Finset.sum_congr rfl
      intro leftOutput _
      apply Finset.sum_congr rfl
      intro rightOutput _
      ring
    _ = a * ∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
        (∑ target : ι,
          finitePositiveWeightsSingleSiteJointUpdateKernel
            leftWeight rightWeight hLeftWeight hRightWeight
            leftInput rightInput target leftOutput rightOutput) *
          cost leftOutput rightOutput := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro leftOutput _
      rw [Finset.mul_sum]
    _ = a * ∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
        ∑ target : ι,
          finitePositiveWeightsSingleSiteJointUpdateKernel
            leftWeight rightWeight hLeftWeight hRightWeight
            leftInput rightInput target leftOutput rightOutput *
          cost leftOutput rightOutput := by
      congr 1
      apply Finset.sum_congr rfl
      intro leftOutput _
      apply Finset.sum_congr rfl
      intro rightOutput _
      rw [Finset.sum_mul]
    _ = a * ∑ target : ι, ∑ leftOutput : ι → G,
        ∑ rightOutput : ι → G,
          finitePositiveWeightsSingleSiteJointUpdateKernel
            leftWeight rightWeight hLeftWeight hRightWeight
            leftInput rightInput target leftOutput rightOutput *
          cost leftOutput rightOutput := by
      congr 1
      calc
        (∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
          ∑ target : ι,
            finitePositiveWeightsSingleSiteJointUpdateKernel
              leftWeight rightWeight hLeftWeight hRightWeight
              leftInput rightInput target leftOutput rightOutput *
            cost leftOutput rightOutput) =
          ∑ leftOutput : ι → G, ∑ target : ι,
            ∑ rightOutput : ι → G,
              finitePositiveWeightsSingleSiteJointUpdateKernel
                leftWeight rightWeight hLeftWeight hRightWeight
                leftInput rightInput target leftOutput rightOutput *
              cost leftOutput rightOutput := by
            apply Finset.sum_congr rfl
            intro leftOutput _
            rw [Finset.sum_comm]
        _ = ∑ target : ι, ∑ leftOutput : ι → G,
            ∑ rightOutput : ι → G,
              finitePositiveWeightsSingleSiteJointUpdateKernel
                leftWeight rightWeight hLeftWeight hRightWeight
                leftInput rightInput target leftOutput rightOutput *
              cost leftOutput rightOutput := by
            rw [Finset.sum_comm]
    _ = a * ∑ target : ι,
        (finitePositiveWeightsSingleSiteJointUpdateCouplingData
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target).expectedCost cost := by
      congr 1
      apply Finset.sum_congr rfl
      intro target _

/-- Exact expected Hamming cost of the common-target uniform random-scan
coupling: average the exact one-site away-cost plus overlap disagreement. -/
theorem finitePositiveWeightsRandomScanJointCoupling_expectedHamming_eq
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (hCard : 0 < Fintype.card ι)
    (leftInput rightInput : ι → G) :
    (finitePositiveWeightsRandomScanJointCouplingData
        leftWeight rightWeight hLeftWeight hRightWeight hCard
        leftInput rightInput).expectedCost finiteProductHammingDistanceReal =
      (Fintype.card ι : ℝ)⁻¹ * ∑ target : ι,
        (finiteProductHammingAwayReal leftInput rightInput target +
          (finitePositiveWeightsSingleSiteOverlapCouplingData
            leftWeight rightWeight hLeftWeight hRightWeight
            leftInput rightInput target).disagreementMass) := by
  rw [finitePositiveWeightsRandomScanJointCoupling_expectedCost_eq_average]
  congr 1
  apply Finset.sum_congr rfl
  intro target _
  exact
    finitePositiveWeightsSingleSiteJointUpdateCoupling_expectedHammingCost_eq
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput target

/-- Influence plus a cross-weight source controls the expected Hamming cost of
the common-target random-scan coupling. -/
theorem finitePositiveWeightsRandomScanJointCoupling_expectedHamming_le_influence_add_source
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (D : FinitePositiveWeightNonstrictL1MatrixData leftWeight)
    (sourceBound : ι → ℝ)
    (hCross : ∀ (environment : ι → G) (target : ι),
      finitePositiveWeightSingleSiteConditionalCrossL1
          leftWeight rightWeight environment target ≤ sourceBound target)
    (hCard : 0 < Fintype.card ι)
    (leftInput rightInput : ι → G) :
    (finitePositiveWeightsRandomScanJointCouplingData
        leftWeight rightWeight hLeftWeight hRightWeight hCard
        leftInput rightInput).expectedCost finiteProductHammingDistanceReal ≤
      (Fintype.card ι : ℝ)⁻¹ * ∑ target : ι,
        (finiteProductHammingAwayReal leftInput rightInput target +
          (2 : ℝ)⁻¹ *
            ((∑ source ∈ finiteProductDisagreementFinset
                leftInput rightInput, D.influence target source) +
              sourceBound target)) := by
  rw [finitePositiveWeightsRandomScanJointCoupling_expectedHamming_eq]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro target _
  exact add_le_add_left
    (finitePositiveWeightsSingleSiteOverlapCoupling_disagreementMass_le_half_mul_influence_add_source
      leftWeight rightWeight hLeftWeight hRightWeight D sourceBound hCross
      leftInput rightInput target)
    _

end
end MathlibAnalytic
end MGAP4D