import MGAP4D.MathlibAnalytic.FinitePositiveWeightParallelCouplingHammingExpectation
import MGAP4D.MathlibAnalytic.FinitePositiveWeightsRandomScanOverlapCoupling
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityMixtureCouplingCost
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- Updating the same coordinate on two configurations replaces exactly that
coordinate's Hamming indicator and leaves every other coordinate unchanged. -/
theorem finiteProductHammingDistanceReal_update_eq_sum_indicator
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι]
    (leftInput rightInput : ι → G) (target : ι) (g h : G) :
    finiteProductHammingDistanceReal
        (Function.update leftInput target g)
        (Function.update rightInput target h) =
      ∑ i : ι, if i = target then
        finitePairDisagreementIndicator (g, h)
      else finitePairDisagreementIndicator (leftInput i, rightInput i) := by
  calc
    finiteProductHammingDistanceReal
        (Function.update leftInput target g)
        (Function.update rightInput target h) =
      finitePairHammingCost (fun i =>
        (Function.update leftInput target g i,
          Function.update rightInput target h i)) := by
      symm
      exact finitePairHammingCost_eq_finiteProductHammingDistanceReal _
    _ = ∑ i : ι, if i = target then
        finitePairDisagreementIndicator (g, h)
      else finitePairDisagreementIndicator (leftInput i, rightInput i) := by
      unfold finitePairHammingCost
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = target
      · subst i
        simp
      · simp [Function.update, hi]

/-- Expectation under the pushed-forward one-site joint update kernel reduces
to expectation under the original one-site overlap coupling. -/
theorem finitePositiveWeightsSingleSiteJointUpdateKernel_expectation
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput : ι → G) (target : ι)
    (cost : (ι → G) → (ι → G) → ℝ) :
    (∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
      finitePositiveWeightsSingleSiteJointUpdateKernel
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target leftOutput rightOutput *
        cost leftOutput rightOutput) =
      ∑ g : G, ∑ h : G,
        (finitePositiveWeightsSingleSiteOverlapCouplingData
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target).joint g h *
        cost (Function.update leftInput target g)
          (Function.update rightInput target h) := by
  classical
  let C := finitePositiveWeightsSingleSiteOverlapCouplingData
    leftWeight rightWeight hLeftWeight hRightWeight
    leftInput rightInput target
  unfold finitePositiveWeightsSingleSiteJointUpdateKernel
  simp_rw [Finset.sum_mul]
  calc
    (∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
      ∑ g : G, ∑ h : G,
        (if Function.update leftInput target g = leftOutput ∧
            Function.update rightInput target h = rightOutput then
          C.joint g h else 0) * cost leftOutput rightOutput) =
      ∑ leftOutput : ι → G, ∑ g : G,
        ∑ rightOutput : ι → G, ∑ h : G,
          (if Function.update leftInput target g = leftOutput ∧
              Function.update rightInput target h = rightOutput then
            C.joint g h else 0) * cost leftOutput rightOutput := by
      apply Finset.sum_congr rfl
      intro leftOutput _
      rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ leftOutput : ι → G,
        ∑ rightOutput : ι → G, ∑ h : G,
          (if Function.update leftInput target g = leftOutput ∧
              Function.update rightInput target h = rightOutput then
            C.joint g h else 0) * cost leftOutput rightOutput := by
      rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ leftOutput : ι → G, ∑ h : G,
        ∑ rightOutput : ι → G,
          (if Function.update leftInput target g = leftOutput ∧
              Function.update rightInput target h = rightOutput then
            C.joint g h else 0) * cost leftOutput rightOutput := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro leftOutput _
      rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ h : G, ∑ leftOutput : ι → G,
        ∑ rightOutput : ι → G,
          (if Function.update leftInput target g = leftOutput ∧
              Function.update rightInput target h = rightOutput then
            C.joint g h else 0) * cost leftOutput rightOutput := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ h : G,
        C.joint g h *
          cost (Function.update leftInput target g)
            (Function.update rightInput target h) := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro h _
      simp

/-- Exact expected Hamming decomposition for one common-coordinate update:
the updated coordinate contributes the overlap-coupling disagreement mass,
while every other coordinate retains its original disagreement indicator. -/
theorem finitePositiveWeightsSingleSiteJointUpdate_expectedHamming_eq
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput : ι → G) (target : ι) :
    (finitePositiveWeightsSingleSiteJointUpdateCouplingData
        leftWeight rightWeight hLeftWeight hRightWeight
        leftInput rightInput target).expectedCost
      finiteProductHammingDistanceReal =
      ∑ i : ι, if i = target then
        (finitePositiveWeightsSingleSiteOverlapCouplingData
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target).disagreementMass
      else finitePairDisagreementIndicator (leftInput i, rightInput i) := by
  classical
  let C := finitePositiveWeightsSingleSiteOverlapCouplingData
    leftWeight rightWeight hLeftWeight hRightWeight
    leftInput rightInput target
  unfold FiniteRealCouplingData.expectedCost
    finitePositiveWeightsSingleSiteJointUpdateCouplingData
  rw [finitePositiveWeightsSingleSiteJointUpdateKernel_expectation]
  simp_rw [finiteProductHammingDistanceReal_update_eq_sum_indicator]
  simp_rw [Finset.mul_sum]
  calc
    (∑ g : G, ∑ h : G, ∑ i : ι,
      C.joint g h *
        (if i = target then finitePairDisagreementIndicator (g, h)
        else finitePairDisagreementIndicator (leftInput i, rightInput i))) =
      ∑ g : G, ∑ i : ι, ∑ h : G,
        C.joint g h *
          (if i = target then finitePairDisagreementIndicator (g, h)
          else finitePairDisagreementIndicator (leftInput i, rightInput i)) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ g : G, ∑ h : G,
        C.joint g h *
          (if i = target then finitePairDisagreementIndicator (g, h)
          else finitePairDisagreementIndicator (leftInput i, rightInput i)) := by
      rw [Finset.sum_comm]
    _ = ∑ i : ι, if i = target then C.disagreementMass
        else finitePairDisagreementIndicator (leftInput i, rightInput i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = target
      · subst i
        simp only [if_pos]
        have hDisagreement := C.pairDisagreementExpectation_eq_disagreementMass
        rw [Fintype.sum_prod_type] at hDisagreement
        exact hDisagreement
      · simp only [if_neg hi]
        rw [← Finset.sum_mul, ← Finset.sum_mul, C.totalMass_eq_one, one_mul]

/-- Exact coordinatewise expected-Hamming decomposition for the common-target
uniform random-scan coupling. -/
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
      (Fintype.card ι : ℝ)⁻¹ * ∑ target : ι, ∑ i : ι,
        if i = target then
          (finitePositiveWeightsSingleSiteOverlapCouplingData
            leftWeight rightWeight hLeftWeight hRightWeight
            leftInput rightInput target).disagreementMass
        else finitePairDisagreementIndicator (leftInput i, rightInput i) := by
  classical
  unfold FiniteRealCouplingData.expectedCost
    finitePositiveWeightsRandomScanJointCouplingData
    finitePositiveWeightsRandomScanJointKernel
  calc
    (∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
      ((Fintype.card ι : ℝ)⁻¹ * ∑ target : ι,
        finitePositiveWeightsSingleSiteJointUpdateKernel
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target leftOutput rightOutput) *
        finiteProductHammingDistanceReal leftOutput rightOutput) =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
          (∑ target : ι,
            finitePositiveWeightsSingleSiteJointUpdateKernel
              leftWeight rightWeight hLeftWeight hRightWeight
              leftInput rightInput target leftOutput rightOutput) *
            finiteProductHammingDistanceReal leftOutput rightOutput := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro leftOutput _
      apply Finset.sum_congr rfl
      intro rightOutput _
      ring
    _ = (Fintype.card ι : ℝ)⁻¹ *
        ∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
          ∑ target : ι,
            finitePositiveWeightsSingleSiteJointUpdateKernel
              leftWeight rightWeight hLeftWeight hRightWeight
              leftInput rightInput target leftOutput rightOutput *
            finiteProductHammingDistanceReal leftOutput rightOutput := by
      congr 1
      apply Finset.sum_congr rfl
      intro leftOutput _
      apply Finset.sum_congr rfl
      intro rightOutput _
      rw [Finset.sum_mul]
    _ = (Fintype.card ι : ℝ)⁻¹ * ∑ target : ι,
        ∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
          finitePositiveWeightsSingleSiteJointUpdateKernel
            leftWeight rightWeight hLeftWeight hRightWeight
            leftInput rightInput target leftOutput rightOutput *
          finiteProductHammingDistanceReal leftOutput rightOutput := by
      congr 1
      calc
        (∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
          ∑ target : ι,
            finitePositiveWeightsSingleSiteJointUpdateKernel
              leftWeight rightWeight hLeftWeight hRightWeight
              leftInput rightInput target leftOutput rightOutput *
            finiteProductHammingDistanceReal leftOutput rightOutput) =
          ∑ leftOutput : ι → G, ∑ target : ι,
            ∑ rightOutput : ι → G,
              finitePositiveWeightsSingleSiteJointUpdateKernel
                leftWeight rightWeight hLeftWeight hRightWeight
                leftInput rightInput target leftOutput rightOutput *
              finiteProductHammingDistanceReal leftOutput rightOutput := by
            apply Finset.sum_congr rfl
            intro leftOutput _
            rw [Finset.sum_comm]
        _ = ∑ target : ι, ∑ leftOutput : ι → G,
            ∑ rightOutput : ι → G,
              finitePositiveWeightsSingleSiteJointUpdateKernel
                leftWeight rightWeight hLeftWeight hRightWeight
                leftInput rightInput target leftOutput rightOutput *
              finiteProductHammingDistanceReal leftOutput rightOutput := by
            rw [Finset.sum_comm]
    _ = (Fintype.card ι : ℝ)⁻¹ * ∑ target : ι, ∑ i : ι,
        if i = target then
          (finitePositiveWeightsSingleSiteOverlapCouplingData
            leftWeight rightWeight hLeftWeight hRightWeight
            leftInput rightInput target).disagreementMass
        else finitePairDisagreementIndicator (leftInput i, rightInput i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro target _
      exact finitePositiveWeightsSingleSiteJointUpdate_expectedHamming_eq
        leftWeight rightWeight hLeftWeight hRightWeight
        leftInput rightInput target

/-- Influence plus a cross-weight source controls the expected Hamming cost of
the common-target random-scan coupling, coordinate by coordinate. -/
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
      (Fintype.card ι : ℝ)⁻¹ * ∑ target : ι, ∑ i : ι,
        if i = target then
          (2 : ℝ)⁻¹ *
            ((∑ source ∈ finiteProductDisagreementFinset
                leftInput rightInput, D.influence target source) +
              sourceBound target)
        else finitePairDisagreementIndicator (leftInput i, rightInput i) := by
  rw [finitePositiveWeightsRandomScanJointCoupling_expectedHamming_eq]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro target _
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = target
  · subst i
    simp only [if_pos]
    exact
      finitePositiveWeightsSingleSiteOverlapCoupling_disagreementMass_le_half_mul_influence_add_source
        leftWeight rightWeight hLeftWeight hRightWeight D sourceBound hCross
        leftInput rightInput target
  · simp [hi]

end
end MathlibAnalytic
end MGAP4D
