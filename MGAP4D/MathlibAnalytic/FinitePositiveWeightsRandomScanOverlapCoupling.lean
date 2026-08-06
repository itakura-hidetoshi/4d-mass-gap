import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanKernelProbability
import MGAP4D.MathlibAnalytic.FinitePositiveWeightsSingleSiteOverlapCoupling
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- Push-forward of a cross-weight one-site overlap coupling to a joint law on
full configurations after updating the same target coordinate. -/
def finitePositiveWeightsSingleSiteJointUpdateKernel
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput : ι → G) (target : ι)
    (leftOutput rightOutput : ι → G) : ℝ :=
  ∑ g : G, ∑ h : G,
    if Function.update leftInput target g = leftOutput ∧
        Function.update rightInput target h = rightOutput then
      (finitePositiveWeightsSingleSiteOverlapCouplingData
        leftWeight rightWeight hLeftWeight hRightWeight
        leftInput rightInput target).joint g h
    else 0

/-- The pushed-forward one-site joint update kernel is nonnegative. -/
theorem finitePositiveWeightsSingleSiteJointUpdateKernel_nonneg
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput : ι → G) (target : ι)
    (leftOutput rightOutput : ι → G) :
    0 ≤ finitePositiveWeightsSingleSiteJointUpdateKernel
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput target leftOutput rightOutput := by
  unfold finitePositiveWeightsSingleSiteJointUpdateKernel
  apply Finset.sum_nonneg
  intro g _
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact (finitePositiveWeightsSingleSiteOverlapCouplingData
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput target).joint_nonneg g h
  · exact le_rfl

/-- The left full-configuration marginal is exactly the left one-site update
kernel. -/
theorem finitePositiveWeightsSingleSiteJointUpdateKernel_leftMarginal
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput : ι → G) (target : ι)
    (leftOutput : ι → G) :
    ∑ rightOutput : ι → G,
      finitePositiveWeightsSingleSiteJointUpdateKernel
        leftWeight rightWeight hLeftWeight hRightWeight
        leftInput rightInput target leftOutput rightOutput =
      finitePositiveWeightSingleSiteUpdateKernel
        leftWeight leftInput target leftOutput := by
  classical
  let C := finitePositiveWeightsSingleSiteOverlapCouplingData
    leftWeight rightWeight hLeftWeight hRightWeight
    leftInput rightInput target
  unfold finitePositiveWeightsSingleSiteJointUpdateKernel
    finitePositiveWeightSingleSiteUpdateKernel
  calc
    (∑ rightOutput : ι → G, ∑ g : G, ∑ h : G,
      if Function.update leftInput target g = leftOutput ∧
          Function.update rightInput target h = rightOutput then
        C.joint g h else 0) =
      ∑ g : G, ∑ h : G, ∑ rightOutput : ι → G,
        if Function.update leftInput target g = leftOutput ∧
            Function.update rightInput target h = rightOutput then
          C.joint g h else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ h : G,
        if Function.update leftInput target g = leftOutput then
          C.joint g h else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro h _
      by_cases hg : Function.update leftInput target g = leftOutput
      · simp [hg]
      · simp [hg]
    _ = ∑ g : G,
        if Function.update leftInput target g = leftOutput then
          finitePositiveWeightSingleSiteProbability
            leftWeight leftInput target g else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : Function.update leftInput target g = leftOutput
      · simp only [hg, if_true]
        exact finitePositiveWeightsSingleSiteOverlapCoupling_leftMarginal
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target g
      · simp [hg]

/-- The right full-configuration marginal is exactly the right one-site update
kernel. -/
theorem finitePositiveWeightsSingleSiteJointUpdateKernel_rightMarginal
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput : ι → G) (target : ι)
    (rightOutput : ι → G) :
    ∑ leftOutput : ι → G,
      finitePositiveWeightsSingleSiteJointUpdateKernel
        leftWeight rightWeight hLeftWeight hRightWeight
        leftInput rightInput target leftOutput rightOutput =
      finitePositiveWeightSingleSiteUpdateKernel
        rightWeight rightInput target rightOutput := by
  classical
  let C := finitePositiveWeightsSingleSiteOverlapCouplingData
    leftWeight rightWeight hLeftWeight hRightWeight
    leftInput rightInput target
  unfold finitePositiveWeightsSingleSiteJointUpdateKernel
    finitePositiveWeightSingleSiteUpdateKernel
  calc
    (∑ leftOutput : ι → G, ∑ g : G, ∑ h : G,
      if Function.update leftInput target g = leftOutput ∧
          Function.update rightInput target h = rightOutput then
        C.joint g h else 0) =
      ∑ h : G, ∑ g : G, ∑ leftOutput : ι → G,
        if Function.update leftInput target g = leftOutput ∧
            Function.update rightInput target h = rightOutput then
          C.joint g h else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = ∑ h : G, ∑ g : G,
        if Function.update rightInput target h = rightOutput then
          C.joint g h else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro g _
      by_cases hh : Function.update rightInput target h = rightOutput
      · simp [hh]
      · simp [hh]
    _ = ∑ h : G,
        if Function.update rightInput target h = rightOutput then
          finitePositiveWeightSingleSiteProbability
            rightWeight rightInput target h else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : Function.update rightInput target h = rightOutput
      · simp only [hh, if_true]
        exact finitePositiveWeightsSingleSiteOverlapCoupling_rightMarginal
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target h
      · simp [hh]

/-- The pushed-forward one-site kernel is an exact coupling of the two
full-configuration one-site update rows. -/
noncomputable def finitePositiveWeightsSingleSiteJointUpdateCouplingData
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput : ι → G) (target : ι) :
    FiniteRealCouplingData
      (finitePositiveWeightSingleSiteUpdateProbabilityData
        leftWeight hLeftWeight leftInput target)
      (finitePositiveWeightSingleSiteUpdateProbabilityData
        rightWeight hRightWeight rightInput target) :=
  { joint := finitePositiveWeightsSingleSiteJointUpdateKernel
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput target
    joint_nonneg := finitePositiveWeightsSingleSiteJointUpdateKernel_nonneg
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput target
    left_marginal := finitePositiveWeightsSingleSiteJointUpdateKernel_leftMarginal
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput target
    right_marginal := finitePositiveWeightsSingleSiteJointUpdateKernel_rightMarginal
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput target }

/-- Uniform random-scan average of the cross-weight one-site joint update
kernels, using the same randomly chosen target on both sides. -/
def finitePositiveWeightsRandomScanJointKernel
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput leftOutput rightOutput : ι → G) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ target : ι,
    finitePositiveWeightsSingleSiteJointUpdateKernel
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput target leftOutput rightOutput

/-- The cross-weight random-scan joint kernel is nonnegative. -/
theorem finitePositiveWeightsRandomScanJointKernel_nonneg
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput leftOutput rightOutput : ι → G) :
    0 ≤ finitePositiveWeightsRandomScanJointKernel
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput leftOutput rightOutput := by
  unfold finitePositiveWeightsRandomScanJointKernel
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun target _ =>
      finitePositiveWeightsSingleSiteJointUpdateKernel_nonneg
        leftWeight rightWeight hLeftWeight hRightWeight
        leftInput rightInput target leftOutput rightOutput)

/-- The left marginal of the joint random-scan kernel is the left random-scan
row. -/
theorem finitePositiveWeightsRandomScanJointKernel_leftMarginal
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput leftOutput : ι → G) :
    ∑ rightOutput : ι → G,
      finitePositiveWeightsRandomScanJointKernel
        leftWeight rightWeight hLeftWeight hRightWeight
        leftInput rightInput leftOutput rightOutput =
      finitePositiveWeightRandomScanKernel
        leftWeight leftInput leftOutput := by
  classical
  unfold finitePositiveWeightsRandomScanJointKernel
    finitePositiveWeightRandomScanKernel
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro target _
  exact finitePositiveWeightsSingleSiteJointUpdateKernel_leftMarginal
    leftWeight rightWeight hLeftWeight hRightWeight
    leftInput rightInput target leftOutput

/-- The right marginal of the joint random-scan kernel is the right
random-scan row. -/
theorem finitePositiveWeightsRandomScanJointKernel_rightMarginal
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput rightOutput : ι → G) :
    ∑ leftOutput : ι → G,
      finitePositiveWeightsRandomScanJointKernel
        leftWeight rightWeight hLeftWeight hRightWeight
        leftInput rightInput leftOutput rightOutput =
      finitePositiveWeightRandomScanKernel
        rightWeight rightInput rightOutput := by
  classical
  unfold finitePositiveWeightsRandomScanJointKernel
    finitePositiveWeightRandomScanKernel
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro target _
  exact finitePositiveWeightsSingleSiteJointUpdateKernel_rightMarginal
    leftWeight rightWeight hLeftWeight hRightWeight
    leftInput rightInput target rightOutput

/-- Exact coupling of the two cross-weight random-scan rows. -/
noncomputable def finitePositiveWeightsRandomScanJointCouplingData
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (hCard : 0 < Fintype.card ι)
    (leftInput rightInput : ι → G) :
    FiniteRealCouplingData
      (finitePositiveWeightRandomScanProbabilityData
        leftWeight hLeftWeight hCard leftInput)
      (finitePositiveWeightRandomScanProbabilityData
        rightWeight hRightWeight hCard rightInput) :=
  { joint := finitePositiveWeightsRandomScanJointKernel
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput
    joint_nonneg := finitePositiveWeightsRandomScanJointKernel_nonneg
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput
    left_marginal := finitePositiveWeightsRandomScanJointKernel_leftMarginal
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput
    right_marginal := finitePositiveWeightsRandomScanJointKernel_rightMarginal
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput }

end
end MathlibAnalytic
end MGAP4D
