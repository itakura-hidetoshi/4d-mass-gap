import MGAP4D.MathlibAnalytic.FinitePositiveWeightDobrushinRandomScanContraction
import MGAP4D.MathlibAnalytic.FinitePositiveWeightLocalTiltConditional
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Cross-weight one-site conditional `L¹` distance controls the difference of
the corresponding one-site conditional expectations against any observable
with a declared coordinate-variation profile. -/
theorem FiniteProductVariationBound.singleSiteExpectation_crossWeight_difference_abs_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (A : ι → G)
    (target : ι) :
    |finitePositiveWeightSingleSiteExpectation leftWeight f A target -
        finitePositiveWeightSingleSiteExpectation rightWeight f A target| ≤
      finitePositiveWeightSingleSiteConditionalCrossL1
          leftWeight rightWeight A target *
        P.variation target := by
  classical
  let p : G → ℝ :=
    finitePositiveWeightSingleSiteProbability leftWeight A target
  let q : G → ℝ :=
    finitePositiveWeightSingleSiteProbability rightWeight A target
  let u : G → ℝ := fun g => f (Function.update A target g)
  have hpSum : ∑ g : G, p g = 1 := by
    simpa [p] using
      finitePositiveWeightSingleSiteProbability_sum_eq_one
        leftWeight hLeftWeight A target
  have hqSum : ∑ g : G, q g = 1 := by
    simpa [q] using
      finitePositiveWeightSingleSiteProbability_sum_eq_one
        rightWeight hRightWeight A target
  have hOscillation :
      ∀ g h : G, |u g - u h| ≤ P.variation target := by
    intro g h
    exact
      P.variation_bound target
        (Function.update A target g)
        (Function.update A target h)
        (finiteProductUpdates_sameBase_agreeOff A target g h)
  unfold finitePositiveWeightSingleSiteExpectation
  change
    |(∑ g : G, p g * u g) - ∑ g : G, q g * u g| ≤ _
  simpa [p, q, u, finitePositiveWeightSingleSiteConditionalCrossL1] using
    finiteRealProbability_expectation_difference_abs_le_l1_mul
      p q u (P.variation target) hOscillation hpSum hqSum

/-- A declared pointwise source bound for cross-weight conditionals gives the
corresponding one-site expectation comparison, retaining the target variation
as a multiplicative weight. -/
theorem FiniteProductVariationBound.singleSiteExpectation_crossWeight_difference_abs_le_source_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (sourceBound : ι → ℝ)
    (hCrossL1 :
      ∀ (A : ι → G) (target : ι),
        finitePositiveWeightSingleSiteConditionalCrossL1
            leftWeight rightWeight A target ≤
          sourceBound target)
    (A : ι → G)
    (target : ι) :
    |finitePositiveWeightSingleSiteExpectation leftWeight f A target -
        finitePositiveWeightSingleSiteExpectation rightWeight f A target| ≤
      sourceBound target * P.variation target := by
  exact le_trans
    (P.singleSiteExpectation_crossWeight_difference_abs_le
      leftWeight rightWeight hLeftWeight hRightWeight A target)
    (mul_le_mul_of_nonneg_right
      (hCrossL1 A target) (P.variation_nonneg target))

/-- Cross-weight random-scan comparison.  The error is retained as the local
pairing of the conditional source vector with the observable variation
profile; it is not collapsed to a volume-dependent uniform bound. -/
theorem FiniteProductVariationBound.randomScan_crossWeight_difference_abs_le_sourcePairing
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (sourceBound : ι → ℝ)
    (hCrossL1 :
      ∀ (A : ι → G) (target : ι),
        finitePositiveWeightSingleSiteConditionalCrossL1
            leftWeight rightWeight A target ≤
          sourceBound target)
    (A : ι → G) :
    |finitePositiveWeightRandomScanConditionalExpectation leftWeight f A -
        finitePositiveWeightRandomScanConditionalExpectation rightWeight f A| ≤
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          sourceBound target * P.variation target := by
  have hInvNonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hTarget (target : ι) :
      |finitePositiveWeightSingleSiteExpectation leftWeight f A target -
          finitePositiveWeightSingleSiteExpectation rightWeight f A target| ≤
        sourceBound target * P.variation target :=
    P.singleSiteExpectation_crossWeight_difference_abs_le_source_mul
      leftWeight rightWeight hLeftWeight hRightWeight
      sourceBound hCrossL1 A target
  unfold finitePositiveWeightRandomScanConditionalExpectation
  calc
    |(Fintype.card ι : ℝ)⁻¹ *
          (∑ target : ι,
            finitePositiveWeightSingleSiteExpectation
              leftWeight f A target) -
        (Fintype.card ι : ℝ)⁻¹ *
          (∑ target : ι,
            finitePositiveWeightSingleSiteExpectation
              rightWeight f A target)| =
      (Fintype.card ι : ℝ)⁻¹ *
        |∑ target : ι,
          (finitePositiveWeightSingleSiteExpectation
              leftWeight f A target -
            finitePositiveWeightSingleSiteExpectation
              rightWeight f A target)| := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_nonneg hInvNonneg]
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          |finitePositiveWeightSingleSiteExpectation
              leftWeight f A target -
            finitePositiveWeightSingleSiteExpectation
              rightWeight f A target| := by
      apply mul_le_mul_of_nonneg_left _ hInvNonneg
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          sourceBound target * P.variation target := by
      apply mul_le_mul_of_nonneg_left _ hInvNonneg
      apply Finset.sum_le_sum
      intro target _htarget
      exact hTarget target

end

end MathlibAnalytic
end MGAP4D
