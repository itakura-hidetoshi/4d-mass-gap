import MGAP4D.MathlibAnalytic.FinitePositiveWeightDobrushinApproximateTensorization
import MGAP4D.MathlibAnalytic.FinitePMFLikelihoodRatioTotalVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A four-point cross-ratio estimate comparing two one-site fibers of a
positive finite product weight.  This is the normalization-stable input for a
target/source conditional influence estimate. -/
def FinitePositiveWeightSingleSiteCrossRatioBound
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι)
    (ratio : ℝ) : Prop :=
  ∀ g h : G,
    weight (Function.update A target g) *
        weight (Function.update B target h) ≤
      ratio *
        (weight (Function.update B target g) *
          weight (Function.update A target h))

/-- A fiber cross-ratio estimate survives normalization and gives pointwise
likelihood-ratio domination of the corresponding one-site conditional laws. -/
theorem finitePositiveWeightSingleSiteProbability_le_ratio_mul_of_crossRatio
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (A B : ι → G)
    (target : ι)
    (ratio : ℝ)
    (hCross : FinitePositiveWeightSingleSiteCrossRatioBound
      weight A B target ratio)
    (g : G) :
    finitePositiveWeightSingleSiteProbability weight A target g ≤
      ratio *
        finitePositiveWeightSingleSiteProbability weight B target g := by
  let ZA := finitePositiveWeightSingleSitePartition weight A target
  let ZB := finitePositiveWeightSingleSitePartition weight B target
  have hZA : 0 < ZA :=
    finitePositiveWeightSingleSitePartition_pos weight hweight A target
  have hZB : 0 < ZB :=
    finitePositiveWeightSingleSitePartition_pos weight hweight B target
  unfold finitePositiveWeightSingleSiteProbability
  change weight (Function.update A target g) / ZA ≤
    ratio * (weight (Function.update B target g) / ZB)
  rw [show ratio * (weight (Function.update B target g) / ZB) =
      (ratio * weight (Function.update B target g)) / ZB by ring]
  apply (div_le_div_iff₀ hZA hZB).2
  unfold ZA ZB finitePositiveWeightSingleSitePartition
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _hh
  exact hCross g h

/-- The cross-ratio condition is symmetric in the two environments. -/
theorem finitePositiveWeightSingleSiteCrossRatioBound_symm
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι)
    (ratio : ℝ)
    (hCross : FinitePositiveWeightSingleSiteCrossRatioBound
      weight A B target ratio) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      weight B A target ratio := by
  intro g h
  simpa [mul_comm, mul_left_comm, mul_assoc] using hCross h g

/-- A mutual fiber cross-ratio bound gives the full conditional `L¹` estimate.
The factor two is present because the repository's Dobrushin matrix uses full
`L¹`, not half total variation. -/
theorem finitePositiveWeightSingleSiteConditionalL1_le_of_crossRatio
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (A B : ι → G)
    (target : ι)
    (ratio : ℝ)
    (hRatio : 1 ≤ ratio)
    (hCross : FinitePositiveWeightSingleSiteCrossRatioBound
      weight A B target ratio) :
    finitePositiveWeightSingleSiteConditionalL1 weight A B target ≤
      2 * ((ratio - 1) / (ratio + 1)) := by
  let p : G → ℝ :=
    finitePositiveWeightSingleSiteProbability weight A target
  let q : G → ℝ :=
    finitePositiveWeightSingleSiteProbability weight B target
  have hpMass : ∑ g : G, p g = 1 := by
    simpa [p] using
      finitePositiveWeightSingleSiteProbability_sum_eq_one
        weight hweight A target
  have hqMass : ∑ g : G, q g = 1 := by
    simpa [q] using
      finitePositiveWeightSingleSiteProbability_sum_eq_one
        weight hweight B target
  have hpq : ∀ g : G, p g ≤ ratio * q g := by
    intro g
    exact finitePositiveWeightSingleSiteProbability_le_ratio_mul_of_crossRatio
      weight hweight A B target ratio hCross g
  have hqp : ∀ g : G, q g ≤ ratio * p g := by
    intro g
    exact finitePositiveWeightSingleSiteProbability_le_ratio_mul_of_crossRatio
      weight hweight B A target ratio
        (finitePositiveWeightSingleSiteCrossRatioBound_symm
          weight A B target ratio hCross) g
  have hTV :=
    finite_probabilityVector_totalVariation_le_of_mutual_le_mul
      p q ratio hpMass hqMass hRatio hpq hqp
  unfold finitePositiveWeightSingleSiteConditionalL1
  change (∑ g : G, |p g - q g|) ≤
    2 * ((ratio - 1) / (ratio + 1))
  nlinarith

/-- Cross-ratio radii and a strict row-sum certificate for an arbitrary
positive finite product weight.  Off-diagonal radius `R target source`
controls the four-point fiber cross ratio by `exp R`; diagonal influence is
set to zero because conditioning on the target coordinate forgets its stored
value exactly. -/
structure FinitePositiveWeightCrossRatioDobrushinData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) where
  radius : ι → ι → ℝ
  radius_nonneg : ∀ target source : ι, 0 ≤ radius target source
  crossRatioBound :
    ∀ (target source : ι) (A B : ι → G),
      target ≠ source →
      FiniteProductAgreeOff A B source →
        FinitePositiveWeightSingleSiteCrossRatioBound
          weight A B target (Real.exp (radius target source))
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  rowSum_le_coefficient :
    ∀ target : ι,
      ∑ source : ι,
        if target = source then 0 else
          2 * ((Real.exp (radius target source) - 1) /
            (Real.exp (radius target source) + 1)) ≤
        coefficient
  coefficient_lt_one : coefficient < 1

/-- Full-`L¹` influence generated by a cross-ratio radius. -/
noncomputable def finitePositiveWeightCrossRatioInfluence
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightCrossRatioDobrushinData weight)
    (target source : ι) : ℝ :=
  if target = source then 0 else
    2 * ((Real.exp (D.radius target source) - 1) /
      (Real.exp (D.radius target source) + 1))

/-- Cross-ratio influence is nonnegative. -/
theorem finitePositiveWeightCrossRatioInfluence_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightCrossRatioDobrushinData weight)
    (target source : ι) :
    0 ≤ finitePositiveWeightCrossRatioInfluence D target source := by
  by_cases hEq : target = source
  · simp [finitePositiveWeightCrossRatioInfluence, hEq]
  · rw [finitePositiveWeightCrossRatioInfluence, if_neg hEq]
    exact mul_nonneg (by norm_num)
      (expLikelihoodRatioTotalVariationBound_nonneg
        (D.radius target source) (D.radius_nonneg target source))

/-- Diagonal cross-ratio influence is exactly zero. -/
theorem finitePositiveWeightCrossRatioInfluence_diagonal
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightCrossRatioDobrushinData weight)
    (e : ι) :
    finitePositiveWeightCrossRatioInfluence D e e = 0 := by
  simp [finitePositiveWeightCrossRatioInfluence]

/-- The cross-ratio influence bounds every exact target conditional change
produced by a one-source environment perturbation. -/
theorem finitePositiveWeightSingleSiteConditionalL1_le_crossRatioInfluence
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (D : FinitePositiveWeightCrossRatioDobrushinData weight)
    (target source : ι)
    (A B : ι → G)
    (hAgree : FiniteProductAgreeOff A B source) :
    finitePositiveWeightSingleSiteConditionalL1 weight A B target ≤
      finitePositiveWeightCrossRatioInfluence D target source := by
  by_cases hEq : target = source
  · subst source
    rw [finitePositiveWeightSingleSiteConditionalL1_eq_zero_of_agreeOff
      weight A B target hAgree,
      finitePositiveWeightCrossRatioInfluence_diagonal]
  · rw [finitePositiveWeightCrossRatioInfluence, if_neg hEq]
    apply finitePositiveWeightSingleSiteConditionalL1_le_of_crossRatio
      weight hweight A B target (Real.exp (D.radius target source))
    · simpa using
        (Real.exp_le_exp.mpr (D.radius_nonneg target source))
    · exact D.crossRatioBound target source A B hEq hAgree

/-- Convert proof-relevant cross-ratio data into the generic Dobrushin `L¹`
matrix consumed by random-scan contraction and approximate tensorization. -/
noncomputable def
    FinitePositiveWeightCrossRatioDobrushinData.toDobrushinL1MatrixData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {weight : (ι → G) → ℝ}
    (hweight : ∀ A : ι → G, 0 < weight A)
    (D : FinitePositiveWeightCrossRatioDobrushinData weight) :
    FinitePositiveWeightDobrushinL1MatrixData weight :=
  { influence := finitePositiveWeightCrossRatioInfluence D
    influence_nonneg := finitePositiveWeightCrossRatioInfluence_nonneg D
    influence_diagonal_zero :=
      finitePositiveWeightCrossRatioInfluence_diagonal D
    conditionalL1_le := fun target source A B hAgree =>
      finitePositiveWeightSingleSiteConditionalL1_le_crossRatioInfluence
        weight hweight D target source A B hAgree
    coefficient := D.coefficient
    coefficient_nonneg := D.coefficient_nonneg
    rowSum_le_coefficient := by
      intro target
      simpa [finitePositiveWeightCrossRatioInfluence] using
        D.rowSum_le_coefficient target
    coefficient_lt_one := D.coefficient_lt_one }

/-- Cross-ratio Dobrushin data directly yields the centered approximate
 tensorization inequality for the underlying positive weight. -/
theorem finitePositiveWeight_crossRatio_approximateTensorization
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (D : FinitePositiveWeightCrossRatioDobrushinData weight)
    (hCard : 0 < Fintype.card ι)
    (f : (ι → G) → ℝ)
    (hCenter : finitePositiveWeightSum weight f = 0) :
    finitePositiveWeightPairing weight f f ≤
      (finitePositiveWeightDobrushinGap
        (D.toDobrushinL1MatrixData hweight))⁻¹ *
        finitePositiveWeightTotalSingleSiteVariance weight f :=
  finitePositiveWeight_centered_dobrushin_approximateTensorization_inv_gap
    weight hweight (D.toDobrushinL1MatrixData hweight)
      hCard f hCenter

end

end MathlibAnalytic
end MGAP4D
