import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Residual of the second probability weight after extracting the common
subprobability `μ / R`. -/
def finiteProbabilityLikelihoodRatioResidual
    {Ω : Type}
    (μ ν : Ω → ℝ)
    (R : ℝ)
    (y : Ω) : ℝ :=
  ν y - μ y / R

/-- Explicit coupling obtained by placing `μ / R` on the diagonal and coupling
the remaining left mass `(1 - R⁻¹) μ` independently with the right residual
`ν - μ / R`.  The formula contains no division by the residual mass. -/
def finiteProbabilityLikelihoodRatioCoupling
    {Ω : Type}
    [DecidableEq Ω]
    (μ ν : Ω → ℝ)
    (R : ℝ)
    (x y : Ω) : ℝ :=
  (if x = y then μ x / R else 0) +
    μ x * finiteProbabilityLikelihoodRatioResidual μ ν R y

/-- A one-sided pointwise likelihood-ratio bound makes the right residual
nonnegative. -/
theorem finiteProbabilityLikelihoodRatioResidual_nonneg
    {Ω : Type}
    (μ ν : Ω → ℝ)
    (R : ℝ)
    (hR : 0 < R)
    (hRatio : ∀ x : Ω, μ x ≤ R * ν x)
    (y : Ω) :
    0 ≤ finiteProbabilityLikelihoodRatioResidual μ ν R y := by
  unfold finiteProbabilityLikelihoodRatioResidual
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hR).2
  simpa [mul_comm] using hRatio y

/-- The explicit likelihood-ratio coupling is nonnegative. -/
theorem finiteProbabilityLikelihoodRatioCoupling_nonneg
    {Ω : Type}
    [DecidableEq Ω]
    (μ ν : Ω → ℝ)
    (R : ℝ)
    (hμ : ∀ x : Ω, 0 ≤ μ x)
    (hR : 0 < R)
    (hRatio : ∀ x : Ω, μ x ≤ R * ν x)
    (x y : Ω) :
    0 ≤ finiteProbabilityLikelihoodRatioCoupling μ ν R x y := by
  unfold finiteProbabilityLikelihoodRatioCoupling
  apply add_nonneg
  · by_cases hxy : x = y
    · subst y
      simp only [if_pos rfl]
      exact div_nonneg (hμ x) hR.le
    · simp [hxy]
  · exact mul_nonneg (hμ x)
      (finiteProbabilityLikelihoodRatioResidual_nonneg
        μ ν R hR hRatio y)

/-- The right residual has total mass `1 - R⁻¹`. -/
theorem finiteProbabilityLikelihoodRatioResidual_sum
    {Ω : Type}
    [Fintype Ω]
    (μ ν : Ω → ℝ)
    (R : ℝ)
    (hμSum : ∑ x : Ω, μ x = 1)
    (hνSum : ∑ x : Ω, ν x = 1) :
    (∑ y : Ω, finiteProbabilityLikelihoodRatioResidual μ ν R y) =
      1 - R⁻¹ := by
  unfold finiteProbabilityLikelihoodRatioResidual
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, hμSum, hνSum]
  simp [one_div]

/-- The explicit coupling has first marginal `μ`. -/
theorem finiteProbabilityLikelihoodRatioCoupling_leftMarginal
    {Ω : Type}
    [Fintype Ω]
    [DecidableEq Ω]
    (μ ν : Ω → ℝ)
    (R : ℝ)
    (hμSum : ∑ x : Ω, μ x = 1)
    (hνSum : ∑ x : Ω, ν x = 1)
    (x : Ω) :
    (∑ y : Ω, finiteProbabilityLikelihoodRatioCoupling μ ν R x y) = μ x := by
  unfold finiteProbabilityLikelihoodRatioCoupling
  rw [Finset.sum_add_distrib]
  have hDiagonal :
      (∑ y : Ω, if x = y then μ x / R else 0) = μ x / R := by
    simp
  rw [hDiagonal, ← Finset.mul_sum,
    finiteProbabilityLikelihoodRatioResidual_sum μ ν R hμSum hνSum]
  ring

/-- The explicit coupling has second marginal `ν`. -/
theorem finiteProbabilityLikelihoodRatioCoupling_rightMarginal
    {Ω : Type}
    [Fintype Ω]
    [DecidableEq Ω]
    (μ ν : Ω → ℝ)
    (R : ℝ)
    (hμSum : ∑ x : Ω, μ x = 1)
    (y : Ω) :
    (∑ x : Ω, finiteProbabilityLikelihoodRatioCoupling μ ν R x y) = ν y := by
  unfold finiteProbabilityLikelihoodRatioCoupling
  rw [Finset.sum_add_distrib]
  have hDiagonal :
      (∑ x : Ω, if x = y then μ x / R else 0) = μ y / R := by
    simp
  rw [hDiagonal, ← Finset.sum_mul, hμSum, one_mul]
  unfold finiteProbabilityLikelihoodRatioResidual
  ring

/-- Any nonnegative cost bounded by one and vanishing on the diagonal has
expectation at most the residual mass under the explicit coupling. -/
theorem finiteProbabilityLikelihoodRatioCoupling_cost_le_one_sub_inv
    {Ω : Type}
    [Fintype Ω]
    [DecidableEq Ω]
    (μ ν : Ω → ℝ)
    (R : ℝ)
    (hμ : ∀ x : Ω, 0 ≤ μ x)
    (hμSum : ∑ x : Ω, μ x = 1)
    (hνSum : ∑ x : Ω, ν x = 1)
    (hR : 0 < R)
    (hRatio : ∀ x : Ω, μ x ≤ R * ν x)
    (cost : Ω → Ω → ℝ)
    (hCostNonneg : ∀ x y : Ω, 0 ≤ cost x y)
    (hCostLeOne : ∀ x y : Ω, cost x y ≤ 1)
    (hCostDiagonal : ∀ x : Ω, cost x x = 0) :
    (∑ x : Ω, ∑ y : Ω,
      finiteProbabilityLikelihoodRatioCoupling μ ν R x y * cost x y) ≤
      1 - R⁻¹ := by
  calc
    (∑ x : Ω, ∑ y : Ω,
      finiteProbabilityLikelihoodRatioCoupling μ ν R x y * cost x y) ≤
        ∑ x : Ω, ∑ y : Ω,
          μ x * finiteProbabilityLikelihoodRatioResidual μ ν R y := by
      apply Finset.sum_le_sum
      intro x _hx
      apply Finset.sum_le_sum
      intro y _hy
      by_cases hxy : x = y
      · subst y
        simp [hCostDiagonal]
        exact mul_nonneg (hμ x)
          (finiteProbabilityLikelihoodRatioResidual_nonneg
            μ ν R hR hRatio x)
      · rw [finiteProbabilityLikelihoodRatioCoupling]
        simp only [if_neg hxy, zero_add]
        exact mul_le_of_le_one_right
          (mul_nonneg (hμ x)
            (finiteProbabilityLikelihoodRatioResidual_nonneg
              μ ν R hR hRatio y))
          (hCostLeOne x y)
    _ = (∑ x : Ω, μ x) *
        (∑ y : Ω, finiteProbabilityLikelihoodRatioResidual μ ν R y) := by
      calc
        (∑ x : Ω, ∑ y : Ω,
          μ x * finiteProbabilityLikelihoodRatioResidual μ ν R y) =
            ∑ x : Ω, μ x *
              (∑ y : Ω,
                finiteProbabilityLikelihoodRatioResidual μ ν R y) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [Finset.mul_sum]
        _ = (∑ x : Ω, μ x) *
            (∑ y : Ω,
              finiteProbabilityLikelihoodRatioResidual μ ν R y) := by
          rw [Finset.sum_mul]
    _ = 1 - R⁻¹ := by
      rw [hμSum,
        finiteProbabilityLikelihoodRatioResidual_sum μ ν R hμSum hνSum,
        one_mul]

/-- In particular the residual bound is nonnegative when `R ≥ 1`. -/
theorem one_sub_inv_nonneg_of_one_le
    (R : ℝ)
    (hR : 1 ≤ R) :
    0 ≤ 1 - R⁻¹ := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hInv : R⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hRpos]
    exact hR
  linarith

end

end MathlibAnalytic
end MGAP4D
