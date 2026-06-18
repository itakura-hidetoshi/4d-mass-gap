import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonConditionalTotalVariationBounds

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Sharp total-variation comparison for two finite probability vectors under
mutual multiplicative domination by `c`.

The pointwise estimate is
`(c + 1) |p - q| ≤ (c - 1) (p + q)`, and summing uses only that both
vectors have total mass one. -/
theorem finite_probabilityVector_totalVariation_le_of_mutual_le_mul
    {X : Type*} [Fintype X]
    (p q : X → ℝ) (c : ℝ)
    (hpMass : ∑ x : X, p x = 1)
    (hqMass : ∑ x : X, q x = 1)
    (hc : 1 ≤ c)
    (hpq : ∀ x : X, p x ≤ c * q x)
    (hqp : ∀ x : X, q x ≤ c * p x) :
    (2 : ℝ)⁻¹ * ∑ x : X, |p x - q x| ≤
      (c - 1) / (c + 1) := by
  classical
  have hPoint : ∀ x : X,
      (c + 1) * |p x - q x| ≤ (c - 1) * (p x + q x) := by
    intro x
    by_cases h : p x ≤ q x
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      nlinarith [hqp x]
    · have h' : q x ≤ p x := le_of_not_ge h
      rw [abs_of_nonneg (sub_nonneg.mpr h')]
      nlinarith [hpq x]
  have hSum :
      (c + 1) * (∑ x : X, |p x - q x|) ≤ 2 * (c - 1) := by
    calc
      (c + 1) * (∑ x : X, |p x - q x|) =
          ∑ x : X, (c + 1) * |p x - q x| := by
            rw [Finset.mul_sum]
      _ ≤ ∑ x : X, (c - 1) * (p x + q x) := by
        apply Finset.sum_le_sum
        intro x _hx
        exact hPoint x
      _ = (c - 1) * (∑ x : X, (p x + q x)) := by
        rw [Finset.mul_sum]
      _ = (c - 1) * ((∑ x : X, p x) + ∑ x : X, q x) := by
        rw [Finset.sum_add_distrib]
      _ = 2 * (c - 1) := by
        rw [hpMass, hqMass]
        ring
  have hDen : 0 < c + 1 := by linarith
  apply (le_div_iff₀ hDen).2
  calc
    ((2 : ℝ)⁻¹ * ∑ x : X, |p x - q x|) * (c + 1) =
        (2 : ℝ)⁻¹ * ((c + 1) * ∑ x : X, |p x - q x|) := by
          ring
    _ ≤ (2 : ℝ)⁻¹ * (2 * (c - 1)) :=
      mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = c - 1 := by ring

/-- A finite PMF pair with mutual likelihood-ratio bound `c` has total
variation at most `(c - 1) / (c + 1)`. -/
theorem finite_pmf_totalVariation_le_of_mutual_le_mul
    {X : Type*} [Fintype X]
    (p q : PMF X) (c : ℝ)
    (hc : 1 ≤ c)
    (hpq : ∀ x : X, (p x).toReal ≤ c * (q x).toReal)
    (hqp : ∀ x : X, (q x).toReal ≤ c * (p x).toReal) :
    (2 : ℝ)⁻¹ * ∑ x : X, |(p x).toReal - (q x).toReal| ≤
      (c - 1) / (c + 1) :=
  finite_probabilityVector_totalVariation_le_of_mutual_le_mul
    (fun x => (p x).toReal) (fun x => (q x).toReal) c
    (finite_pmf_sum_toReal_eq_one p)
    (finite_pmf_sum_toReal_eq_one q)
    hc hpq hqp

/-- Exponential likelihood-ratio control gives the canonical hyperbolic-tangent
form of the finite total-variation estimate. -/
theorem finite_pmf_totalVariation_le_of_mutual_le_exp_mul
    {X : Type*} [Fintype X]
    (p q : PMF X) (R : ℝ)
    (hR : 0 ≤ R)
    (hpq : ∀ x : X, (p x).toReal ≤ Real.exp R * (q x).toReal)
    (hqp : ∀ x : X, (q x).toReal ≤ Real.exp R * (p x).toReal) :
    (2 : ℝ)⁻¹ * ∑ x : X, |(p x).toReal - (q x).toReal| ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  have hExp : 1 ≤ Real.exp R := by
    simpa using (Real.exp_le_exp.mpr hR)
  exact finite_pmf_totalVariation_le_of_mutual_le_mul
    p q (Real.exp R) hExp hpq hqp

/-- The exponential likelihood-ratio TV majorant is nonnegative. -/
theorem expLikelihoodRatioTotalVariationBound_nonneg
    (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ (Real.exp R - 1) / (Real.exp R + 1) := by
  have hExp : 1 ≤ Real.exp R := by
    simpa using (Real.exp_le_exp.mpr hR)
  exact div_nonneg (sub_nonneg.mpr hExp) (by positivity)

/-- For every finite radius, the exponential likelihood-ratio TV majorant is
strictly below one. -/
theorem expLikelihoodRatioTotalVariationBound_lt_one
    (R : ℝ) :
    (Real.exp R - 1) / (Real.exp R + 1) < 1 := by
  have hDen : 0 < Real.exp R + 1 := by positivity
  apply (div_lt_iff₀ hDen).2
  linarith [Real.exp_pos R]

end

end MathlibAnalytic
end MGAP4D
