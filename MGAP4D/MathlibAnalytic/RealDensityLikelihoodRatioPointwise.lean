import Mathlib

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pointwise algebraic core of the sharp likelihood-ratio total-variation
bound. -/
theorem real_density_abs_sub_mul_le_of_mutual_le_mul
    {X : Type*}
    (p q : X → ℝ)
    (c : ℝ)
    (hc : 1 ≤ c)
    (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x)
    (hpq : ∀ x, p x ≤ c * q x)
    (hqp : ∀ x, q x ≤ c * p x)
    (x : X) :
    (c + 1) * |p x - q x| ≤
      (c - 1) * (p x + q x) := by
  by_cases h : p x ≤ q x
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith [hp x, hq x, hqp x]
  · have h' : q x ≤ p x := le_of_not_ge h
    rw [abs_of_nonneg (sub_nonneg.mpr h')]
    nlinarith [hp x, hq x, hpq x]

end
end MathlibAnalytic
end MGAP4D
