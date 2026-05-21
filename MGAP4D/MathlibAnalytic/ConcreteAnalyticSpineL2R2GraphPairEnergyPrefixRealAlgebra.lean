import MGAP4D.MathlibAnalytic.Basic

namespace MGAP4D
namespace MathlibAnalytic

/-- Pure real-algebra kernel for the positive-coefficient Cauchy--Schwarz step.
It is intentionally independent of the concrete prefix carrier. -/
theorem real_sq_le_mul_of_vertex_quadratic_nonneg
    (a b i : ℝ) (ha : 0 < a)
    (h : 0 ≤ ((-i / a) ^ 2) * a + (2 : ℝ) * ((-i / a) * i) + b) :
    i ^ 2 ≤ a * b := by
  have hs :
      ((-i / a) ^ 2) * a + (2 : ℝ) * ((-i / a) * i) + b =
        b - i ^ 2 / a := by
    field_simp [ne_of_gt ha] <;> ring
  have hnonneg : 0 ≤ b - i ^ 2 / a := by
    rwa [hs] at h
  have hmul_nonneg : 0 ≤ a * (b - i ^ 2 / a) := by
    exact mul_nonneg ha.le hnonneg
  have hmul_simplified : a * (b - i ^ 2 / a) = a * b - i ^ 2 := by
    field_simp [ne_of_gt ha] <;> ring
  have hdiff_nonneg : 0 ≤ a * b - i ^ 2 := by
    rwa [hmul_simplified] at hmul_nonneg
  nlinarith

end MathlibAnalytic
end MGAP4D
