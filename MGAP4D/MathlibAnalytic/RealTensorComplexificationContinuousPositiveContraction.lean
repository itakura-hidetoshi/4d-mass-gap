import MGAP4D.MathlibAnalytic.RealTensorComplexificationContinuousSelfAdjointContraction
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace RealTensorComplexification

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The real part of the complexified quadratic form is the sum of the real
quadratic forms on the real and imaginary coordinates. -/
theorem re_inner_ofContinuousLinearMapContraction_self_eq
    (T : H →L[ℝ] H)
    (hcontraction : ∀ x, ‖T x‖ ≤ ‖x‖)
    (x : Space H) :
    (inner ℂ (ofContinuousLinearMapContraction T hcontraction x) x).re =
      inner ℝ (T (realPart x)) (realPart x) +
        inner ℝ (T (imagPart x)) (imagPart x) := by
  rw [inner_complex_re]
  change realInner (ofContinuousLinearMap T x) x = _
  rw [← realImagLinearEquiv_inner_map_map]
  simp [realImagLinearEquiv_apply, toRealImagLinear,
    toRealImagProdLinear, WithLp.prod_inner_apply]

/-- Nonnegativity of a real quadratic form is preserved by continuous complex
scalar extension. -/
theorem re_inner_ofContinuousLinearMapContraction_self_nonneg
    (T : H →L[ℝ] H)
    (hcontraction : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hpositive : ∀ x, 0 ≤ inner ℝ (T x) x)
    (x : Space H) :
    0 ≤ (inner ℂ (ofContinuousLinearMapContraction T hcontraction x) x).re := by
  rw [re_inner_ofContinuousLinearMapContraction_self_eq]
  exact add_nonneg (hpositive (realPart x)) (hpositive (imagPart x))

/-- The continuous complexification of a symmetric positive real contraction is
positive in Mathlib's bundled continuous-linear-map sense. -/
theorem isPositive_ofContinuousLinearMapContraction
    (T : H →L[ℝ] H)
    (hcontraction : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hsymmetric : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hpositive : ∀ x, 0 ≤ inner ℝ (T x) x) :
    (ofContinuousLinearMapContraction T hcontraction).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨isSymmetric_ofContinuousLinearMapContraction
    T hcontraction hsymmetric, ?_⟩
  intro x
  exact re_inner_ofContinuousLinearMapContraction_self_nonneg
    T hcontraction hpositive x

/-- The continuous complexification of a symmetric positive real contraction is
nonnegative in the Loewner order. -/
theorem nonneg_ofContinuousLinearMapContraction
    (T : H →L[ℝ] H)
    (hcontraction : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hsymmetric : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hpositive : ∀ x, 0 ≤ inner ℝ (T x) x) :
    0 ≤ ofContinuousLinearMapContraction T hcontraction :=
  (ContinuousLinearMap.nonneg_iff_isPositive
    (ofContinuousLinearMapContraction T hcontraction)).2
      (isPositive_ofContinuousLinearMapContraction
        T hcontraction hsymmetric hpositive)

end RealTensorComplexification

end
end MathlibAnalytic
end MGAP4D
