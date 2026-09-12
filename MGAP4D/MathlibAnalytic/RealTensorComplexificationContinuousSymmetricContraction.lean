import MGAP4D.MathlibAnalytic.RealTensorComplexificationContinuousContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

namespace RealTensorComplexification

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Real symmetry is preserved by algebraic complex scalar extension when the
complexification is viewed through its canonical underlying real inner product. -/
theorem realInner_ofContinuousLinearMap_left_eq_right
    (T : H →L[ℝ] H)
    (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (x y : Space H) :
    realInner (ofContinuousLinearMap T x) y =
      realInner x (ofContinuousLinearMap T y) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [realInner]
  · intro z u
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp [realInner]
    · intro w v
      simp only [ofContinuousLinearMap_tmul]
      unfold realInner
      rw [TensorProduct.inner_tmul, TensorProduct.inner_tmul, hT u v]
    · intro y₁ y₂ hy₁ hy₂
      rw [map_add, realInner_add_right, realInner_add_right, hy₁, hy₂]
  · intro x₁ x₂ hx₁ hx₂
    rw [map_add, realInner_add_left, realInner_add_left, hx₁, hx₂]

/-- A symmetric bounded real-linear operator has a complex scalar extension
symmetric for the canonical complex inner product. -/
theorem inner_ofContinuousLinearMap_left_eq_right
    (T : H →L[ℝ] H)
    (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (x y : Space H) :
    inner ℂ (ofContinuousLinearMap T x) y =
      inner ℂ x (ofContinuousLinearMap T y) := by
  rw [inner_complex_eq_complexInner, inner_complex_eq_complexInner]
  unfold complexInner
  rw [realInner_ofContinuousLinearMap_left_eq_right T hT x y]
  rw [← linearMap_map_imaginaryUnit
    (T := ofContinuousLinearMap T) x]
  rw [realInner_ofContinuousLinearMap_left_eq_right T hT
    (imaginaryUnitLinearIsometry x) y]

/-- The continuous complex contraction wrapper preserves symmetry of the
underlying bounded real-linear contraction. -/
theorem inner_ofContinuousLinearMapContraction_left_eq_right
    (T : H →L[ℝ] H)
    (hcontraction : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hsymmetric : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (x y : Space H) :
    inner ℂ (ofContinuousLinearMapContraction T hcontraction x) y =
      inner ℂ x (ofContinuousLinearMapContraction T hcontraction y) := by
  simpa only [ofContinuousLinearMapContraction_apply] using
    inner_ofContinuousLinearMap_left_eq_right T hsymmetric x y

end RealTensorComplexification

end

end MathlibAnalytic
end MGAP4D
