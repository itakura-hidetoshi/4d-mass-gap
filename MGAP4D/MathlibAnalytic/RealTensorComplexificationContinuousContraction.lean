import MGAP4D.MathlibAnalytic.RealTensorComplexificationLinearMap
import MGAP4D.MathlibAnalytic.RealTensorComplexificationRealImagCompleteSpace
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

namespace RealTensorComplexification

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Real coordinates commute with scalar extension of a bounded real-linear map. -/
@[simp] theorem realPart_ofContinuousLinearMap
    (T : E →L[ℝ] F)
    (x : Space E) :
    realPart (ofContinuousLinearMap T x) = T (realPart x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z y
    simp
  · intro x y hx hy
    simpa [map_add, hx, hy]

/-- Imaginary coordinates commute with scalar extension of a bounded real-linear map. -/
@[simp] theorem imagPart_ofContinuousLinearMap
    (T : E →L[ℝ] F)
    (x : Space E) :
    imagPart (ofContinuousLinearMap T x) = T (imagPart x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z y
    simp
  · intro x y hx hy
    simpa [map_add, hx, hy]

/-- The tensor norm is the `L²` sum of the real and imaginary coordinate norms. -/
theorem norm_sq_eq_realPart_add_imagPart (x : Space E) :
    ‖x‖ ^ 2 = ‖realPart x‖ ^ 2 + ‖imagPart x‖ ^ 2 := by
  simpa [realImagLinearIsometryEquiv_apply, toRealImagLinear,
    toRealImagProdLinear] using
    (WithLp.prod_norm_sq_eq_of_L2
      (realImagLinearIsometryEquiv (H := E) x))

/-- Scalar extension preserves the contraction bound of a bounded real-linear map. -/
theorem norm_ofContinuousLinearMap_le
    (T : E →L[ℝ] F)
    (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (x : Space E) :
    ‖ofContinuousLinearMap T x‖ ≤ ‖x‖ := by
  have hre := hT (realPart x)
  have him := hT (imagPart x)
  have hre_sq :
      ‖T (realPart x)‖ ^ 2 ≤ ‖realPart x‖ ^ 2 := by
    nlinarith [norm_nonneg (T (realPart x)), norm_nonneg (realPart x)]
  have him_sq :
      ‖T (imagPart x)‖ ^ 2 ≤ ‖imagPart x‖ ^ 2 := by
    nlinarith [norm_nonneg (T (imagPart x)), norm_nonneg (imagPart x)]
  have hsq :
      ‖ofContinuousLinearMap T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq_realPart_add_imagPart,
      norm_sq_eq_realPart_add_imagPart,
      realPart_ofContinuousLinearMap,
      imagPart_ofContinuousLinearMap]
    exact add_le_add hre_sq him_sq
  nlinarith [norm_nonneg (ofContinuousLinearMap T x), norm_nonneg x]

/-- A real contraction extends canonically to a continuous complex-linear
contraction on the algebraic complexification equipped with its Hilbert norm. -/
def ofContinuousLinearMapContraction
    (T : E →L[ℝ] F)
    (hT : ∀ x, ‖T x‖ ≤ ‖x‖) :
    Space E →L[ℂ] Space F :=
  (ofContinuousLinearMap T).mkContinuous 1 fun x => by
    simpa using norm_ofContinuousLinearMap_le T hT x

@[simp] theorem ofContinuousLinearMapContraction_apply
    (T : E →L[ℝ] F)
    (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (x : Space E) :
    ofContinuousLinearMapContraction T hT x =
      ofContinuousLinearMap T x :=
  rfl

@[simp] theorem ofContinuousLinearMapContraction_tmul
    (T : E →L[ℝ] F)
    (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (z : ℂ)
    (x : E) :
    ofContinuousLinearMapContraction T hT (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ] T x := by
  rfl

/-- The continuous complex scalar extension retains operator bound one. -/
theorem norm_ofContinuousLinearMapContraction_le
    (T : E →L[ℝ] F)
    (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (x : Space E) :
    ‖ofContinuousLinearMapContraction T hT x‖ ≤ ‖x‖ :=
  norm_ofContinuousLinearMap_le T hT x

end RealTensorComplexification

end

end MathlibAnalytic
end MGAP4D
