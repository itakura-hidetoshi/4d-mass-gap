import Mathlib.Analysis.Normed.Operator.Extend
import MGAP4D.MathlibAnalytic.RealLinearIsometryProjectedCompression

noncomputable section

namespace MGAP4D
namespace MathlibAnalytic

open Function

variable {E H B F : Type*}
variable [AddCommGroup E] [Module ℝ E]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Extend a real-linear map from a dense algebraic carrier into a complete
Hilbert space, then pull that extension back to the whole ambient Hilbert
realization by the canonical projected inverse of an isometric embedding.

This packages the exact pattern needed by OS reconstruction: `e : E → H` may
have a kernel (the OS null space), so no injectivity assumption is required.
The sole analytic input is the pointwise estimate `‖u x‖ ≤ C ‖e x‖`. -/
noncomputable def realLinearDenseIsometricAmbientExtension
    (u : E →ₗ[ℝ] F)
    (e : E →ₗ[ℝ] H)
    (J : H →ₗᵢ[ℝ] B)
    (hDense : DenseRange e)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hBound : ∀ x, ‖u x‖ ≤ C * ‖e x‖) :
    B →L[ℝ] F :=
  (u.extendOfNorm e).comp (realLinearIsometryProjectedInverse J)

/-- The ambient extension agrees exactly with the original map on every dense
represented vector. -/
@[simp] theorem realLinearDenseIsometricAmbientExtension_apply
    (u : E →ₗ[ℝ] F)
    (e : E →ₗ[ℝ] H)
    (J : H →ₗᵢ[ℝ] B)
    (hDense : DenseRange e)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hBound : ∀ x, ‖u x‖ ≤ C * ‖e x‖)
    (x : E) :
    realLinearDenseIsometricAmbientExtension
        u e J hDense C hC hBound (J (e x)) = u x := by
  rw [realLinearDenseIsometricAmbientExtension,
    ContinuousLinearMap.comp_apply,
    realLinearIsometryProjectedInverse_apply_map]
  exact LinearMap.extendOfNorm_eq hDense ⟨C, hBound⟩ x

/-- The same carrier bound controls the ambient extension pointwise. -/
theorem realLinearDenseIsometricAmbientExtension_norm_le
    (u : E →ₗ[ℝ] F)
    (e : E →ₗ[ℝ] H)
    (J : H →ₗᵢ[ℝ] B)
    (hDense : DenseRange e)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hBound : ∀ x, ‖u x‖ ≤ C * ‖e x‖)
    (y : B) :
    ‖realLinearDenseIsometricAmbientExtension
        u e J hDense C hC hBound y‖ ≤ C * ‖y‖ := by
  change
    ‖u.extendOfNorm e (realLinearIsometryProjectedInverse J y)‖ ≤
      C * ‖y‖
  calc
    ‖u.extendOfNorm e (realLinearIsometryProjectedInverse J y)‖ ≤
        C * ‖realLinearIsometryProjectedInverse J y‖ :=
      LinearMap.norm_extendOfNorm_apply_le hDense C hBound _
    _ ≤ C * ‖y‖ := by
      exact mul_le_mul_of_nonneg_left
        (realLinearIsometryProjectedInverse_norm_le J y) hC

/-- Passing through the OS completion and the ambient orthogonal projection
costs no operator-norm factor: the global lift has norm at most the original
dense-carrier constant. -/
theorem realLinearDenseIsometricAmbientExtension_opNorm_le
    (u : E →ₗ[ℝ] F)
    (e : E →ₗ[ℝ] H)
    (J : H →ₗᵢ[ℝ] B)
    (hDense : DenseRange e)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hBound : ∀ x, ‖u x‖ ≤ C * ‖e x‖) :
    ‖realLinearDenseIsometricAmbientExtension
        u e J hDense C hC hBound‖ ≤ C := by
  exact ContinuousLinearMap.opNorm_le_bound _ hC
    (realLinearDenseIsometricAmbientExtension_norm_le
      u e J hDense C hC hBound)

end MathlibAnalytic
end MGAP4D

end
