import Mathlib.Tactic

/-!
# Scalar inverse-square perturbation

A small model-independent estimate used by normalized transfer operators.

If positive numbers x,y admit positive lower bounds mx,my, then

  |x^{-2} - y^{-2}|
    <= mx^{-1} my^{-1} (mx^{-1} + my^{-1}) |x-y|.

Keeping this scalar avoids unfolding large operator-valued expressions inside
inverse-square arithmetic.
-/

namespace MGAP4D
namespace MathlibAnalytic

/-- Inverse-square variation on the positive half-line, controlled by explicit
positive lower bounds for both arguments. -/
theorem real_inv_sq_norm_sub_inv_sq_le_of_pos_lower_bounds
    (x y mx my : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hmx : 0 < mx)
    (hmy : 0 < my)
    (hmx_le : mx ≤ x)
    (hmy_le : my ≤ y) :
    ‖(x ^ 2)⁻¹ - (y ^ 2)⁻¹‖ ≤
      (mx⁻¹ * my⁻¹ * (mx⁻¹ + my⁻¹)) * ‖x - y‖ := by
  have hxInvPos : 0 < x⁻¹ := inv_pos.mpr hx
  have hyInvPos : 0 < y⁻¹ := inv_pos.mpr hy
  have hmxInvPos : 0 < mx⁻¹ := inv_pos.mpr hmx
  have hmyInvPos : 0 < my⁻¹ := inv_pos.mpr hmy
  have hxInv_le : x⁻¹ ≤ mx⁻¹ :=
    (inv_le_inv₀ hx hmx).2 hmx_le
  have hyInv_le : y⁻¹ ≤ my⁻¹ :=
    (inv_le_inv₀ hy hmy).2 hmy_le
  have hInvSubIdentity :
      x⁻¹ - y⁻¹ = (y - x) * (x⁻¹ * y⁻¹) := by
    field_simp [hx.ne', hy.ne']
    <;> ring
  have hInvSub :
      ‖x⁻¹ - y⁻¹‖ ≤
        (mx⁻¹ * my⁻¹) * ‖x - y‖ := by
    calc
      ‖x⁻¹ - y⁻¹‖ =
          (x⁻¹ * y⁻¹) * ‖x - y‖ := by
            rw [hInvSubIdentity, norm_mul, norm_mul, norm_sub_rev]
            simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hx, abs_of_pos hy]
            ring
      _ ≤ (mx⁻¹ * my⁻¹) * ‖x - y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hxInv_le hyInv_le hyInvPos.le hmxInvPos.le)
          (norm_nonneg _)
  have hInvAdd :
      ‖x⁻¹ + y⁻¹‖ ≤ mx⁻¹ + my⁻¹ := by
    calc
      ‖x⁻¹ + y⁻¹‖ ≤ ‖x⁻¹‖ + ‖y⁻¹‖ := norm_add_le _ _
      _ = x⁻¹ + y⁻¹ := by
        simp only [Real.norm_eq_abs, abs_of_pos hxInvPos, abs_of_pos hyInvPos]
      _ ≤ mx⁻¹ + my⁻¹ := add_le_add hxInv_le hyInv_le
  rw [inv_pow, inv_pow]
  calc
    ‖x⁻¹ ^ 2 - y⁻¹ ^ 2‖ =
        ‖(x⁻¹ - y⁻¹) * (x⁻¹ + y⁻¹)‖ := by
          congr 1
          ring
    _ = ‖x⁻¹ - y⁻¹‖ * ‖x⁻¹ + y⁻¹‖ := norm_mul _ _
    _ ≤
        ((mx⁻¹ * my⁻¹) * ‖x - y‖) *
          ‖x⁻¹ + y⁻¹‖ := by
      exact mul_le_mul_of_nonneg_right hInvSub (norm_nonneg _)
    _ ≤
        ((mx⁻¹ * my⁻¹) * ‖x - y‖) *
          (mx⁻¹ + my⁻¹) := by
      exact mul_le_mul_of_nonneg_left hInvAdd
        (mul_nonneg
          (mul_nonneg hmxInvPos.le hmyInvPos.le)
          (norm_nonneg _))
    _ =
        (mx⁻¹ * my⁻¹ * (mx⁻¹ + my⁻¹)) * ‖x - y‖ := by
      ring

end MathlibAnalytic
end MGAP4D
