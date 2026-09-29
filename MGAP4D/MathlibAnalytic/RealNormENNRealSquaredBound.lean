import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Real norm bounds from finite ENNReal squared estimates

The right-hand side must be finite before applying `ENNReal.toReal_mono`.
After that step, nonnegative square roots give the norm estimate without
cancelling or dividing by a residual. Both zero coefficient and zero residual
are included. The two vectors may belong to different seminormed groups.
-/

namespace MGAP4D.MathlibAnalytic

open scoped ENNReal

/-- Transfer the squared inequality to reals, using finiteness of the whole
right-hand side rather than treating `toReal` as globally monotone. -/
theorem norm_sq_le_toReal_mul_norm_sq_of_ofReal_norm_sq_le
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (A : ℝ≥0∞) (hA : A ≠ ⊤) (u : E) (v : F)
    (h : ENNReal.ofReal (‖u‖ ^ 2) ≤ A * ENNReal.ofReal (‖v‖ ^ 2)) :
    ‖u‖ ^ 2 ≤ A.toReal * ‖v‖ ^ 2 := by
  have hFinite : A * ENNReal.ofReal (‖v‖ ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top hA ENNReal.ofReal_ne_top
  have hReal := ENNReal.toReal_mono hFinite h
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg ‖u‖),
    ENNReal.toReal_ofReal (sq_nonneg ‖v‖)] using hReal

/-- The exact square-root coefficient, including all zero cases. -/
theorem norm_le_sqrt_toReal_mul_norm_of_ofReal_norm_sq_le
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (A : ℝ≥0∞) (hA : A ≠ ⊤) (u : E) (v : F)
    (h : ENNReal.ofReal (‖u‖ ^ 2) ≤ A * ENNReal.ofReal (‖v‖ ^ 2)) :
    ‖u‖ ≤ Real.sqrt A.toReal * ‖v‖ := by
  have hReal := norm_sq_le_toReal_mul_norm_sq_of_ofReal_norm_sq_le A hA u v h
  have hRoot : (Real.sqrt A.toReal) ^ 2 = A.toReal :=
    Real.sq_sqrt ENNReal.toReal_nonneg
  have hSquared : ‖u‖ ^ 2 ≤ (Real.sqrt A.toReal * ‖v‖) ^ 2 := by
    simpa only [mul_pow, hRoot] using hReal
  exact (sq_le_sq₀ (norm_nonneg u)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v))).mp hSquared

end MGAP4D.MathlibAnalytic
