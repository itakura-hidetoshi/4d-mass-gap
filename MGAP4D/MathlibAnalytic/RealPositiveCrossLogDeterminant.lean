import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Positive determinant and exact logarithmic cross ratio

The positive product multiplying the exponential difference is retained.
This scalar identity does not make any claim about a signed physical source.
-/
namespace MGAP4D.MathlibAnalytic
noncomputable section
set_option autoImplicit false

/-- Exact determinant identity for four strictly positive real entries. -/
theorem realPositiveCrossDet_eq_exp_crossLog
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a * d - b * c = b * c *
      (Real.exp ((Real.log a - Real.log c) - (Real.log b - Real.log d)) - 1) := by
  have he : Real.exp ((Real.log a - Real.log c) - (Real.log b - Real.log d)) =
      (a * d) / (b * c) := by
    simp only [Real.exp_sub, Real.exp_log ha, Real.exp_log hb,
      Real.exp_log hc, Real.exp_log hd]
    field_simp [hb.ne', hc.ne', hd.ne'] <;> ring
  rw [he]
  field_simp [hb.ne', hc.ne'] <;> ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.realPositiveCrossDet_eq_exp_crossLog
