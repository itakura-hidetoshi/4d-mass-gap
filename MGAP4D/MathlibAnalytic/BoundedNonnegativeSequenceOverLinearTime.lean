import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Bounded nonnegative sequences divided by linear time

A uniformly bounded nonnegative real sequence, divided by a positive constant
multiple of the natural-number time parameter, converges to zero.  This is the
pure real-analysis squeeze step needed to expose the fixed-positive-
regularization order-of-limits obstruction for physical OS correlations.
-/

namespace MGAP4D

open Filter
open scoped Topology

/-- A bounded nonnegative numerator divided by `(n : ℝ) * h`, with `h > 0`,
converges to zero. -/
theorem boundedNonnegativeSequence_div_natMul_tendsto_zero
    (f : ℕ → ℝ) (K h : ℝ)
    (hh : 0 < h)
    (hf0 : ∀ n : ℕ, 0 ≤ f n)
    (hfK : ∀ n : ℕ, f n ≤ K) :
    Tendsto (fun n : ℕ => f n / ((n : ℝ) * h)) atTop (𝓝 0) := by
  have hden :
      Tendsto (fun n : ℕ => (n : ℝ) * h) atTop atTop := by
    exact
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_mul_const hh
  have hupper :
      Tendsto (fun n : ℕ => K / ((n : ℝ) * h)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hden
  apply squeeze_zero
  · intro n
    exact div_nonneg (hf0 n) (mul_nonneg (Nat.cast_nonneg n) hh.le)
  · intro n
    exact div_le_div_of_nonneg_right (hfK n)
      (mul_nonneg (Nat.cast_nonneg n) hh.le)
  · exact hupper

end MGAP4D
