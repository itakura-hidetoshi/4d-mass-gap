import MGAP4D.MathlibAnalytic.ConvexSecantDecayRate
import Mathlib.Tactic

/-!
# Telescoping equal-step secant decay rates

For a real-valued function `f` and a fixed step `h`, the equal-step secant
decay rates

`(f(ih) - f(ih+h)) / h`

telescope exactly.  Summing the first `n` rates gives the endpoint difference

`(f 0 - f(nh)) / h`.

No positivity or nonzero assumption on `h` is required: in a field Lean's
zero-division convention makes the identity valid at `h = 0` as well.
-/

namespace MGAP4D

open scoped BigOperators

/-- Equal-step secant decay rates telescope to the endpoint decay. -/
theorem sum_range_secantDecayRate_equalStep
    (f : ℝ → ℝ) (h : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n,
        secantDecayRate f ((i : ℝ) * h) ((i : ℝ) * h + h) =
      (f 0 - f ((n : ℝ) * h)) / h := by
  induction n with
  | zero => simp [secantDecayRate]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold secantDecayRate
      have hden : ((n : ℝ) * h + h) - (n : ℝ) * h = h := by ring
      rw [hden]
      have hsucc : ((n + 1 : ℕ) : ℝ) * h = (n : ℝ) * h + h := by
        norm_num
        ring
      rw [hsucc]
      ring

end MGAP4D
