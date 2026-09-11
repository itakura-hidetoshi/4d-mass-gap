import MGAP4D.MathlibAnalytic.NNRealContinuousRealClampMidpointExtension
import Mathlib.Tactic

/-!
# Multiplicative midpoint inequalities for real clamp extensions

A multiplicative midpoint inequality on `NNReal`

`f ((s+t)/2)^2 ≤ f s * f t`

transfers exactly to the canonical real clamp extension on nonnegative real
arguments.  Combining this with the additive midpoint inequality yields the
zero-safe regularized estimate

`(f̃(m)+ε)^2 ≤ (f̃(s)+ε)(f̃(t)+ε)`

for every `ε ≥ 0`.

The latter is the algebraic bridge needed before applying logarithms: positive
regularization avoids any separate zero case while introducing no new analytic
or physical assumption.
-/

namespace MGAP4D

/-- A multiplicative midpoint inequality on `NNReal` transfers to the real
clamp extension for arbitrary nonnegative real arguments. -/
theorem nnrealRealClampExtension_midpoint_sq_le_mul
    (f : NNReal → ℝ)
    (hmul : ∀ s t : NNReal,
      f ((s + t) / 2) ^ 2 ≤ f s * f t)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    nnrealRealClampExtension f ((s + t) / 2) ^ 2 ≤
      nnrealRealClampExtension f s * nnrealRealClampExtension f t := by
  have hst : 0 ≤ (s + t) / 2 := by positivity
  have harg :
      Real.toNNReal ((s + t) / 2) =
        (Real.toNNReal s + Real.toNNReal t) / 2 := by
    apply NNReal.eq
    simp [Real.toNNReal_of_nonneg hs, Real.toNNReal_of_nonneg ht,
      Real.toNNReal_of_nonneg hst]
  have h := hmul (Real.toNNReal s) (Real.toNNReal t)
  simpa only [nnrealRealClampExtension, harg] using h

/-- Additive and multiplicative midpoint inequalities combine to a regularized
multiplicative midpoint inequality for every nonnegative `ε`.

This elementary identity is the zero-safe precursor of logarithmic convexity:
a strictly positive `ε` makes every regularized value positive. -/
theorem nnrealRealClampExtension_add_eps_midpoint_sq_le_mul
    (f : NNReal → ℝ)
    (hadd : ∀ s t : NNReal,
      2 * f ((s + t) / 2) ≤ f s + f t)
    (hmul : ∀ s t : NNReal,
      f ((s + t) / 2) ^ 2 ≤ f s * f t)
    (ε : ℝ) (hε : 0 ≤ ε)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (nnrealRealClampExtension f ((s + t) / 2) + ε) ^ 2 ≤
      (nnrealRealClampExtension f s + ε) *
        (nnrealRealClampExtension f t + ε) := by
  have ha := nnrealRealClampExtension_two_mul_midpoint_le
    f hadd hs ht
  have hm := nnrealRealClampExtension_midpoint_sq_le_mul
    f hmul hs ht
  have hcross :
      0 ≤ ε *
        ((nnrealRealClampExtension f s + nnrealRealClampExtension f t) -
          2 * nnrealRealClampExtension f ((s + t) / 2)) :=
    mul_nonneg hε (sub_nonneg.mpr ha)
  nlinarith

end MGAP4D
