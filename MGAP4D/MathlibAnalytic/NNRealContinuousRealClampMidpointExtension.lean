import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

/-!
# Continuous real clamp extension of `NNReal` functions

A function on nonnegative reals can be viewed canonically as a function on all
reals by precomposing with `Real.toNNReal`.  Since `Real.toNNReal` is continuous,
continuity is preserved.  Moreover, a midpoint inequality on `NNReal` transfers
exactly to pairs of nonnegative real arguments.

This isolates the generic topology/algebra needed to move physical Euclidean
correlations from the `NNReal` semigroup parameter to the real half-line
`Set.Ici 0`, where Mathlib's real convexity API is available.
-/

namespace MGAP4D

/-- Canonical clamp extension of `f : NNReal → ℝ` to all real arguments. -/
def nnrealRealClampExtension (f : NNReal → ℝ) (t : ℝ) : ℝ :=
  f t.toNNReal

/-- Continuous functions on `NNReal` have continuous real clamp extensions. -/
theorem nnrealRealClampExtension_continuous
    (f : NNReal → ℝ) (hf : Continuous f) :
    Continuous (nnrealRealClampExtension f) := by
  exact hf.comp continuous_real_toNNReal

/-- The real clamp extension agrees with the original function after coercion
of every nonnegative argument. -/
@[simp]
theorem nnrealRealClampExtension_coe
    (f : NNReal → ℝ) (t : NNReal) :
    nnrealRealClampExtension f (t : ℝ) = f t := by
  simp [nnrealRealClampExtension]

/-- A standard midpoint inequality on `NNReal` transfers to arbitrary
nonnegative real arguments under the clamp extension. -/
theorem nnrealRealClampExtension_two_mul_midpoint_le
    (f : NNReal → ℝ)
    (hmidpoint : ∀ s t : NNReal,
      2 * f ((s + t) / 2) ≤ f s + f t)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    2 * nnrealRealClampExtension f ((s + t) / 2) ≤
      nnrealRealClampExtension f s + nnrealRealClampExtension f t := by
  have hst : 0 ≤ (s + t) / 2 := by positivity
  have harg :
      Real.toNNReal ((s + t) / 2) =
        (Real.toNNReal s + Real.toNNReal t) / 2 := by
    apply NNReal.eq
    simp [Real.toNNReal_of_nonneg hs, Real.toNNReal_of_nonneg ht,
      Real.toNNReal_of_nonneg hst]
  have h := hmidpoint (Real.toNNReal s) (Real.toNNReal t)
  simpa only [nnrealRealClampExtension, harg] using h

/-- Average-value form of the transferred midpoint inequality. -/
theorem nnrealRealClampExtension_midpoint_le_average
    (f : NNReal → ℝ)
    (hmidpoint : ∀ s t : NNReal,
      2 * f ((s + t) / 2) ≤ f s + f t)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    nnrealRealClampExtension f ((s + t) / 2) ≤
      (nnrealRealClampExtension f s + nnrealRealClampExtension f t) / 2 := by
  have h := nnrealRealClampExtension_two_mul_midpoint_le
    f hmidpoint hs ht
  linarith

end MGAP4D
