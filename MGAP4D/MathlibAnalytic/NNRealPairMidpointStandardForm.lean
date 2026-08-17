import MGAP4D.MathlibAnalytic.NNRealForwardMidpointPairConvexity
import Mathlib.Tactic

/-!
# Standard midpoint form on `NNReal`

The half-time pair inequality

`2 f (a+b) ≤ f (a+a) + f (b+b)`

is exactly the usual midpoint inequality after substituting `a = s/2` and
`b = t/2`.  This file performs that normalization once, independently of the
physical OS-semigroup layer.
-/

namespace MGAP4D

/-- Convert the doubled-endpoint half-time form of midpoint convexity into the
standard midpoint inequality on `NNReal`. -/
theorem nnreal_two_mul_midpoint_le_of_pair_doubled
    (f : NNReal → ℝ)
    (hpair : ∀ a b : NNReal,
      2 * f (a + b) ≤ f (a + a) + f (b + b))
    (s t : NNReal) :
    2 * f ((s + t) / 2) ≤ f s + f t := by
  have h := hpair (s / 2) (t / 2)
  have hmid : s / 2 + t / 2 = (s + t) / 2 := by
    apply NNReal.eq
    ring
  have hs : s / 2 + s / 2 = s := by
    apply NNReal.eq
    ring
  have ht : t / 2 + t / 2 = t := by
    apply NNReal.eq
    ring
  simpa only [hmid, hs, ht] using h

end MGAP4D
