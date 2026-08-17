import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Secant decay rates of convex functions

For a real-valued function `f`, define the secant decay rate on an ordered
pair `(s,t)` by

`(f s - f t) / (t - s)`.

This is the negative of the usual secant slope.  Hence convexity says that
adjacent secant decay rates are antitone: for `x < y < z`, the decay rate on
`[y,z]` is no larger than the decay rate on `[x,y]`.

The definition is separated from the physical OS layer so that the latter is a
direct instantiation of Mathlib's `ConvexOn.slope_mono_adjacent` theorem.
-/

namespace MGAP4D

/-- Negative secant slope, interpreted as an interval decay rate. -/
noncomputable def secantDecayRate (f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (f s - f t) / (t - s)

/-- Convexity makes adjacent secant decay rates antitone. -/
theorem ConvexOn.secantDecayRate_anti_adjacent
    {D : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ D f)
    {x y z : ℝ} (hx : x ∈ D) (hz : z ∈ D)
    (hxy : x < y) (hyz : y < z) :
    secantDecayRate f y z ≤ secantDecayRate f x y := by
  have h := hf.slope_mono_adjacent hx hz hxy hyz
  unfold secantDecayRate
  calc
    (f y - f z) / (z - y) = -((f z - f y) / (z - y)) := by ring
    _ ≤ -((f y - f x) / (y - x)) := neg_le_neg h
    _ = (f x - f y) / (y - x) := by ring

end MGAP4D
