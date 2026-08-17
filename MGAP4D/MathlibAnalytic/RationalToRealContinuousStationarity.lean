import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Rat

/-!
# Rational-to-real continuous stationarity

This file isolates the purely topological `ℚ → ℝ` extension step used after rational-time
stationarity has been established.

The point is deliberately an uniqueness/continuity statement: density of `ℚ` in `ℝ` does not
construct a real-time process.  Rather, once a candidate real-time quantity is known to depend
continuously on the real shift and agrees with the rational-time quantity, its values are forced
by the rational values.
-/

namespace MGAP4D

/-- Two continuous maps out of `ℝ` into a Hausdorff space are equal as soon as they agree on all
rational points. -/
theorem continuous_eq_of_eq_on_rat
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {f g : ℝ → X}
    (hf : Continuous f) (hg : Continuous g)
    (hRat : ∀ q : ℚ, f (q : ℝ) = g (q : ℝ)) :
    f = g := by
  exact Rat.denseRange_cast.equalizer hf hg (by
    funext q
    exact hRat q)

/-- A continuous real-shift family that is stationary at every rational shift is stationary at
all real shifts. -/
theorem real_stationary_of_rational_stationary
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (F : ℝ → X)
    (hF : Continuous F)
    (hRat : ∀ q : ℚ, F (q : ℝ) = F 0) :
    ∀ r : ℝ, F r = F 0 := by
  have hConst : F = fun _ : ℝ => F 0 :=
    continuous_eq_of_eq_on_rat hF continuous_const hRat
  intro r
  exact congrFun hConst r

end MGAP4D
