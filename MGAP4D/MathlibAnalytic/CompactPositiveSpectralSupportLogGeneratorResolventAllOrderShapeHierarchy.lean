import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventGlobalShape
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- Every level of the nonzero quadratic support-resolvent derivative hierarchy
is strictly convex on the full symmetric coercive gap.  Thus strict convexity
is not a zeroth-order accident: it propagates through the entire derivative
tower because the next derivative level is strictly increasing. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_strictConvexOn
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E)
    (hu : u ≠ 0)
    (n : ℕ) :
    StrictConvexOn ℝ (Set.Ioo (-c) c)
      (iteratedDeriv n
        (realLinearPMapAmbientResolventQuadraticAmplitude
          A c hc hNorm hKer hSurj u)) := by
  let q := realLinearPMapAmbientResolventQuadraticAmplitude
    A c hc hNorm hKer hSurj u
  let qn := iteratedDeriv n q
  change StrictConvexOn ℝ (Set.Ioo (-c) c) qn
  have hderivMono : StrictMonoOn (deriv qn) (Set.Ioo (-c) c) := by
    have hnext :=
      realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_strictMonoOn
        A c hc hNorm hKer hSurj hSelf hQuad u hu (n + 1)
    simpa only [qn, q, iteratedDeriv_succ] using hnext
  have hderivMonoInterior :
      StrictMonoOn (deriv qn) (interior (Set.Ioo (-c) c)) := by
    simpa only [interior_Ioo] using hderivMono
  have hcont : ContinuousOn qn (Set.Ioo (-c) c) := by
    intro lambda hlambda
    have hnext :=
      realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
        A c hc hNorm hKer hSurj hSelf hQuad u hu (n + 1) lambda
        (abs_lt.mpr hlambda)
    have hdpos : 0 < deriv qn lambda := by
      simpa only [qn, q, iteratedDeriv_succ] using hnext
    exact
      (differentiableAt_of_deriv_ne_zero hdpos.ne').continuousAt.continuousWithinAt
  exact hderivMonoInterior.strictConvexOn_of_deriv (convex_Ioo (-c) c) hcont

/-- Every derivative level also identifies the spectral parameter uniquely on
the coercive gap. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_injOn
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E)
    (hu : u ≠ 0)
    (n : ℕ) :
    Set.InjOn
      (iteratedDeriv n
        (realLinearPMapAmbientResolventQuadraticAmplitude
          A c hc hNorm hKer hSurj u))
      (Set.Ioo (-c) c) :=
  (realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_strictMonoOn
    A c hc hNorm hKer hSurj hSelf hQuad u hu n).injOn

/-- Three-point form of the all-order strict shape theorem: for every
`x < y < z` in the coercive gap, the adjacent secant slope of the `n`-th
response level strictly increases from `[x,y]` to `[y,z]`. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_slope_strict_mono_adjacent
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (n : ℕ) {x y z : ℝ}
    (hx : x ∈ Set.Ioo (-c) c) (hz : z ∈ Set.Ioo (-c) c) (hxy : x < y) (hyz : y < z) :
    let q := iteratedDeriv n
      (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u)
    (q y - q x) / (y - x) < (q z - q y) / (z - y) := by
  dsimp only
  exact
    (realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_strictConvexOn
      A c hc hNorm hKer hSurj hSelf hQuad u hu n).slope_strict_mono_adjacent
        hx hz hxy hyz

end

end MathlibAnalytic
end MGAP4D
