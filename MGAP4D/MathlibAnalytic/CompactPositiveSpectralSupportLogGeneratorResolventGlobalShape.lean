import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventStrictAbsoluteMonotonicity
import Mathlib.Analysis.Convex.Deriv
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
is strictly increasing on the full symmetric coercive gap.

The derivative of the `n`-th level is exactly the `(n+1)`-st iterated
derivative, which is strictly positive by strict absolute monotonicity. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_strictMonoOn
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
    StrictMonoOn
      (iteratedDeriv n
        (realLinearPMapAmbientResolventQuadraticAmplitude
          A c hc hNorm hKer hSurj u))
      (Set.Ioo (-c) c) := by
  let q := realLinearPMapAmbientResolventQuadraticAmplitude
    A c hc hNorm hKer hSurj u
  have hdpos : ∀ lambda ∈ Set.Ioo (-c) c,
      0 < deriv (iteratedDeriv n q) lambda := by
    intro lambda hlambda
    have hnext :=
      realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
        A c hc hNorm hKer hSurj hSelf hQuad u hu (n + 1) lambda
        (abs_lt.mpr hlambda)
    simpa only [iteratedDeriv_succ] using hnext
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-c) c)
  · intro lambda hlambda
    exact
      (differentiableAt_of_deriv_ne_zero (hdpos lambda hlambda).ne').continuousAt.continuousWithinAt
  · simpa only [interior_Ioo] using hdpos

/-- The nonzero quadratic support-resolvent amplitude itself is strictly
increasing on the whole coercive gap. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_strictMonoOn
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
    (hu : u ≠ 0) :
    StrictMonoOn
      (realLinearPMapAmbientResolventQuadraticAmplitude
        A c hc hNorm hKer hSurj u)
      (Set.Ioo (-c) c) := by
  simpa only [iteratedDeriv_zero] using
    (realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_strictMonoOn
      A c hc hNorm hKer hSurj hSelf hQuad u hu 0)

/-- Hence the spectral parameter is identified uniquely by a nonzero quadratic
support-resolvent amplitude inside the coercive gap. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_injOn
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
    (hu : u ≠ 0) :
    Set.InjOn
      (realLinearPMapAmbientResolventQuadraticAmplitude
        A c hc hNorm hKer hSurj u)
      (Set.Ioo (-c) c) :=
  (realLinearPMapAmbientResolventQuadraticAmplitude_strictMonoOn
    A c hc hNorm hKer hSurj hSelf hQuad u hu).injOn

/-- The nonzero quadratic support-resolvent amplitude is strictly convex on
its full symmetric coercive gap.  Its derivative is the first level of the
hierarchy, and that level is itself strictly increasing because the second
scalar derivative is strictly positive everywhere in the gap. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_strictConvexOn
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
    (hu : u ≠ 0) :
    StrictConvexOn ℝ (Set.Ioo (-c) c)
      (realLinearPMapAmbientResolventQuadraticAmplitude
        A c hc hNorm hKer hSurj u) := by
  let q := realLinearPMapAmbientResolventQuadraticAmplitude
    A c hc hNorm hKer hSurj u
  have hderivMono : StrictMonoOn (deriv q) (Set.Ioo (-c) c) := by
    simpa only [iteratedDeriv_one] using
      (realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_strictMonoOn
        A c hc hNorm hKer hSurj hSelf hQuad u hu 1)
  have hderivMonoInterior :
      StrictMonoOn (deriv q) (interior (Set.Ioo (-c) c)) := by
    simpa only [interior_Ioo] using hderivMono
  have hcont : ContinuousOn q (Set.Ioo (-c) c) := by
    intro lambda hlambda
    have hfirst :=
      realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
        A c hc hNorm hKer hSurj hSelf hQuad u hu 1 lambda
        (abs_lt.mpr hlambda)
    have hdpos : 0 < deriv q lambda := by
      simpa only [iteratedDeriv_one] using hfirst
    exact
      (differentiableAt_of_deriv_ne_zero hdpos.ne').continuousAt.continuousWithinAt
  change StrictConvexOn ℝ (Set.Ioo (-c) c) q
  exact hderivMonoInterior.strictConvexOn_of_deriv (convex_Ioo (-c) c) hcont

end

end MathlibAnalytic
end MGAP4D
