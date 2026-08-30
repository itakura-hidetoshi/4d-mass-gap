import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventTuranHierarchy
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- The factorial-normalized consecutive derivative ratio of every nonzero
coercive support-resolvent quadratic amplitude is nondecreasing in derivative
order.  This is the quotient form of the Turán hierarchy, made legitimate by
strict absolute positivity of every derivative level. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_mono
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) ≤
      iteratedDeriv (n + 2) q lambda /
        ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda) := by
  let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
  change iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda) ≤
    iteratedDeriv (n + 2) q lambda /
      ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda)
  have hn : 0 < iteratedDeriv n q lambda := by
    simpa [q] using
      (realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
        A c hc hNorm hKer hSurj hSelf hQuad u hu n lambda hlambda)
  have hn1 : 0 < iteratedDeriv (n + 1) q lambda := by
    simpa [q] using
      (realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
        A c hc hNorm hKer hSurj hSelf hQuad u hu (n + 1) lambda hlambda)
  have hden0 : 0 < (n + 1 : ℝ) * iteratedDeriv n q lambda := by positivity
  have hden1 : 0 < (n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda := by positivity
  rw [div_le_div_iff₀ hden0 hden1]
  have hturan :=
    realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_turan
      A c hc hNorm hKer hSurj hSelf hQuad u hu n lambda hlambda
  change
    iteratedDeriv (n + 1) q lambda *
        ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda) ≤
      iteratedDeriv (n + 2) q lambda *
        ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  nlinarith

end

end MathlibAnalytic
end MGAP4D
