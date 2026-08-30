import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventDerivativeRatioMonotonicity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- At every fixed point of the full coercive gap, the factorial-normalized
consecutive derivative ratio is a monotone sequence in derivative order. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_monotone
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    Monotone (fun n : ℕ =>
      iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda)) := by
  dsimp only
  apply monotone_nat_of_le_succ
  intro n
  exact realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_mono
    A c hc hNorm hKer hSurj hSelf hQuad u hu n lambda hlambda

/-- Global order comparison form: any lower derivative-ratio order is bounded
by any higher one, not merely by the adjacent successor. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_le_of_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (lambda : ℝ) (hlambda : |lambda| < c)
    {n m : ℕ} (hnm : n ≤ m) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) ≤
      iteratedDeriv (m + 1) q lambda /
        ((m + 1 : ℝ) * iteratedDeriv m q lambda) := by
  dsimp only
  exact
    (realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_monotone
      A c hc hNorm hKer hSurj hSelf hQuad u hu lambda hlambda) hnm

end

end MathlibAnalytic
end MGAP4D
