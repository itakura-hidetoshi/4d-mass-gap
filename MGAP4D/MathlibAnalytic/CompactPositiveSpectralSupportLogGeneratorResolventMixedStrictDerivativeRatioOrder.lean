import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventDerivativeRatioParameterMonotonicity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- At every derivative order, the normalized support-resolvent response scale
is injective in the spectral parameter on the full coercive gap. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_injOn
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun) (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (n : ℕ) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    Set.InjOn (fun lambda : ℝ =>
      iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda)) (Set.Ioo (-c) c) := by
  exact
    (realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_strictMonoOn
      A c hc hNorm hKer hSurj hSelf hQuad u hu n).injOn

/-- Mixed strict comparison: if derivative order does not decrease and the
spectral parameter moves strictly to the right, then the normalized response
scale increases strictly.  No non-eigenvector hypothesis is required. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_lt_of_le_of_lt
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun) (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) {n m : ℕ} (hnm : n ≤ m)
    {lambda mu : ℝ} (hlambda : lambda ∈ Set.Ioo (-c) c)
    (hmu : mu ∈ Set.Ioo (-c) c) (hlm : lambda < mu) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) <
      iteratedDeriv (m + 1) q mu /
        ((m + 1 : ℝ) * iteratedDeriv m q mu) := by
  dsimp only
  calc
    iteratedDeriv (n + 1)
          (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u) lambda /
        ((n + 1 : ℝ) * iteratedDeriv n
          (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u) lambda) ≤
      iteratedDeriv (m + 1)
          (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u) lambda /
        ((m + 1 : ℝ) * iteratedDeriv m
          (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u) lambda) :=
      realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_le_of_le
        A c hc hNorm hKer hSurj hSelf hQuad u hu lambda (abs_lt.mpr hlambda) hnm
    _ < iteratedDeriv (m + 1)
          (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u) mu /
        ((m + 1 : ℝ) * iteratedDeriv m
          (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u) mu) :=
      realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_strictMonoOn
        A c hc hNorm hKer hSurj hSelf hQuad u hu m hlambda hmu hlm

end

end MathlibAnalytic
end MGAP4D
