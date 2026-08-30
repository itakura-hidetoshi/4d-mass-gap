import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventGlobalDerivativeRatioOrder
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- At every derivative order, the factorial-normalized consecutive derivative
ratio has strictly positive derivative throughout the full coercive gap. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_deriv_pos
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    0 < deriv (fun t : ℝ =>
      iteratedDeriv (n + 1) q t /
        ((n + 1 : ℝ) * iteratedDeriv n q t)) lambda := by
  let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
  change 0 < deriv (fun t : ℝ =>
    iteratedDeriv (n + 1) q t /
      ((n + 1 : ℝ) * iteratedDeriv n q t)) lambda
  have hn : 0 < iteratedDeriv n q lambda := by
    simpa [q] using
      (realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
        A c hc hNorm hKer hSurj hSelf hQuad u hu n lambda hlambda)
  have hn1 : 0 < iteratedDeriv (n + 1) q lambda := by
    simpa [q] using
      (realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
        A c hc hNorm hKer hSurj hSelf hQuad u hu (n + 1) lambda hlambda)
  have hn2 : 0 < iteratedDeriv (n + 2) q lambda := by
    simpa [q] using
      (realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
        A c hc hNorm hKer hSurj hSelf hQuad u hu (n + 2) lambda hlambda)
  have hdiffn : DifferentiableAt ℝ (iteratedDeriv n q) lambda := by
    apply differentiableAt_of_deriv_ne_zero
    simpa only [iteratedDeriv_succ] using hn1.ne'
  have hdiffn1 : DifferentiableAt ℝ (iteratedDeriv (n + 1) q) lambda := by
    apply differentiableAt_of_deriv_ne_zero
    simpa only [iteratedDeriv_succ] using hn2.ne'
  have hderivn : HasDerivAt (iteratedDeriv n q) (iteratedDeriv (n + 1) q lambda) lambda := by
    simpa only [iteratedDeriv_succ] using hdiffn.hasDerivAt
  have hderivn1 : HasDerivAt (iteratedDeriv (n + 1) q)
      (iteratedDeriv (n + 2) q lambda) lambda := by
    simpa only [iteratedDeriv_succ] using hdiffn1.hasDerivAt
  have hden_ne : (n + 1 : ℝ) * iteratedDeriv n q lambda ≠ 0 := by positivity
  have hratio := hderivn1.div (hderivn.const_mul (n + 1 : ℝ)) hden_ne
  change HasDerivAt (fun t : ℝ =>
      iteratedDeriv (n + 1) q t /
        ((n + 1 : ℝ) * iteratedDeriv n q t))
      ((iteratedDeriv (n + 2) q lambda * ((n + 1 : ℝ) * iteratedDeriv n q lambda) -
          iteratedDeriv (n + 1) q lambda *
            ((n + 1 : ℝ) * iteratedDeriv (n + 1) q lambda)) /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) ^ 2) lambda at hratio
  have hturan :=
    realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_turan
      A c hc hNorm hKer hSurj hSelf hQuad u hu n lambda hlambda
  change
    (n + 2 : ℝ) * (iteratedDeriv (n + 1) q lambda) ^ 2 ≤
      (n + 1 : ℝ) * iteratedDeriv n q lambda * iteratedDeriv (n + 2) q lambda at hturan
  have hnum :
      0 < iteratedDeriv (n + 2) q lambda *
          ((n + 1 : ℝ) * iteratedDeriv n q lambda) -
        iteratedDeriv (n + 1) q lambda *
          ((n + 1 : ℝ) * iteratedDeriv (n + 1) q lambda) := by
    nlinarith
  rw [hratio.deriv]
  exact div_pos hnum (sq_pos_of_pos (by positivity))

/-- At fixed derivative order, the normalized consecutive derivative ratio is
strictly increasing in the spectral parameter on the full coercive gap. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_strictMonoOn
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (n : ℕ) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    StrictMonoOn (fun lambda : ℝ =>
      iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda)) (Set.Ioo (-c) c) := by
  let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
  let R := fun lambda : ℝ =>
    iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  change StrictMonoOn R (Set.Ioo (-c) c)
  have hdpos : ∀ lambda ∈ Set.Ioo (-c) c, 0 < deriv R lambda := by
    intro lambda hlambda
    simpa [R, q] using
      (realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_deriv_pos
        A c hc hNorm hKer hSurj hSelf hQuad u hu n lambda (abs_lt.mpr hlambda))
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-c) c)
  · intro lambda hlambda
    exact
      (differentiableAt_of_deriv_ne_zero (hdpos lambda hlambda).ne').continuousAt.continuousWithinAt
  · simpa only [interior_Ioo] using hdpos

/-- Mixed order/parameter comparison: raising derivative order and moving the
spectral parameter to the right can only increase the normalized response scale. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_le_of_le_of_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) {n m : ℕ} (hnm : n ≤ m)
    {lambda mu : ℝ} (hlambda : lambda ∈ Set.Ioo (-c) c)
    (hmu : mu ∈ Set.Ioo (-c) c) (hlm : lambda ≤ mu) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) ≤
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
    _ ≤ iteratedDeriv (m + 1)
          (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u) mu /
        ((m + 1 : ℝ) * iteratedDeriv m
          (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u) mu) :=
      (realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_strictMonoOn
        A c hc hNorm hKer hSurj hSelf hQuad u hu m).monotoneOn hlambda hmu hlm

end

end MathlibAnalytic
end MGAP4D
