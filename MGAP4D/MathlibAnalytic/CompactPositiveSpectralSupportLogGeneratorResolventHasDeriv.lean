import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventDifferentiability
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter Asymptotics
open scoped InnerProductSpace LinearPMap Topology

noncomputable section

universe u

/-- The canonical ambient resolvent family of a coercive unbounded real-linear
operator is operator-norm differentiable throughout the coercive gap.  Its
derivative is the square of the resolvent.  The proof is obtained directly from
the quadratic Taylor remainder established on the actual unbounded-operator
domain; no boundedness of the forward operator is introduced. -/
theorem realLinearPMapAmbientResolventFamily_hasDerivAt
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    HasDerivAt F ((F lambda).comp (F lambda)) lambda := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  let d : ℝ := (|lambda| + c) / 2
  have hld : |lambda| < d := by
    dsimp [d]
    linarith
  have hdc : d < c := by
    dsimp [d]
    linarith
  have hd : 0 ≤ d := (abs_nonneg lambda).trans hld.le
  have hlocal : ∀ᶠ mu in 𝓝 lambda, |mu| ≤ d := by
    have hopen : IsOpen {x : ℝ | |x| < d} :=
      isOpen_lt continuous_abs continuous_const
    have hmem : lambda ∈ {x : ℝ | |x| < d} := hld
    filter_upwards [hopen.mem_nhds hmem] with mu hmu
    exact hmu.le
  have hO :
      (fun mu : ℝ =>
        F mu - F lambda - (mu - lambda) • (F lambda).comp (F lambda))
        =O[𝓝 lambda] (fun mu : ℝ => ‖mu - lambda‖ ^ 2) := by
    apply IsBigO.of_bound ((c - d)⁻¹ ^ 3)
    filter_upwards [hlocal] with mu hmu
    have hquad :=
      realLinearPMapAmbientResolventFamily_firstOrderRemainder_norm_le_inner_gap
        A c d hc hd hdc hNorm hKer hSurj lambda mu hld.le hmu
    simpa [F, Real.norm_eq_abs, abs_pow, abs_of_nonneg (sq_nonneg (mu - lambda)),
      mul_comm] using hquad
  have hsmall :
      (fun mu : ℝ => ‖mu - lambda‖ ^ 2) =o[𝓝 lambda]
        (fun mu : ℝ => mu - lambda) :=
    isLittleO_pow_sub_sub lambda (by norm_num)
  exact HasDerivAt.of_isLittleO (hO.trans_isLittleO hsmall)

/-- Differentiability receipt on the full open coercive gap. -/
theorem realLinearPMapAmbientResolventFamily_differentiableAt
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    DifferentiableAt ℝ
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj) lambda :=
  (realLinearPMapAmbientResolventFamily_hasDerivAt
    A c hc hNorm hKer hSurj lambda hlambda).differentiableAt

/-- The derivative selected by Mathlib agrees with the exact resolvent square. -/
theorem realLinearPMapAmbientResolventFamily_deriv_eq_comp_self
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    deriv F lambda = (F lambda).comp (F lambda) := by
  dsimp only
  exact (realLinearPMapAmbientResolventFamily_hasDerivAt
    A c hc hNorm hKer hSurj lambda hlambda).deriv

/-- The canonical resolvent family is continuous at every point of the open gap. -/
theorem realLinearPMapAmbientResolventFamily_continuousAt
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    ContinuousAt
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj) lambda :=
  (realLinearPMapAmbientResolventFamily_hasDerivAt
    A c hc hNorm hKer hSurj lambda hlambda).continuousAt

/-- The exact derivative value varies continuously throughout the open gap. -/
theorem realLinearPMapAmbientResolventFamily_derivativeValue_continuousAt
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    ContinuousAt (fun mu => (F mu).comp (F mu)) lambda := by
  dsimp only
  have hF := realLinearPMapAmbientResolventFamily_continuousAt
    A c hc hNorm hKer hSurj lambda hlambda
  exact hF.clm_comp hF

end

end MathlibAnalytic
end MGAP4D
