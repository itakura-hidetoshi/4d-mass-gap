import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventStrictQuadraticPositivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- The coercively generated ambient resolvent has trivial kernel throughout
its symmetric gap.  This is a direct consequence of the actual-domain
preimage receipt and does not require the forward operator to be bounded. -/
theorem realLinearPMapAmbientResolventFamily_eq_zero_iff
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
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (y : E) :
    realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda y = 0 ↔ y = 0 := by
  constructor
  · intro hFy
    rcases realLinearPMapAmbientResolventFamily_exists_domain_preimage
        A c hc hNorm hKer hSurj lambda hlambda y with
      ⟨x, hxy, hFx⟩
    have hxcoe : (x : E) = 0 := by
      rw [← hFx]
      exact hFy
    have hx : x = 0 := by
      apply Subtype.ext
      exact hxcoe
    rw [← hxy, hx]
    simp [realLinearPMapDomainShift]
  · intro hy
    rw [hy]
    exact map_zero _

/-- Hence every bounded ambient resolvent in the coercive gap is injective. -/
theorem realLinearPMapAmbientResolventFamily_injective
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
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    Function.Injective
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda) := by
  intro y z hyz
  have hsub :
      realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda (y - z) = 0 := by
    rw [map_sub, hyz, sub_self]
  have hyz0 : y - z = 0 :=
    (realLinearPMapAmbientResolventFamily_eq_zero_iff
      A c hc hNorm hKer hSurj lambda hlambda (y - z)).mp hsub
  exact sub_eq_zero.mp hyz0

/-- For a self-adjoint coercive forward operator, the first scalar derivative
of every nonzero quadratic resolvent amplitude is strictly positive on the
whole symmetric coercive gap.  In particular the response is locally
strictly increasing everywhere in the gap. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_one_pos
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
    (u : E)
    (hu : u ≠ 0)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    0 < iteratedDeriv 1
      (realLinearPMapAmbientResolventQuadraticAmplitude
        A c hc hNorm hKer hSurj u)
      lambda := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hformula :=
    realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
      A c hc hNorm hKer hSurj u 1 lambda hlambda
  have hFself :=
    realLinearPMapAmbientResolventFamily_isSelfAdjoint_of_isSelfAdjoint
      A c hc hNorm hKer hSurj hSelf lambda hlambda
  have hFsymm : (F lambda).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hFself
  have hFu : F lambda u ≠ 0 := by
    intro hzero
    apply hu
    apply realLinearPMapAmbientResolventFamily_injective
      A c hc hNorm hKer hSurj lambda hlambda
    simpa [F] using hzero
  have hsymm :
      inner ℝ (F lambda (F lambda u)) u =
        inner ℝ (F lambda u) (F lambda u) := by
    exact hFsymm (F lambda u) u
  rw [hformula]
  norm_num
  change 0 < inner ℝ (F lambda (F lambda u)) u
  calc
    0 < inner ℝ (F lambda u) (F lambda u) := by
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hFu)
    _ = inner ℝ (F lambda (F lambda u)) u := hsymm.symm

end

end MathlibAnalytic
end MGAP4D
