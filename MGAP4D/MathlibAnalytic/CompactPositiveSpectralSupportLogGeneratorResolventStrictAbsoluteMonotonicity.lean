import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventStrictFirstResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- Every power of an injective positive self-adjoint bounded real-Hilbert
endomorphism has a strictly positive quadratic form on every nonzero vector.

The proof is the strict analogue of the two-step positivity recursion.  At
level `k + 2`, self-adjointness moves the leftmost operator across the inner
product and reduces to level `k` on `A u`; injectivity guarantees that this new
vector remains nonzero. -/
theorem realContinuousLinearMap_pow_inner_pos_of_selfAdjoint_of_inner_pos
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →L[ℝ] E)
    (hself : IsSelfAdjoint A)
    (hinj : Function.Injective A)
    (hpos : ∀ u : E, u ≠ 0 → 0 < inner ℝ (A u) u)
    (n : ℕ)
    (u : E)
    (hu : u ≠ 0) :
    0 < inner ℝ ((A ^ n) u) u := by
  have hsymm : A.toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hself
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
      rcases n with _ | n
      · simpa [real_inner_self_eq_norm_sq] using
          sq_pos_of_pos (norm_pos_iff.mpr hu)
      · rcases n with _ | k
        · simpa using hpos u hu
        · have hpow : A ^ (k + 2) = A * (A ^ k) * A := by
            calc
              A ^ (k + 2) = A ^ (k + 1) * A := by
                simpa [Nat.add_assoc] using pow_succ A (k + 1)
              _ = (A * A ^ k) * A := by
                rw [show k + 1 = 1 + k by omega, pow_add, pow_one]
          rw [hpow]
          change 0 < inner ℝ (A ((A ^ k) (A u))) u
          have hs :
              inner ℝ (A ((A ^ k) (A u))) u =
                inner ℝ ((A ^ k) (A u)) (A u) := by
            exact hsymm ((A ^ k) (A u)) u
          rw [hs]
          have hAu : A u ≠ 0 := by
            intro hzero
            apply hu
            apply hinj
            simpa using hzero
          exact ih k (by omega) (A u) hAu

/-- Every power of the coercively generated bounded ambient resolvent is
strictly positive on nonzero vectors throughout the symmetric coercive gap.
This combines support-resolvent self-adjointness, strict quadratic positivity,
and the injectivity receipt without ever bounding the forward operator. -/
theorem realLinearPMapAmbientResolventFamily_pow_inner_pos
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
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (n : ℕ)
    (u : E)
    (hu : u ≠ 0) :
    0 < inner ℝ
      ((realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda ^ n) u)
      u := by
  exact
    realContinuousLinearMap_pow_inner_pos_of_selfAdjoint_of_inner_pos
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda)
      (realLinearPMapAmbientResolventFamily_isSelfAdjoint_of_isSelfAdjoint
        A c hc hNorm hKer hSurj hSelf lambda hlambda)
      (realLinearPMapAmbientResolventFamily_injective
        A c hc hNorm hKer hSurj lambda hlambda)
      (fun y hy =>
        realLinearPMapAmbientResolventFamily_inner_pos_of_quadratic_lower_bound
          A c hc hNorm hKer hSurj hQuad lambda hlambda y hy)
      n u hu

/-- Strict absolute monotonicity of the support-resolvent quadratic amplitude:
for every derivative order, every nonzero vector has strictly positive scalar
response throughout the full symmetric coercive gap.

This simultaneously contains strict quadratic positivity (`n = 0`) and the
strict first-response theorem (`n = 1`), and upgrades the previous all-order
nonnegativity receipt to strict positivity. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
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
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    0 < iteratedDeriv n
      (realLinearPMapAmbientResolventQuadraticAmplitude
        A c hc hNorm hKer hSurj u)
      lambda := by
  rw [realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
    A c hc hNorm hKer hSurj u n lambda hlambda]
  exact mul_pos (by positivity)
    (realLinearPMapAmbientResolventFamily_pow_inner_pos
      A c hc hNorm hKer hSurj hSelf hQuad lambda hlambda (n + 1) u hu)

end

end MathlibAnalytic
end MGAP4D
