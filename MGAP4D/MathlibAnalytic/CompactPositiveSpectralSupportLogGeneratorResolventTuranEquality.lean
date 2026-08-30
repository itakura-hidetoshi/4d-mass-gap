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

/-- Equality in the positive self-adjoint moment log-convexity inequality is
rigid: for a nonzero vector it occurs exactly when that vector is a single
spectral mode of the operator.

The forward implication is a weighted-variance argument.  Writing
`a = ⟨A^n u,u⟩`, `b = ⟨A^(n+1)u,u⟩` and
`z = a • A u - b • u`, the Turán equality makes
`⟨A^n z,z⟩` vanish.  Strict positivity of every power of `A` forces `z = 0`,
and `a > 0` then gives `A u = (b / a) • u`. -/
theorem realContinuousLinearMap_pow_inner_logConvex_eq_iff_eigenmode
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (hself : IsSelfAdjoint A) (hinj : Function.Injective A)
    (hpos : ∀ z : E, z ≠ 0 → 0 < inner ℝ (A z) z)
    (n : ℕ) (u : E) (hu : u ≠ 0) :
    (inner ℝ ((A ^ (n + 1)) u) u) ^ 2 =
        inner ℝ ((A ^ n) u) u * inner ℝ ((A ^ (n + 2)) u) u ↔
      ∃ r : ℝ, A u = r • u := by
  constructor
  · intro heq
    set a : ℝ := inner ℝ ((A ^ n) u) u with haDef
    set b : ℝ := inner ℝ ((A ^ (n + 1)) u) u with hbDef
    set d : ℝ := inner ℝ ((A ^ (n + 2)) u) u with hdDef
    have ha : 0 < a := by
      rw [haDef]
      exact
        realContinuousLinearMap_pow_inner_pos_of_selfAdjoint_of_inner_pos
          A hself hinj hpos n u hu
    have heq' : b ^ 2 = a * d := by
      simpa [haDef, hbDef, hdDef] using heq
    have hsymm : A.toLinearMap.IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hself
    have hshift : inner ℝ ((A ^ n) (A u)) (A u) = d := by
      rw [hdDef]
      exact (realContinuousLinearMap_pow_inner_shift_two A hself n u).symm
    have hcrossRight : inner ℝ ((A ^ n) (A u)) u = b := by
      rw [hbDef, pow_succ]
      rfl
    have hcrossLeft : inner ℝ ((A ^ n) u) (A u) = b := by
      calc
        inner ℝ ((A ^ n) u) (A u) = inner ℝ (A u) ((A ^ n) u) :=
          real_inner_comm _ _
        _ = inner ℝ u (A ((A ^ n) u)) := hsymm u ((A ^ n) u)
        _ = inner ℝ (A ((A ^ n) u)) u := real_inner_comm _ _
        _ = b := by
          rw [hbDef]
          have hpow : A ^ (n + 1) = A * A ^ n := by
            rw [show n + 1 = 1 + n by omega, pow_add, pow_one]
          rw [hpow]
          rfl
    set z : E := a • A u - b • u with hzDef
    have hzquad : inner ℝ ((A ^ n) z) z = 0 := by
      rw [hzDef]
      simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hshift, hcrossRight, hcrossLeft, ← haDef]
      nlinarith
    have hz : z = 0 := by
      by_contra hz0
      have hzpos :=
        realContinuousLinearMap_pow_inner_pos_of_selfAdjoint_of_inner_pos
          A hself hinj hpos n z hz0
      rw [hzquad] at hzpos
      exact (lt_irrefl 0) hzpos
    have hsub : a • A u - b • u = 0 := by
      rw [← hzDef, hz]
    have hlin : a • A u = b • u := sub_eq_zero.mp hsub
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hscaled := congrArg (fun w : E => a⁻¹ • w) hlin
    refine ⟨b / a, ?_⟩
    simpa [smul_smul, ha0, div_eq_mul_inv, mul_comm] using hscaled
  · rintro ⟨r, hr⟩
    have hpow : ∀ k : ℕ, (A ^ k) u = (r ^ k) • u := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ]
          change (A ^ k) (A u) = (r ^ (k + 1)) • u
          rw [hr, map_smul, ih]
          simp [smul_smul, pow_succ, mul_comm]
    rw [hpow (n + 1), hpow n, hpow (n + 2)]
    simp only [real_inner_smul_left]
    have hp1 : r ^ (n + 1) = r ^ n * r := by
      exact pow_succ r n
    have hp2 : r ^ (n + 2) = (r ^ n * r) * r := by
      calc
        r ^ (n + 2) = r ^ (n + 1) * r := by
          simpa [Nat.add_assoc] using pow_succ r (n + 1)
        _ = (r ^ n * r) * r := by rw [hp1]
    rw [hp1, hp2]
    ring

/-- Coercive ambient-resolvent specialization of moment equality rigidity. -/
theorem realLinearPMapAmbientResolventFamily_pow_inner_logConvex_eq_iff_eigenmode
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (lambda : ℝ) (hlambda : |lambda| < c) (n : ℕ) (u : E) (hu : u ≠ 0) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound A c hc hNorm hKer hSurj lambda
    (inner ℝ ((F ^ (n + 1)) u) u) ^ 2 =
        inner ℝ ((F ^ n) u) u * inner ℝ ((F ^ (n + 2)) u) u ↔
      ∃ r : ℝ, F u = r • u := by
  dsimp only
  exact
    realContinuousLinearMap_pow_inner_logConvex_eq_iff_eigenmode
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

/-- Equality of two consecutive factorial-normalized derivative ratios occurs
exactly for a single ambient-resolvent spectral mode.  Thus the weak order in
derivative degree is strict precisely away from one-mode states. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_eigenmode
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound A c hc hNorm hKer hSurj lambda
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) =
      iteratedDeriv (n + 2) q lambda /
        ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda) ↔
      ∃ r : ℝ, F u = r • u := by
  dsimp only
  let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj lambda
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
  have hmomentIff :=
    realLinearPMapAmbientResolventFamily_pow_inner_logConvex_eq_iff_eigenmode
      A c hc hNorm hKer hSurj hSelf hQuad lambda hlambda (n + 1) u hu
  dsimp only at hmomentIff
  constructor
  · intro hratio
    have hcross := (div_eq_div_iff hden0.ne' hden1.ne').mp hratio
    rw [realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
        A c hc hNorm hKer hSurj u n lambda hlambda,
      realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
        A c hc hNorm hKer hSurj u (n + 1) lambda hlambda,
      realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
        A c hc hNorm hKer hSurj u (n + 2) lambda hlambda] at hcross
    change
      (((n + 1).factorial : ℝ) * inner ℝ ((F ^ (n + 2)) u) u) *
          ((n + 2 : ℝ) *
            (((n + 1).factorial : ℝ) * inner ℝ ((F ^ (n + 2)) u) u)) =
        (((n + 2).factorial : ℝ) * inner ℝ ((F ^ (n + 3)) u) u) *
          ((n + 1 : ℝ) *
            ((n.factorial : ℝ) * inner ℝ ((F ^ (n + 1)) u) u)) at hcross
    have hcoef : 0 < (n + 2 : ℝ) * (n + 1 : ℝ) ^ 2 * ((n.factorial : ℝ) ^ 2) := by
      positivity
    have hmoment :
        (inner ℝ ((F ^ (n + 2)) u) u) ^ 2 =
          inner ℝ ((F ^ (n + 1)) u) u * inner ℝ ((F ^ (n + 3)) u) u := by
      norm_num [Nat.factorial_succ] at hcross
      ring_nf at hcross
      nlinarith
    exact hmomentIff.mp hmoment
  · intro hmode
    have hmoment := hmomentIff.mpr hmode
    apply (div_eq_div_iff hden0.ne' hden1.ne').mpr
    rw [realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
        A c hc hNorm hKer hSurj u n lambda hlambda,
      realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
        A c hc hNorm hKer hSurj u (n + 1) lambda hlambda,
      realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
        A c hc hNorm hKer hSurj u (n + 2) lambda hlambda]
    change
      (((n + 1).factorial : ℝ) * inner ℝ ((F ^ (n + 2)) u) u) *
          ((n + 2 : ℝ) *
            (((n + 1).factorial : ℝ) * inner ℝ ((F ^ (n + 2)) u) u)) =
        (((n + 2).factorial : ℝ) * inner ℝ ((F ^ (n + 3)) u) u) *
          ((n + 1 : ℝ) *
            ((n.factorial : ℝ) * inner ℝ ((F ^ (n + 1)) u) u))
    norm_num [Nat.factorial_succ]
    ring_nf
    nlinarith

end

end MathlibAnalytic
end MGAP4D
