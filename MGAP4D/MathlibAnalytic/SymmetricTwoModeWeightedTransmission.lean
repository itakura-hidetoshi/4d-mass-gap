import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic

/-!
# Two-mode weighted transmission through a symmetric operator

Let Q fix a constant mode u and multiply an orthogonal mode v by a real
coefficient lambda in [0,1]. A weighting W whose quadratic form is bounded
below by m >= 0 gives the following transmitted fluctuation floor:

  m * lambda * norm v <= norm (Q (W (v - c u))).

In particular, no offset can erase a nonzero v when m and lambda are positive.

The proof tests against v - lambda c u. It uses only symmetry, the two
stated eigenmode relations, positivity of W, and Cauchy--Schwarz. No
inverse operator, spectral completeness, compactness minimum, or target
response lower bound is assumed. W need not be linear for this estimate.

This is an abstract analytic lemma. Applying it to a physical Wilson
operator still requires the actual eigenmode identities and an independent
lower bound on its actual weight. It does not assert those model inputs.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace

set_option autoImplicit false

section RealInnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact Pythagorean square for an arbitrary offset along an orthogonal
mode; neither vector is required to have unit norm. -/
theorem orthogonal_twoMode_norm_sq (u v : E)
    (hvu : inner ℝ v u = 0) (c : ℝ) :
    ‖v - c • u‖ ^ 2 = ‖v‖ ^ 2 + c ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, hvu]
  simp only [mul_zero, sub_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- A nonnegative quadratic-form lower weight and two symmetric eigenmodes
give a quantitative transmission lower bound for every constant offset.
The lower weight and eigenmode relations are explicit hypotheses. -/
theorem symmetric_twoMode_weighted_norm_lower
    (Q : E →ₗ[ℝ] E) (hQ : Q.IsSymmetric) (W : E → E)
    (u v : E) (hvu : inner ℝ v u = 0)
    (m lambda : ℝ) (hm : 0 ≤ m)
    (hlambda : 0 ≤ lambda) (hlambda_one : lambda ≤ 1)
    (hQu : Q u = u) (hQv : Q v = lambda • v)
    (hW : ∀ x : E, m * ‖x‖ ^ 2 ≤ inner ℝ (W x) x)
    (c : ℝ) :
    m * lambda * ‖v‖ ≤ ‖Q (W (v - c • u))‖ := by
  let w : E := v - c • u
  let q : E := v - (lambda * c) • u
  have hw_sq : ‖w‖ ^ 2 = ‖v‖ ^ 2 + c ^ 2 * ‖u‖ ^ 2 :=
    orthogonal_twoMode_norm_sq u v hvu c
  have hq_sq :
      ‖q‖ ^ 2 = ‖v‖ ^ 2 + (lambda * c) ^ 2 * ‖u‖ ^ 2 :=
    orthogonal_twoMode_norm_sq u v hvu (lambda * c)
  have hlambda_sq : lambda ^ 2 ≤ 1 := by nlinarith
  have hscaled : (lambda * c) ^ 2 * ‖u‖ ^ 2 ≤ c ^ 2 * ‖u‖ ^ 2 := by
    calc
      (lambda * c) ^ 2 * ‖u‖ ^ 2 =
          lambda ^ 2 * (c ^ 2 * ‖u‖ ^ 2) := by ring
      _ ≤ 1 * (c ^ 2 * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hlambda_sq
          (mul_nonneg (sq_nonneg c) (sq_nonneg ‖u‖))
      _ = c ^ 2 * ‖u‖ ^ 2 := one_mul _
  have hq_le_w : ‖q‖ ≤ ‖w‖ := by
    have hsq : ‖q‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [hq_sq, hw_sq]
      exact add_le_add_left hscaled _
    nlinarith only [hsq, norm_nonneg q, norm_nonneg w]
  have hv_le_w : ‖v‖ ≤ ‖w‖ := by
    have hnonneg : 0 ≤ c ^ 2 * ‖u‖ ^ 2 :=
      mul_nonneg (sq_nonneg c) (sq_nonneg ‖u‖)
    nlinarith only [hw_sq, hnonneg, norm_nonneg v, norm_nonneg w]
  have hQq : Q q = lambda • w := by
    simp only [q, w, map_sub, map_smul, hQv, hQu, smul_sub, smul_smul]
  have hcross :
      lambda * (m * ‖w‖ ^ 2) ≤ ‖Q (W w)‖ * ‖w‖ := by
    calc
      lambda * (m * ‖w‖ ^ 2) ≤ lambda * inner ℝ (W w) w :=
        mul_le_mul_of_nonneg_left (hW w) hlambda
      _ = inner ℝ (Q (W w)) q := by
        rw [hQ (W w) q, hQq, real_inner_smul_right]
      _ ≤ ‖Q (W w)‖ * ‖q‖ := real_inner_le_norm _ _
      _ ≤ ‖Q (W w)‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_left hq_le_w (norm_nonneg _)
  by_cases hw_zero : ‖w‖ = 0
  · have hv_zero : ‖v‖ = 0 := by
      rw [hw_zero] at hv_le_w
      exact le_antisymm hv_le_w (norm_nonneg v)
    rw [hv_zero, mul_zero]
    exact norm_nonneg _
  · have hw_pos : 0 < ‖w‖ :=
      lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw_zero)
    have hcancel : m * lambda * ‖w‖ ≤ ‖Q (W w)‖ := by
      apply le_of_mul_le_mul_right _ hw_pos
      calc
        (m * lambda * ‖w‖) * ‖w‖ = lambda * (m * ‖w‖ ^ 2) := by ring
        _ ≤ ‖Q (W w)‖ * ‖w‖ := hcross
    exact (mul_le_mul_of_nonneg_left hv_le_w (mul_nonneg hm hlambda)).trans hcancel

/-- Squared fluctuation floor from the same two modes and lower weight.
This form directly matches the squared norms in variance estimates. -/
theorem symmetric_twoMode_weighted_sq_lower
    (Q : E →ₗ[ℝ] E) (hQ : Q.IsSymmetric) (W : E → E)
    (u v : E) (hvu : inner ℝ v u = 0)
    (m lambda : ℝ) (hm : 0 ≤ m)
    (hlambda : 0 ≤ lambda) (hlambda_one : lambda ≤ 1)
    (hQu : Q u = u) (hQv : Q v = lambda • v)
    (hW : ∀ x : E, m * ‖x‖ ^ 2 ≤ inner ℝ (W x) x)
    (c : ℝ) :
    m ^ 2 * lambda ^ 2 * ‖v‖ ^ 2 ≤ ‖Q (W (v - c • u))‖ ^ 2 := by
  have h := symmetric_twoMode_weighted_norm_lower Q hQ W u v hvu
    m lambda hm hlambda hlambda_one hQu hQv hW c
  have hs := pow_le_pow_left₀
    (mul_nonneg (mul_nonneg hm hlambda) (norm_nonneg v)) h 2
  simpa only [mul_pow] using hs

end RealInnerProduct

end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.orthogonal_twoMode_norm_sq
#print axioms MGAP4D.MathlibAnalytic.symmetric_twoMode_weighted_norm_lower
#print axioms MGAP4D.MathlibAnalytic.symmetric_twoMode_weighted_sq_lower
