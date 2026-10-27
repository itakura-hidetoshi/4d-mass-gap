import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
# Finite Gram-row Bessel bound

A bounded row sum of absolute real Gram entries bounds synthesis, and hence
bounds the total squared response of ONE bounded linear functional. This is
an upper (Bessel) bound, not a lower frame assumption. Empty index types,
zero coefficients and a zero functional are included. There is no claim
here that a specific physical family satisfies the Gram-row premise.
-/

namespace MGAP4D.MathlibAnalytic
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

private theorem finiteReal_two_mul_le_abs_mul_squares (a b g : ℝ) :
    2 * a * b * g ≤ |g| * (a ^ 2 + b ^ 2) := by
  by_cases hg : 0 ≤ g
  · rw [abs_of_nonneg hg]
    nlinarith [mul_nonneg hg (sq_nonneg (a - b))]
  · have hg' : g < 0 := lt_of_not_ge hg
    rw [abs_of_neg hg']
    nlinarith [mul_nonneg (neg_nonneg.mpr hg'.le) (sq_nonneg (a + b))]

/-- Schur's finite real quadratic estimate with an absolute Gram row bound.
No positive-definiteness hypothesis or eigenvector choice is necessary. -/
theorem finiteReal_symmetric_quadratic_le_row_bound
    {ι : Type*} [Fintype ι] (g : ι → ι → ℝ)
    (hsym : ∀ i j, g i j = g j i)
    (D : ℝ) (hrow : ∀ i, ∑ j, |g i j| ≤ D) (a : ι → ℝ) :
    (∑ i, ∑ j, a i * a j * g i j) ≤ D * ∑ i, (a i) ^ 2 := by
  classical
  have hterm :
      (∑ i, ∑ j, 2 * (a i * a j * g i j)) ≤
        ∑ i, ∑ j, |g i j| * ((a i) ^ 2 + (a j) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j _hj
    nlinarith [finiteReal_two_mul_le_abs_mul_squares (a i) (a j) (g i j)]
  have hswap :
      (∑ i, ∑ j, |g i j| * (a j) ^ 2) =
        ∑ i, ∑ j, |g i j| * (a i) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hsym j i]
  have hbound :
      (∑ i, ∑ j, |g i j| * (a i) ^ 2) ≤ D * ∑ i, (a i) ^ 2 := by
    calc
      (∑ i, ∑ j, |g i j| * (a i) ^ 2) =
          ∑ i, (∑ j, |g i j|) * (a i) ^ 2 := by
        simp only [Finset.sum_mul]
      _ ≤ ∑ i, D * (a i) ^ 2 :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg (a i)))
      _ = D * ∑ i, (a i) ^ 2 := (Finset.mul_sum _ _ _).symm
  simp only [mul_add, Finset.sum_add_distrib] at hterm
  rw [hswap] at hterm
  have hdouble :
      (∑ i, ∑ j, 2 * (a i * a j * g i j)) =
        2 * (∑ i, ∑ j, a i * a j * g i j) := by
    simp only [Finset.mul_sum]
  rw [hdouble] at hterm
  linarith

/-- A finite family with absolute Gram row sum at most D has a synthesis
squared norm at most D times the coefficient squared Euclidean norm. -/
theorem finiteRealHilbert_synthesis_sq_le_gram_row_bound
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : ι → E)
    (D : ℝ) (hrow : ∀ i, ∑ j, |⟪v i, v j⟫_ℝ| ≤ D)
    (a : ι → ℝ) :
    ‖∑ i, a i • v i‖ ^ 2 ≤ D * ∑ i, (a i) ^ 2 := by
  have hexpand :
      ‖∑ i, a i • v i‖ ^ 2 =
        ∑ i, ∑ j, a i * a j * ⟪v i, v j⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    rw [real_inner_comm (v i) (v j)]
    ring
  rw [hexpand]
  exact finiteReal_symmetric_quadratic_le_row_bound
    (fun i j => ⟪v i, v j⟫_ℝ)
    (fun i j => (real_inner_comm (v i) (v j)).symm) D hrow a

/-- A nonnegative synthesis Bessel bound yields a total response bound for
a SINGLE bounded linear functional, without an orthonormal-basis assumption.
Nonnegativity of D is explicit, including for the empty index type. -/
theorem finiteRealHilbert_functional_sq_sum_le_of_synthesis
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : ι → E) (D : ℝ) (hD : 0 ≤ D)
    (hsynthesis : ∀ a : ι → ℝ,
      ‖∑ i, a i • v i‖ ^ 2 ≤ D * ∑ i, (a i) ^ 2)
    (L : E →L[ℝ] ℝ) :
    (∑ i, (L (v i)) ^ 2) ≤ D * ‖L‖ ^ 2 := by
  classical
  let q : ℝ := ∑ i, (L (v i)) ^ 2
  let w : E := ∑ i, L (v i) • v i
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hw : ‖w‖ ^ 2 ≤ D * q := hsynthesis (fun i => L (v i))
  have hLw : L w = q := by
    simp only [w, q, map_sum, map_smul, smul_eq_mul, pow_two]
  have hop : q ≤ ‖L‖ * ‖w‖ := by
    have h := L.le_opNorm w
    rw [hLw, Real.norm_eq_abs, abs_of_nonneg hq] at h
    exact h
  have hopSq : q ^ 2 ≤ (‖L‖ * ‖w‖) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hop)
      (add_nonneg (mul_nonneg (norm_nonneg L) (norm_nonneg w)) hq)]
  have hscaled := mul_le_mul_of_nonneg_left hw (sq_nonneg ‖L‖)
  change q ≤ D * ‖L‖ ^ 2
  by_cases hzero : q = 0
  · rw [hzero]
    exact mul_nonneg hD (sq_nonneg ‖L‖)
  · have hpositive : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
    nlinarith

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.finiteReal_symmetric_quadratic_le_row_bound
#print axioms MGAP4D.MathlibAnalytic.finiteRealHilbert_synthesis_sq_le_gram_row_bound
#print axioms MGAP4D.MathlibAnalytic.finiteRealHilbert_functional_sq_sum_le_of_synthesis
