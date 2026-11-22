import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstHaarSlopeSignV5_PZ37ANW
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANX — constructive finite-volume positive coupling and signed top overlap

ANV computes the ORIGINAL SU(2) one-slab first Haar action moment 1/4.
ANW proves the actual physical top/first Gauss-law overlap is negative
under the original ANU weighted-error dominance condition.

This additive leaf constructs an explicit positive coupling, depending
on the original finite-volume Wilson action budget C_H, for which that
dominance condition really holds. The original Wilson spatial
halfweights, time-crossing terms, Haar probability, physical Hilbert,
top eigenstate and first Gram–Schmidt Gauss-law mode are unchanged.

The coupling window is volume-dependent; no volume-uniform window,
completed OS operator identification, continuum limit, or 4D mass gap
is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Elementary *real-scalar* sufficient condition for the exact original
Wilson ANW error to be strictly below the 1/4 first-order signal. -/
private theorem p4Q2PZ37ANX_scalar_quarter_dominance
    (lambda beta x : ℝ)
    (hbeta : 0 < beta)
    (hlow : (1 / 2 : ℝ) ≤ lambda)
    (hhigh : lambda ≤ 2)
    (hx0 : 0 ≤ x)
    (hxsmall : x ≤ (1 / 64 : ℝ))
    (hxsq : x^2 ≤ beta / 256) :
    (2 + lambda) * x^2 + lambda * beta * (1 / 4 : ℝ) * x <
      lambda^2 * beta * (1 / 4 : ℝ) := by
  have h1 : (2 + lambda) * x^2 ≤ beta / 64 := by
    calc
      (2 + lambda) * x^2 ≤ 4 * x^2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg x)
      _ ≤ 4 * (beta / 256) :=
        mul_le_mul_of_nonneg_left hxsq (by norm_num)
      _ = beta / 64 := by ring
  have hlx : lambda * x ≤ (1 / 32 : ℝ) := by
    calc
      lambda * x ≤ 2 * x :=
        mul_le_mul_of_nonneg_right hhigh hx0
      _ ≤ 2 * (1 / 64 : ℝ) :=
        mul_le_mul_of_nonneg_left hxsmall (by norm_num)
      _ = 1 / 32 := by norm_num
  have h2 : lambda * beta * (1 / 4 : ℝ) * x ≤ beta / 128 := by
    calc
      lambda * beta * (1 / 4 : ℝ) * x =
          (beta * (1 / 4 : ℝ)) * (lambda * x) := by ring
      _ ≤ (beta * (1 / 4 : ℝ)) * (1 / 32 : ℝ) :=
        mul_le_mul_of_nonneg_left hlx (by positivity)
      _ = beta / 128 := by ring
  have hlsq : (1 / 4 : ℝ) ≤ lambda^2 := by
    nlinarith [sq_nonneg (lambda - (1 / 2 : ℝ))]
  have hrhs : beta / 16 ≤ lambda^2 * beta * (1 / 4 : ℝ) := by
    calc
      beta / 16 = (beta * (1 / 4 : ℝ)) * (1 / 4 : ℝ) := by ring
      _ ≤ (beta * (1 / 4 : ℝ)) * lambda^2 :=
        mul_le_mul_of_nonneg_left hlsq (by positivity)
      _ = lambda^2 * beta * (1 / 4 : ℝ) := by ring
  have hgap : beta / 64 + beta / 128 < beta / 16 := by
    nlinarith
  calc
    (2 + lambda) * x^2 + lambda * beta * (1 / 4 : ℝ) * x ≤
        beta / 64 + beta / 128 := add_le_add h1 h2
    _ < beta / 16 := hgap
    _ ≤ lambda^2 * beta * (1 / 4 : ℝ) := hrhs

/-- The genuine physical top/first-mode inner product has strict negative
sign for every positive beta satisfying two explicit original-model bounds.
No unproved auxiliary top state or surrogate operator is introduced. -/
theorem p4Q2PZ37ANX_originalPhysicalTopFirstOverlap_neg_of_explicit_bounds
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (hlinear :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ (1 / 64 : ℝ))
    (hquadratic :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^2 *
        beta ≤ (1 / 256 : ℝ)) :
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) beta hbeta.le)
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) < 0 := by
  let C : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta.le
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let lambda : ℝ := ‖T‖
  let x : ℝ := C * beta
  have hC : 0 ≤ C := by
    dsimp [C, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget]
    positivity
  have hx0 : 0 ≤ x := mul_nonneg hC hbeta.le
  have hxsmall : x ≤ (1 / 64 : ℝ) := hlinear
  have hsmall : C * beta ≤ 1 := by
    linarith [hxsmall]
  have hNorm0 : ‖U‖ = 1 :=
    p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_norm_eq_one H
  have hNormVariation : |lambda - 1| ≤ x := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_norm_sub_le_beta
        H 2 (by norm_num) 0 beta (by norm_num) hbeta.le
    rw [hNorm0] at h
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hbeta.le] using h
  have hlow : (1 / 2 : ℝ) ≤ lambda := by
    have hleft := (abs_le.mp hNormVariation).1
    linarith [hxsmall]
  have hhigh : lambda ≤ 2 := by
    have hright := (abs_le.mp hNormVariation).2
    linarith [hxsmall]
  have hxsq : x^2 ≤ beta / 256 := by
    have hscaled :
        beta * (C^2 * beta) ≤ beta * (1 / 256 : ℝ) :=
      mul_le_mul_of_nonneg_left hquadratic hbeta.le
    calc
      x^2 = beta * (C^2 * beta) := by dsimp [x]; ring
      _ ≤ beta * (1 / 256 : ℝ) := hscaled
      _ = beta / 256 := by ring
  have hdominance :
      (2 + lambda) * x^2 + lambda * beta * (1 / 4 : ℝ) * x <
        lambda^2 * beta * (1 / 4 : ℝ) :=
    p4Q2PZ37ANX_scalar_quarter_dominance
      lambda beta x hbeta hlow hhigh hx0 hxsmall hxsq
  exact p4Q2PZ37ANW_originalPhysicalTopFirstOverlap_neg_of_quarterDominance
    H beta hbeta.le hsmall hdominance

/-- A concrete, ORIGINAL-model, strictly positive small coupling exists
for each fixed finite H. This window scales with the actual action budget
C_H and is not asserted to be uniform as H tends to infinity. -/
theorem p4Q2PZ37ANX_originalPhysicalTopFirstOverlap_exists_negative
    (H : ℕ) :
    ∃ (beta : ℝ) (hbeta : 0 ≤ beta), 0 < beta ∧
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) < 0 := by
  let C : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hC : 0 ≤ C := by
    dsimp [C, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget]
    positivity
  let d : ℝ := 1 + C
  have hd : 0 < d := by dsimp [d]; linarith
  have hdenom : 0 < 1024 * d^2 := by positivity
  let beta : ℝ := 1 / (1024 * d^2)
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hCd : C ≤ d^2 := by
    dsimp [d]
    nlinarith [sq_nonneg C]
  have hC2d : C^2 ≤ d^2 := by
    dsimp [d]
    nlinarith
  have hlinear : C * beta ≤ (1 / 64 : ℝ) := by
    have hdiv : C / (1024 * d^2) ≤ (1 / 64 : ℝ) :=
      (div_le_iff₀ hdenom).2 (by nlinarith [hCd, sq_nonneg d])
    simpa only [beta, div_eq_mul_inv, one_mul] using hdiv
  have hquadratic : C^2 * beta ≤ (1 / 256 : ℝ) := by
    have hdiv : C^2 / (1024 * d^2) ≤ (1 / 256 : ℝ) :=
      (div_le_iff₀ hdenom).2 (by nlinarith [hC2d, sq_nonneg d])
    simpa only [beta, div_eq_mul_inv, one_mul] using hdiv
  exact ⟨beta, hbeta.le, hbeta,
    p4Q2PZ37ANX_originalPhysicalTopFirstOverlap_neg_of_explicit_bounds
      H beta hbeta hlinear hquadratic⟩

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANX_originalPhysicalTopFirstOverlap_neg_of_explicit_bounds
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANX_originalPhysicalTopFirstOverlap_exists_negative
