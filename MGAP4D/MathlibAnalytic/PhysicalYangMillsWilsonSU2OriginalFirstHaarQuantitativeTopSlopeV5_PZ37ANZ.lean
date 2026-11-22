import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstHaarNegativeBetaIntervalV5_PZ37ANY
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANZ — quantified original physical first-mode slope at beta zero

The original ANU Wilson top-state response is paired with ANV's genuinely
computed first action Haar moment m_H=1/4, not a surrogate or assumed
Fourier mode. The original physical Gauss-law Hilbert, one-slab Wilson
action, spatial halfweights and temporal crossing are unchanged.

At fixed finite H, with original action budget C_H, we show an explicit
O_H(beta^2) remainder for the true top/first-mode inner product. Dividing
by positive beta gives a quantitative O_H(beta) slope error about -1/4.

The coefficient is NOT uniform in H. No completed OS operator
identification, infinite volume bound or 4D continuum mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Original Wilson physical top/first-mode first-order error is bounded
by a concrete second-order quantity at each fixed finite H. -/
theorem p4Q2PZ37ANZ_originalPhysicalTopFirst_quadraticRemainder
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hlinear :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ (1 / 64 : ℝ)) :
    |inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) +
      beta * (1 / 4 : ℝ)| ≤
      (16 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H^2 +
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
      beta^2 := by
  let C : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let lambda : ℝ := ‖T‖
  let b : ℝ := inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta)
    (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)
  let x : ℝ := C * beta
  have hC : 0 ≤ C := by
    dsimp [C, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget]
    positivity
  have hx0 : 0 ≤ x := mul_nonneg hC hbeta
  have hxsmall : x ≤ (1 / 64 : ℝ) := hlinear
  have hsmall : C * beta ≤ 1 := by linarith [hxsmall]
  have hNorm0 : ‖U‖ = 1 :=
    p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_norm_eq_one H
  have hNormVariation : |lambda - 1| ≤ x := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_norm_sub_le_beta
        H 2 (by norm_num) 0 beta (by norm_num) hbeta
    rw [hNorm0] at h
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hbeta] using h
  have hlower : (1 / 2 : ℝ) ≤ lambda := by
    have hleft := (abs_le.mp hNormVariation).1
    linarith [hxsmall]
  have hupper : lambda ≤ 2 := by
    have hright := (abs_le.mp hNormVariation).2
    linarith [hxsmall]
  have hlambdaSq : (1 / 4 : ℝ) ≤ lambda^2 := by
    nlinarith [sq_nonneg (lambda - (1 / 2 : ℝ))]
  have hweighted :
      lambda^2 * |b + beta * (1 / 4 : ℝ)| ≤
        (2 + lambda) * x^2 + lambda * beta * (1 / 4 : ℝ) * x :=
    p4Q2PZ37ANW_originalPhysicalTopFirstSlope_quarterWeightedError_le
      H beta hbeta hsmall
  have hfirst : (2 + lambda) * x^2 ≤ 4 * x^2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg x)
  have hfactor : 0 ≤ beta * (1 / 4 : ℝ) * x := by positivity
  have hsecond :
      lambda * beta * (1 / 4 : ℝ) * x ≤ beta / 2 * x := by
    calc
      lambda * beta * (1 / 4 : ℝ) * x =
          lambda * (beta * (1 / 4 : ℝ) * x) := by ring
      _ ≤ 2 * (beta * (1 / 4 : ℝ) * x) :=
        mul_le_mul_of_nonneg_right hupper hfactor
      _ = beta / 2 * x := by ring
  have hLowWeight :
      (1 / 4 : ℝ) * |b + beta * (1 / 4 : ℝ)| ≤
        lambda^2 * |b + beta * (1 / 4 : ℝ)| :=
    mul_le_mul_of_nonneg_right hlambdaSq (abs_nonneg _)
  have hcore :
      (1 / 4 : ℝ) * |b + beta * (1 / 4 : ℝ)| ≤
        4 * x^2 + beta / 2 * x :=
    hLowWeight.trans (hweighted.trans (add_le_add hfirst hsecond))
  have hquad :
      |b + beta * (1 / 4 : ℝ)| ≤ 16 * x^2 + 2 * beta * x := by
    linarith [hcore]
  change |b + beta * (1 / 4 : ℝ)| ≤ (16 * C^2 + 2 * C) * beta^2
  calc
    |b + beta * (1 / 4 : ℝ)| ≤ 16 * x^2 + 2 * beta * x := hquad
    _ = (16 * C^2 + 2 * C) * beta^2 := by dsimp [x]; ring

/-- Quantitative right-hand beta-zero slope error for the actual
normalized physical Wilson top eigenvector and first Gauss-law mode. -/
theorem p4Q2PZ37ANZ_originalPhysicalTopFirst_normalizedSlopeError_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (hlinear :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ (1 / 64 : ℝ)) :
    |(inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta.le)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)) / beta +
      (1 / 4 : ℝ)| ≤
      (16 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H^2 +
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
      beta := by
  let C : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let b : ℝ := inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta.le)
    (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)
  have hbound :
      |b + beta * (1 / 4 : ℝ)| ≤ (16 * C^2 + 2 * C) * beta^2 :=
    p4Q2PZ37ANZ_originalPhysicalTopFirst_quadraticRemainder
      H beta hbeta.le hlinear
  have heq :
      b / beta + (1 / 4 : ℝ) =
        (b + beta * (1 / 4 : ℝ)) / beta := by
    field_simp [ne_of_gt hbeta]
  change |b / beta + (1 / 4 : ℝ)| ≤ (16 * C^2 + 2 * C) * beta
  rw [heq, abs_div, abs_of_pos hbeta]
  apply (div_le_iff₀ hbeta).2
  calc
    |b + beta * (1 / 4 : ℝ)| ≤ (16 * C^2 + 2 * C) * beta^2 :=
      hbound
    _ = ((16 * C^2 + 2 * C) * beta) * beta := by ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANZ_originalPhysicalTopFirst_quadraticRemainder
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANZ_originalPhysicalTopFirst_normalizedSlopeError_le
