import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstModeTransferBoundV5_PZ37AOD
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOE — original top-state slope with a linear action budget

AOC bounds the genuine fixed-Haar response remainder by 8*C_H*beta^2.
AOD bounds the weighted true-vacuum replacement error by 16*C_H*beta^2.
The original norm variation and beta-zero norm identify a lower bound of
one half whenever C_H*beta <= one half. Removing the two norm weights then
gives a concrete 81*C_H*beta^2 bound for the actual normalized top-state
first-mode overlap. The radius 1/(1024*(1+C_H)) gives overlap <= -beta/8,
and hence strict negativity at every positive beta in that interval.

All vectors, actions, Haar measures and transfer operators are unchanged
original physical Wilson objects. The coefficient and interval still depend
on the finite volume through C_H. No volume-uniform gap, infinite-volume
state, OS identification or continuum Yang--Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- A linear global-budget remainder for the genuine normalized physical
top/first-mode overlap, under the explicit condition C_H*beta <= 1/2. -/
theorem p4Q2PZ37AOE_originalPhysicalTopFirst_quadraticRemainder_linearBudget
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hlinear :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ (1 / 2 : ℝ)) :
    |inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) +
      beta * (1 / 4 : ℝ)| ≤
      81 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta^2 := by
  have hScalar
      (C beta lambda b r : ℝ) (hC : 0 ≤ C) (hbeta : 0 ≤ beta)
      (hlower : (1 / 2 : ℝ) ≤ lambda)
      (hvariation : |lambda - 1| ≤ C * beta)
      (hresponse : |r + beta * (1 / 4 : ℝ)| ≤ 8 * C * beta^2)
      (hweighted : lambda * |lambda * b - r| ≤ 16 * C * beta^2) :
      |b + beta * (1 / 4 : ℝ)| ≤ 81 * C * beta^2 := by
    have hlambda : 0 ≤ lambda := by linarith only [hlower]
    have hbudget : 0 ≤ C * beta^2 := mul_nonneg hC (sq_nonneg beta)
    have hhalfError :
        (1 / 2 : ℝ) * |lambda * b - r| ≤ lambda * |lambda * b - r| :=
      mul_le_mul_of_nonneg_right hlower (abs_nonneg _)
    have herror : |lambda * b - r| ≤ 32 * C * beta^2 := by
      linarith only [hhalfError, hweighted]
    have hbetaQuarter : 0 ≤ beta * (1 / 4 : ℝ) := by positivity
    have hnormError : |(lambda - 1) * (beta * (1 / 4 : ℝ))| ≤
        (1 / 4 : ℝ) * C * beta^2 := by
      rw [abs_mul, abs_of_nonneg hbetaQuarter]
      calc
        _ ≤ (C * beta) * (beta * (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_right hvariation hbetaQuarter
        _ = (1 / 4 : ℝ) * C * beta^2 := by ring
    have herrorBounds := abs_le.mp herror
    have hresponseBounds := abs_le.mp hresponse
    have hnormBounds := abs_le.mp hnormError
    have habs : |lambda * (b + beta * (1 / 4 : ℝ))| ≤
        (161 / 4 : ℝ) * C * beta^2 := by
      apply abs_le.mpr
      constructor
      · nlinarith only [herrorBounds.1, hresponseBounds.1, hnormBounds.1]
      · nlinarith only [herrorBounds.2, hresponseBounds.2, hnormBounds.2]
    have hsum : lambda * |b + beta * (1 / 4 : ℝ)| ≤
        (161 / 4 : ℝ) * C * beta^2 := by
      simpa only [abs_mul, abs_of_nonneg hlambda] using habs
    have hhalfSlope :
        (1 / 2 : ℝ) * |b + beta * (1 / 4 : ℝ)| ≤
          lambda * |b + beta * (1 / 4 : ℝ)| :=
      mul_le_mul_of_nonneg_right hlower (abs_nonneg _)
    nlinarith only [hsum, hhalfSlope, hbudget]
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
  let r : ℝ := inner ℝ
    ((T - U) (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
    (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)
  have hC : 0 ≤ C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hsmall : C * beta ≤ (1 / 2 : ℝ) := hlinear
  have hnormZero : ‖U‖ = 1 :=
    p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_norm_eq_one H
  have hvariation : |lambda - 1| ≤ C * beta := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_norm_sub_le_beta
        H 2 (by norm_num) 0 beta (by norm_num) hbeta
    rw [hnormZero] at h
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hbeta] using h
  have hnormLower : 1 - C * beta ≤ lambda :=
    p4Q2PZ37ANQ_originalPhysicalTopNorm_ge_one_sub_budgetBeta H beta hbeta
  have hlower : (1 / 2 : ℝ) ≤ lambda := by
    linarith only [hnormLower, hsmall]
  have hresponse : |r + beta * (1 / 4 : ℝ)| ≤ 8 * C * beta^2 :=
    p4Q2PZ37AOC_originalFixedHaarResponse_localQuadraticError_le H beta hbeta
  have hweighted : lambda * |lambda * b - r| ≤ 16 * C * beta^2 :=
    p4Q2PZ37AOD_originalTopFirstMode_fixedHaarResponse_weightedError_le_linearBudgetQuadratic
      H beta hbeta
  change |b + beta * (1 / 4 : ℝ)| ≤ 81 * C * beta^2
  exact hScalar
    C beta lambda b r hC hbeta hlower hvariation hresponse hweighted

/-- Dividing by positive beta gives a linear-budget quantitative slope
error for the same original physical top state and first Gauss-law mode. -/
theorem p4Q2PZ37AOE_originalPhysicalTopFirst_normalizedSlopeError_linearBudget
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (hlinear :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ (1 / 2 : ℝ)) :
    |(inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta.le)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)) / beta +
      (1 / 4 : ℝ)| ≤
      81 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta := by
  let C : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let b : ℝ := inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta.le)
    (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)
  have hbound : |b + beta * (1 / 4 : ℝ)| ≤ 81 * C * beta^2 :=
    p4Q2PZ37AOE_originalPhysicalTopFirst_quadraticRemainder_linearBudget
      H beta hbeta.le hlinear
  have heq : b / beta + (1 / 4 : ℝ) =
      (b + beta * (1 / 4 : ℝ)) / beta := by
    field_simp [ne_of_gt hbeta]
  change |b / beta + (1 / 4 : ℝ)| ≤ 81 * C * beta
  rw [heq, abs_div, abs_of_pos hbeta]
  apply (div_le_iff₀ hbeta).2
  calc
    |b + beta * (1 / 4 : ℝ)| ≤ 81 * C * beta^2 := hbound
    _ = (81 * C * beta) * beta := by ring

/-- The improved radius is strictly positive at every finite H. -/
theorem p4Q2PZ37AOE_originalPhysicalTopFirst_linearBudgetRadius_pos
    (H : ℕ) :
    0 < 1 / (1024 *
      (1 + periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)) := by
  have hC := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  positivity

/-- On the whole closed nonnegative interval up to the linear-budget
radius, the actual physical overlap is at most -beta/8. -/
theorem p4Q2PZ37AOE_originalPhysicalTopFirst_le_neg_eighth_on_linearBudgetInterval
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hradius : beta ≤ 1 / (1024 *
      (1 + periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H))) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ≤ -beta / 8 := by
  let C : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let b : ℝ := inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta)
    (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)
  have hC : 0 ≤ C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hden : 0 < 1024 * (1 + C) := by positivity
  have hinterval : beta ≤ 1 / (1024 * (1 + C)) := hradius
  have hproduct : beta * (1024 * (1 + C)) ≤ 1 :=
    (le_div_iff₀ hden).mp hinterval
  have hbudget : C * beta ≤ (1 / 1024 : ℝ) := by
    nlinarith only [hproduct, hbeta]
  have hsmall : C * beta ≤ (1 / 2 : ℝ) :=
    hbudget.trans (by norm_num)
  have hbound : |b + beta * (1 / 4 : ℝ)| ≤ 81 * C * beta^2 :=
    p4Q2PZ37AOE_originalPhysicalTopFirst_quadraticRemainder_linearBudget
      H beta hbeta hsmall
  have hcoefficient : 81 * C * beta ≤ (1 / 8 : ℝ) := by
    nlinarith only [hbudget]
  have hscaled := mul_le_mul_of_nonneg_right hcoefficient hbeta
  have herror : 81 * C * beta^2 ≤ beta / 8 := by
    nlinarith only [hscaled]
  have hupper := (abs_le.mp hbound).2
  change b ≤ -beta / 8
  linarith only [hupper, herror]

/-- Every positive coupling in the improved interval has strictly negative
original physical top/first-mode overlap. The radius remains H-dependent. -/
theorem p4Q2PZ37AOE_originalPhysicalTopFirst_neg_on_linearBudgetInterval
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (hradius : beta ≤ 1 / (1024 *
      (1 + periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H))) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta.le)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) < 0 := by
  have hbound :=
    p4Q2PZ37AOE_originalPhysicalTopFirst_le_neg_eighth_on_linearBudgetInterval
      H beta hbeta.le hradius
  have hnegative : -beta / 8 < 0 := by linarith only [hbeta]
  exact hbound.trans_lt hnegative

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOE_originalPhysicalTopFirst_quadraticRemainder_linearBudget
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOE_originalPhysicalTopFirst_normalizedSlopeError_linearBudget
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOE_originalPhysicalTopFirst_linearBudgetRadius_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOE_originalPhysicalTopFirst_le_neg_eighth_on_linearBudgetInterval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOE_originalPhysicalTopFirst_neg_on_linearBudgetInterval
