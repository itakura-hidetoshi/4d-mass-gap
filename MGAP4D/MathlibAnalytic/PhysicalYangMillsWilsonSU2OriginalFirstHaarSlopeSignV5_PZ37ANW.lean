import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstHaarMomentValueV5_PZ37ANV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANW — native physical top/first-mode signed first-order response

The exact ANV first action Haar moment is the original ANU physical
pair-Haar quantity and equals 1/4.  Here we substitute that value in
ANU's genuine finite-volume quadratic weighted-error estimate, then
deduce the negative sign of the actual top/first-mode overlap whenever
the explicitly displayed error budget is strictly dominated by its
first-order signal.

All operators, Gram–Schmidt modes, Gauss-law states, original Wilson
spatial halfweights and temporal crossings remain unchanged.
No claimed volume-uniform window, OS boundary identification or
four-dimensional continuum mass gap follows from this local result.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The formerly unknown original ANU physical action moment is positive
and nonzero at every finite original spatial half-extent. -/
theorem p4Q2PZ37ANW_originalFirstHaarActionMoment_pos (H : ℕ) :
    0 < p4Q2PZ37ANU_originalFirstHaarActionMoment H := by
  rw [p4Q2PZ37ANV_originalFirstHaarActionMoment_eq_oneFourth]
  norm_num

/-- Exact original-model weighted quadratic remainder with the certified
physical SU(2) coefficient 1/4 in place of an unknown Haar moment. -/
theorem p4Q2PZ37ANW_originalPhysicalTopFirstSlope_quarterWeightedError_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ 1) :
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖)^2 *
      |inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H 2 (by norm_num) beta hbeta)
          (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) +
        beta * (1 / 4 : ℝ)| ≤
      (2 +
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta‖) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta)^2 +
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
        beta * (1 / 4 : ℝ) *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
            beta) := by
  simpa only [p4Q2PZ37ANV_originalFirstHaarActionMoment_eq_oneFourth,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ))]
    using p4Q2PZ37ANU_originalPhysicalTopFirstSlope_weightedError_le
      H beta hbeta hsmall

/-- The genuine physical first Gauss-law mode overlaps the positive top
state with a STRICTLY NEGATIVE signed coefficient once the actual
quadratic remainder is below the certified first-order 1/4 signal.
The hypothesis mentions the real original Wilson transfer norm,
not a proxy or an OS gluing assertion. -/
theorem p4Q2PZ37ANW_originalPhysicalTopFirstOverlap_neg_of_quarterDominance
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ 1)
    (hdominance :
      (2 +
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta hbeta‖) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta)^2 +
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
        beta * (1 / 4 : ℝ) *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
            beta) <
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta‖)^2 * beta * (1 / 4 : ℝ)) :
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) beta hbeta)
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) < 0 := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H 2 (by norm_num) beta hbeta
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let lambda : ℝ := ‖T‖
  let b : ℝ := inner ℝ omega v1
  let x : ℝ := C * beta
  have hlambda : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta
  have hbound :
      lambda^2 * |b + beta * (1 / 4 : ℝ)| ≤
        (2 + lambda) * x^2 + lambda * beta * (1 / 4 : ℝ) * x :=
    p4Q2PZ37ANW_originalPhysicalTopFirstSlope_quarterWeightedError_le
      H beta hbeta hsmall
  have hdom :
      (2 + lambda) * x^2 + lambda * beta * (1 / 4 : ℝ) * x <
        lambda^2 * beta * (1 / 4 : ℝ) := hdominance
  have hstrict :
      lambda^2 * |b + beta * (1 / 4 : ℝ)| <
        lambda^2 * (beta * (1 / 4 : ℝ)) := by
    calc
      _ < lambda^2 * beta * (1 / 4 : ℝ) := lt_of_le_of_lt hbound hdom
      _ = lambda^2 * (beta * (1 / 4 : ℝ)) := by ring
  -- CodeAI typed repair: `mul_lt_mul_left` incorrectly requests a
  -- global MulRightStrictMono ℝ instance, which does not hold for ℝ.
  -- Use an explicit nonnegative multiplier and contradiction instead.
  have habs : |b + beta * (1 / 4 : ℝ)| < beta * (1 / 4 : ℝ) := by
    by_contra hnot
    have hle : beta * (1 / 4 : ℝ) ≤ |b + beta * (1 / 4 : ℝ)| :=
      le_of_not_gt hnot
    have hscaled :
        lambda^2 * (beta * (1 / 4 : ℝ)) ≤
          lambda^2 * |b + beta * (1 / 4 : ℝ)| :=
      mul_le_mul_of_nonneg_left hle (sq_nonneg lambda)
    exact (not_le_of_gt hstrict) hscaled
  have hb : b + beta * (1 / 4 : ℝ) < beta * (1 / 4 : ℝ) :=
    (abs_lt.mp habs).2
  have hbneg : b < 0 := by linarith
  exact hbneg

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANW_originalFirstHaarActionMoment_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANW_originalPhysicalTopFirstSlope_quarterWeightedError_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANW_originalPhysicalTopFirstOverlap_neg_of_quarterDominance
