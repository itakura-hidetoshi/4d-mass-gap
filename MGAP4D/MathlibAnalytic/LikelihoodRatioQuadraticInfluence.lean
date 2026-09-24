import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalResidualWeightedInfluence
import Mathlib.Tactic

/-!
# Quadratic likelihood-ratio influence

The bounded-test and overlap-coupling routes control first-order variation.
For the current L2 profile construction we need the corresponding quadratic
density defect.

If nonnegative densities p and q mutually dominate one another by K >= 1,
the existing sharp coefficient

  c(K) = (K - 1) / (K + 1)

satisfies |p-q| <= c(K) (p+q).  Squaring and dividing by the positive total
local density gives

  (p-q)^2 / (p+q) <= c(K)^2 (p+q).

The zero-total-density case is kept explicit.  This is the pointwise
chi-square-type estimate needed for a later weighted Cauchy--Schwarz step.  In
particular, taking square roots after integration preserves a coefficient
linear in c(K), unlike the mismatch-mass overlap estimate which produces a
square-root loss.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

namespace HaarLikelihoodRatioInfluence

/-- Sharp quadratic density-defect estimate induced by mutual likelihood-ratio
control.  No strict positivity of either density is required. -/
theorem quadratic_defect_le_coefficient_sq_mul_add
    (K p q : ℝ)
    (hK : 1 ≤ K)
    (hp : 0 ≤ p)
    (hq : 0 ≤ q)
    (hpq : p ≤ K * q)
    (hqp : q ≤ K * p) :
    (p - q) ^ 2 / (p + q) ≤
      coefficient K ^ 2 * (p + q) := by
  have hCoeff : 0 ≤ coefficient K := by
    unfold coefficient
    exact div_nonneg (sub_nonneg.mpr hK) (by linarith)
  have hSum : 0 ≤ p + q := add_nonneg hp hq
  by_cases hZero : p + q = 0
  · have hp0 : p = 0 := by nlinarith
    have hq0 : q = 0 := by nlinarith
    simp [hp0, hq0]
  · have hSumPos : 0 < p + q :=
      lt_of_le_of_ne hSum (Ne.symm hZero)
    have hAbs :
        |p - q| ≤ coefficient K * (p + q) :=
      abs_sub_le_coefficient_mul_add K p q hK hpq hqp
    have hRightNonneg :
        0 ≤ coefficient K * (p + q) :=
      mul_nonneg hCoeff hSum
    have hSq :
        (p - q) ^ 2 ≤ (coefficient K * (p + q)) ^ 2 := by
      have hMul :=
        mul_self_le_mul_self (abs_nonneg (p - q)) hAbs
      simpa [pow_two, sq_abs] using hMul
    apply (div_le_iff₀ hSumPos).2
    calc
      (p - q) ^ 2 ≤
          (coefficient K * (p + q)) ^ 2 := hSq
      _ = coefficient K ^ 2 * (p + q) * (p + q) := by
        ring

/-- Equivalent full-L1 normalization.  Since the bounded-test/full-L1
coefficient is 2*c(K), twice the quadratic defect is bounded by its square
times the total density.  This deliberately leaves slack by a factor two; that
slack is useful when the later Cauchy--Schwarz mass factor is at most
2*c(K). -/
theorem two_mul_quadratic_defect_le_fullL1_coefficient_sq_mul_add
    (K p q : ℝ)
    (hK : 1 ≤ K)
    (hp : 0 ≤ p)
    (hq : 0 ≤ q)
    (hpq : p ≤ K * q)
    (hqp : q ≤ K * p) :
    2 * ((p - q) ^ 2 / (p + q)) ≤
      (2 * coefficient K) ^ 2 * (p + q) := by
  have hBase :=
    quadratic_defect_le_coefficient_sq_mul_add
      K p q hK hp hq hpq hqp
  have hCoeffSq : 0 ≤ coefficient K ^ 2 := sq_nonneg _
  have hSum : 0 ≤ p + q := add_nonneg hp hq
  calc
    2 * ((p - q) ^ 2 / (p + q)) ≤
        2 * (coefficient K ^ 2 * (p + q)) :=
      mul_le_mul_of_nonneg_left hBase (by norm_num)
    _ ≤ (2 * coefficient K) ^ 2 * (p + q) := by
      nlinarith [mul_nonneg hCoeffSq hSum]

/-- Exponential-radius specialization.  The canonical full-L1 transform is
exactly twice the sharp likelihood-ratio coefficient, so the preceding
quadratic estimate is immediately expressed in the repository's cross-ratio
influence language. -/
theorem two_mul_quadratic_defect_le_crossRatioInfluenceTransform_sq_mul_add
    (radius p q : ℝ)
    (hRadius : 0 ≤ radius)
    (hp : 0 ≤ p)
    (hq : 0 ≤ q)
    (hpq : p ≤ Real.exp radius * q)
    (hqp : q ≤ Real.exp radius * p) :
    2 * ((p - q) ^ 2 / (p + q)) ≤
      finitePositiveWeightCrossRatioInfluenceTransform radius ^ 2 *
        (p + q) := by
  have hK : 1 ≤ Real.exp radius :=
    Real.one_le_exp hRadius
  simpa [
    finitePositiveWeightCrossRatioInfluenceTransform,
    coefficient] using
    two_mul_quadratic_defect_le_fullL1_coefficient_sq_mul_add
      (Real.exp radius) p q hK hp hq hpq hqp

end HaarLikelihoodRatioInfluence

end

end MGAP4D.MathlibAnalytic
