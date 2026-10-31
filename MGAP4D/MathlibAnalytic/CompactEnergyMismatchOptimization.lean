import MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Optimal full mismatch budget and actual energy regression defect

Optimize the proved full-tail residual-variance bound over its positive
energy slope.  The zero-variance endpoint is handled without division by
sqrt(variance), and the zero-coupling endpoint is included.  With genuine
energy variance 1/4, the regression defect is an actual residual variance,
not an assumed small parameter.  No smallness or positive-margin conclusion
is inferred from its nonnegativity.
-/

namespace MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment

open MeasureTheory
noncomputable section
set_option autoImplicit false

/-- The existing positive-slope residual budget in scalar coordinates. -/
def quadraticBudget (b s v C a : ℝ) : ℝ :=
  (b / a) * (v + 2 * s * a * C + a ^ 2 / 4)

/-- The exact infimum of the positive-slope budgets when b,v are nonnegative. -/
def optimalBudget (b s v C : ℝ) : ℝ := b * (Real.sqrt v + 2 * s * C)

/-- Exact distance above the optimum; no covariance inequality is needed. -/
theorem quadraticBudget_sub_optimal (b s v C a : ℝ)
    (hv : 0 ≤ v) (ha : 0 < a) :
    quadraticBudget b s v C a - optimalBudget b s v C =
      (b / (4 * a)) * (a - 2 * Real.sqrt v) ^ 2 := by
  let r : ℝ := Real.sqrt v
  have hr : r ^ 2 = v := Real.sq_sqrt hv
  change (b / a) * (v + 2 * s * a * C + a ^ 2 / 4) - b * (r + 2 * s * C) =
    (b / (4 * a)) * (a - 2 * r) ^ 2
  rw [← hr]
  field_simp [ha.ne']
  ring

theorem optimalBudget_le_quadraticBudget (b s v C a : ℝ)
    (hb : 0 ≤ b) (hv : 0 ≤ v) (ha : 0 < a) :
    optimalBudget b s v C ≤ quadraticBudget b s v C a := by
  have h := quadraticBudget_sub_optimal b s v C a hv ha
  have hn : 0 ≤ (b / (4 * a)) * (a - 2 * Real.sqrt v) ^ 2 := by positivity
  linarith

/-- Positive variance attains the optimum at the actual positive slope. -/
theorem quadraticBudget_at_sqrt (b s v C : ℝ) (hv : 0 < v) :
    quadraticBudget b s v C (2 * Real.sqrt v) = optimalBudget b s v C := by
  have ha : 0 < 2 * Real.sqrt v := mul_pos (by norm_num) (Real.sqrt_pos.mpr hv)
  have h := quadraticBudget_sub_optimal b s v C (2 * Real.sqrt v) hv.le ha
  have hz : quadraticBudget b s v C (2 * Real.sqrt v) - optimalBudget b s v C = 0 := by
    simpa only [sub_self, pow_two, zero_mul, mul_zero] using h
  exact sub_eq_zero.mp hz

private theorem quadraticBudget_zero_variance (b s C a : ℝ) (ha : 0 < a) :
    quadraticBudget b s 0 C a = optimalBudget b s 0 C + b * a / 4 := by
  unfold quadraticBudget optimalBudget
  rw [Real.sqrt_zero]
  field_simp [ha.ne']
  ring

/-- An arbitrary strict threshold admits a positive-slope certificate
exactly when it exceeds the optimized budget.  At v=0 the infimum need
not be attained, so that endpoint uses an explicit positive small slope. -/
theorem exists_quadraticBudget_lt_iff (b s v C t : ℝ)
    (hb : 0 ≤ b) (hv : 0 ≤ v) :
    (∃ a : ℝ, 0 < a ∧ quadraticBudget b s v C a < t) ↔
      optimalBudget b s v C < t := by
  constructor
  · rintro ⟨a, ha, ht⟩
    exact (optimalBudget_le_quadraticBudget b s v C a hb hv ha).trans_lt ht
  · intro ht
    by_cases hv0 : v = 0
    · subst v
      let δ : ℝ := t - optimalBudget b s 0 C
      have hδ : 0 < δ := sub_pos.mpr ht
      have hb1 : 0 < b + 1 := by linarith
      let a : ℝ := 4 * δ / (b + 1)
      have ha : 0 < a := div_pos (mul_pos (by norm_num) hδ) hb1
      have haeq : a * (b + 1) = 4 * δ := by
        exact div_mul_cancel₀ (4 * δ) hb1.ne'
      have hsmall : b * a / 4 < δ := by nlinarith [haeq]
      refine ⟨a, ha, ?_⟩
      rw [quadraticBudget_zero_variance b s C a ha]
      dsimp [δ] at hsmall
      linarith
    · have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
      refine ⟨2 * Real.sqrt v, mul_pos (by norm_num) (Real.sqrt_pos.mpr hvp), ?_⟩
      rw [quadraticBudget_at_sqrt b s v C hvp]
      exact ht

/-- Optimize any quantity bounded by all positive-slope budgets.  This
includes b=0 and v=0, and assumes no smallness of the quantity. -/
theorem scalar_optimized_bound (b s v C m : ℝ)
    (hb : 0 ≤ b) (hv : 0 ≤ v)
    (hbound : ∀ a : ℝ, 0 < a → m ≤ quadraticBudget b s v C a) :
    m ≤ optimalBudget b s v C := by
  by_contra h
  have hstrict : optimalBudget b s v C < m := lt_of_not_ge h
  obtain ⟨a, ha, hlt⟩ := (exists_quadraticBudget_lt_iff b s v C m hb hv).mpr hstrict
  exact (not_lt_of_ge (hbound a ha)) hlt

section Probability

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [CompactSpace α] [SecondCountableTopology α] [BorelSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

/-- The actual least-squares energy residual, retaining any constant part. -/
def regressionResidual (F E : α → ℝ) : α → ℝ :=
  residual 1 (-4 * covariance μ F E) F E

/-- Exact defect after projection onto the centered energy direction. -/
def regressionDefect (F E : α → ℝ) : ℝ :=
  variance μ F - 4 * covariance μ F E ^ 2

/-- Complete the variance square using the genuine energy variance. -/
theorem variance_residual_eq_defect_add_square (s a : ℝ) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) (hEV : variance μ E = (1 / 4 : ℝ)) :
    variance μ (residual s a F E) = regressionDefect μ F E +
      (s * a + 4 * covariance μ F E) ^ 2 / 4 := by
  rw [variance_residual μ s a F E hF hE, hEV]
  unfold regressionDefect
  ring

/-- The defect is the variance of an actual continuous residual. -/
theorem regressionDefect_eq_residualVariance (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) (hEV : variance μ E = (1 / 4 : ℝ)) :
    regressionDefect μ F E = variance μ (regressionResidual μ F E) := by
  have h := variance_residual_eq_defect_add_square μ 1 (-4 * covariance μ F E)
    F E hF hE hEV
  simpa [regressionResidual] using h.symm

theorem regressionDefect_nonneg (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) (hEV : variance μ E = (1 / 4 : ℝ)) :
    0 ≤ regressionDefect μ F E := by
  rw [regressionDefect_eq_residualVariance μ F E hF hE hEV]
  have hR : Continuous (regressionResidual μ F E) :=
    hF.add (continuous_const.mul hE)
  exact variance_nonneg μ (regressionResidual μ F E) hR

/-- This is a global minimum among all real affine energy slopes. -/
theorem regressionDefect_le_residualVariance (s a : ℝ) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) (hEV : variance μ E = (1 / 4 : ℝ)) :
    regressionDefect μ F E ≤ variance μ (residual s a F E) := by
  rw [variance_residual_eq_defect_add_square μ s a F E hF hE hEV]
  have hq : 0 ≤ (s * a + 4 * covariance μ F E) ^ 2 / 4 := by positivity
  linarith

/-- Genuine covariance Cauchy bound derived from the residual variance. -/
theorem four_covariance_sq_le_variance (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) (hEV : variance μ E = (1 / 4 : ℝ)) :
    4 * covariance μ F E ^ 2 ≤ variance μ F := by
  have h := regressionDefect_nonneg μ F E hF hE hEV
  unfold regressionDefect at h
  linarith

theorem two_abs_covariance_le_sqrt_variance (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) (hEV : variance μ E = (1 / 4 : ℝ)) :
    2 * |covariance μ F E| ≤ Real.sqrt (variance μ F) := by
  have hsq : (2 * covariance μ F E) ^ 2 ≤ variance μ F := by
    nlinarith [four_covariance_sq_le_variance μ F E hF hE hEV]
  have h := Real.abs_le_sqrt hsq
  simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] using h

theorem optimizedCoefficient_nonneg (s : ℝ) (hs : s ^ 2 = 1) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) (hEV : variance μ E = (1 / 4 : ℝ)) :
    0 ≤ Real.sqrt (variance μ F) + 2 * s * covariance μ F E := by
  have hsq : (-2 * s * covariance μ F E) ^ 2 ≤ variance μ F := by
    calc
      _ = 4 * covariance μ F E ^ 2 := by norm_num [mul_pow, hs]
      _ ≤ _ := four_covariance_sq_le_variance μ F E hF hE hEV
  have h := Real.le_sqrt_of_sq_le hsq
  linarith

/-- The full original mismatch with no free slope parameter. -/
theorem mismatch_le_optimized (b s : ℝ) (hb : 0 ≤ b) (hs : s ^ 2 = 1)
    (F E : α → ℝ) (hF : Continuous F) (hE : Continuous E)
    (hEV : variance μ E = (1 / 4 : ℝ)) :
    mismatch μ b s F E ≤
      b * (Real.sqrt (variance μ F) + 2 * s * covariance μ F E) := by
  apply scalar_optimized_bound b s (variance μ F) (covariance μ F E)
    (mismatch μ b s F E) hb (variance_nonneg μ F hF)
  intro a ha
  have h := mismatch_le_residual_variance μ b s a hb ha F E hF hE
  rw [variance_residual μ s a F E hF hE, hEV] at h
  have hsa : (s * a) ^ 2 = a ^ 2 := by rw [mul_pow, hs, one_mul]
  have hquarter : a ^ 2 * (1 / 4 : ℝ) = a ^ 2 / 4 := by ring
  rw [hsa, hquarter] at h
  exact h

/-- The zero-variance endpoint is zero, not an undefined optimized slope. -/
theorem mismatch_eq_zero_of_variance_zero (b s : ℝ) (hb : 0 ≤ b) (hs : s ^ 2 = 1)
    (F E : α → ℝ) (hF : Continuous F) (hE : Continuous E)
    (hEV : variance μ E = (1 / 4 : ℝ)) (hV : variance μ F = 0) :
    mismatch μ b s F E = 0 := by
  have hC : covariance μ F E = 0 := by
    have h := four_covariance_sq_le_variance μ F E hF hE hEV
    rw [hV] at h
    nlinarith [sq_nonneg (covariance μ F E)]
  have hu := mismatch_le_optimized μ b s hb hs F E hF hE hEV
  have hu0 : mismatch μ b s F E ≤ 0 := by
    simpa only [hV, hC, Real.sqrt_zero, mul_zero, add_zero] using hu
  have hn : (0 : ℝ) ≤ mismatch μ b s F E := by
    unfold mismatch
    exact integral_nonneg (fun _ => le_max_right _ _)
  exact le_antisymm hu0 hn

end Probability
end
end MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment

#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.quadraticBudget_sub_optimal
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimalBudget_le_quadraticBudget
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.quadraticBudget_at_sqrt
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.exists_quadraticBudget_lt_iff
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.scalar_optimized_bound
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.variance_residual_eq_defect_add_square
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.regressionDefect_eq_residualVariance
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.regressionDefect_nonneg
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.regressionDefect_le_residualVariance
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.four_covariance_sq_le_variance
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.two_abs_covariance_le_sqrt_variance
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimizedCoefficient_nonneg
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.mismatch_le_optimized
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.mismatch_eq_zero_of_variance_zero
