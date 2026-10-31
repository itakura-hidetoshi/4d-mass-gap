import MGAP4D.MathlibAnalytic.CompactEnergyMismatchOptimization
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Sharp covariance after projecting both arguments onto centered energy

On the same compact probability space, project two actual continuous functions
onto the energy direction with variance 1/4. Their residual covariance is
Cov(F,D)-4 Cov(F,E)Cov(D,E). Cauchy--Schwarz controls its square by the PRODUCT
of the two genuine regression defects. Neither defect is assumed small.
-/
namespace MGAP4D.MathlibAnalytic.CompactEnergyRegressionContrast
open MeasureTheory
open CompactEnergyMismatchMoment
open scoped Topology InnerProductSpace
noncomputable section
set_option autoImplicit false

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [CompactSpace α] [SecondCountableTopology α] [BorelSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

private theorem ci {F : α → ℝ} (hF : Continuous F) : Integrable F μ :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Covariance is symmetric without changing the measure. -/
theorem covariance_swap (F D : α → ℝ) : covariance μ F D = covariance μ D F := by
  unfold covariance
  simp only [mul_comm]

/-- Actual covariance is linear under subtraction of an energy component. -/
theorem covariance_sub_mul_left (F E D : α → ℝ) (a : ℝ)
    (hF : Continuous F) (hE : Continuous E) (hD : Continuous D) :
    covariance μ (fun x => F x - a * E x) D =
      covariance μ F D - a * covariance μ E D := by
  have hm : (∫ x, F x - a * E x ∂μ) = (∫ x, F x ∂μ) - a * ∫ x, E x ∂μ := by
    rw [integral_sub (ci μ hF) ((ci μ hE).const_mul a), integral_const_mul]
  have hp : (∫ x, (F x - a * E x) * D x ∂μ) =
      (∫ x, F x * D x ∂μ) - a * ∫ x, E x * D x ∂μ := by
    calc
      _ = ∫ x, F x * D x - a * (E x * D x) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := by
        rw [integral_sub (ci μ (hF.mul hD)) ((ci μ (hE.mul hD)).const_mul a),
          integral_const_mul]
  unfold covariance
  rw [hm, hp]
  ring

/-- The same identity in the second argument. -/
theorem covariance_sub_mul_right (F D E : α → ℝ) (a : ℝ)
    (hF : Continuous F) (hD : Continuous D) (hE : Continuous E) :
    covariance μ F (fun x => D x - a * E x) =
      covariance μ F D - a * covariance μ F E := by
  rw [covariance_swap μ F, covariance_sub_mul_left μ D E F a hD hE hF,
    covariance_swap μ D F, covariance_swap μ E F]

private theorem centered_product (F D : α → ℝ)
    (hF : Continuous F) (hD : Continuous D) :
    (∫ x, (F x - ∫ y, F y ∂μ) * (D x - ∫ y, D y ∂μ) ∂μ) =
      covariance μ F D := by
  let mF : ℝ := ∫ x, F x ∂μ
  let mD : ℝ := ∫ x, D x ∂μ
  have hFD := ci μ (hF.mul hD)
  have hA := (ci μ hD).const_mul mF
  have hB := (ci μ hF).const_mul mD
  have hp (x : α) : (F x - mF) * (D x - mD) =
      (F x * D x - mF * D x) - mD * F x + mF * mD := by ring
  change (∫ x, (F x - mF) * (D x - mD) ∂μ) = covariance μ F D
  simp_rw [hp]
  rw [integral_add ((hFD.sub hA).sub hB) (integrable_const _),
    integral_sub (hFD.sub hA) hB, integral_sub hFD hA,
    integral_const_mul, integral_const_mul]
  simp [covariance, mF, mD]
  ring

/-- Cauchy--Schwarz in the actual centered Haar-L2 realization. -/
theorem covariance_sq_le_variances (F D : α → ℝ)
    (hF : Continuous F) (hD : Continuous D) :
    (covariance μ F D) ^ 2 ≤ variance μ F * variance μ D := by
  let Fc : C(α, ℝ) := ⟨fun x => F x - ∫ y, F y ∂μ, hF.sub continuous_const⟩
  let Dc : C(α, ℝ) := ⟨fun x => D x - ∫ y, D y ∂μ, hD.sub continuous_const⟩
  let Fp : Lp ℝ 2 μ := ContinuousMap.toLp 2 μ ℝ Fc
  let Dp : Lp ℝ 2 μ := ContinuousMap.toLp 2 μ ℝ Dc
  have hFD : inner ℝ Fp Dp = covariance μ F D := by
    calc
      _ = ∫ x, Dc x * Fc x ∂μ := MeasureTheory.ContinuousMap.inner_toLp μ Fc Dc
      _ = covariance μ D F := centered_product μ D F hD hF
      _ = covariance μ F D := covariance_swap μ D F
  have hFF : inner ℝ Fp Fp = variance μ F :=
    (MeasureTheory.ContinuousMap.inner_toLp μ Fc Fc).trans (centered_product μ F F hF hF)
  have hDD : inner ℝ Dp Dp = variance μ D :=
    (MeasureTheory.ContinuousMap.inner_toLp μ Dc Dc).trans (centered_product μ D D hD hD)
  have h := pow_le_pow_left₀ (abs_nonneg (inner ℝ Fp Dp)) (abs_real_inner_le_norm Fp Dp) 2
  rw [sq_abs, mul_pow, ← real_inner_self_eq_norm_sq Fp,
    ← real_inner_self_eq_norm_sq Dp, hFD, hFF, hDD] at h
  exact h

/-- Expose only the small scalar residual wrapper, not physical definitions. -/
theorem regressionResidual_eq_sub (F E : α → ℝ) :
    regressionResidual μ F E = fun x => F x - 4 * covariance μ F E * E x := by
  funext x
  dsimp [regressionResidual, residual]
  ring

private theorem regression_continuous (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) : Continuous (regressionResidual μ F E) := by
  rw [regressionResidual_eq_sub]
  exact hF.sub (continuous_const.mul hE)

/-- Exact covariance of the TWO true residuals; no orthogonality is assumed. -/
theorem regression_covariance (F D E : α → ℝ)
    (hF : Continuous F) (hD : Continuous D) (hE : Continuous E)
    (hEV : variance μ E = (1 / 4 : ℝ)) :
    covariance μ (regressionResidual μ F E) (regressionResidual μ D E) =
      covariance μ F D - 4 * covariance μ F E * covariance μ D E := by
  rw [regressionResidual_eq_sub, regressionResidual_eq_sub]
  rw [covariance_sub_mul_left μ F E _ _ hF hE
    (hD.sub (continuous_const.mul hE)),
    covariance_sub_mul_right μ F D E _ hF hD hE,
    covariance_sub_mul_right μ E D E _ hE hD hE,
    covariance_swap μ E D]
  change _ - (4 * covariance μ F E) *
    (covariance μ D E - (4 * covariance μ D E) * variance μ E) = _
  rw [hEV]
  ring

/-- Sharp regression Cauchy bound: the error is controlled by both residuals,
not by the full variance of either original argument. -/
theorem regression_pairing_sq_le (F D E : α → ℝ)
    (hF : Continuous F) (hD : Continuous D) (hE : Continuous E)
    (hEV : variance μ E = (1 / 4 : ℝ)) :
    (covariance μ F D - 4 * covariance μ F E * covariance μ D E) ^ 2 ≤
      regressionDefect μ F E * regressionDefect μ D E := by
  have h := covariance_sq_le_variances μ
    (regressionResidual μ F E) (regressionResidual μ D E)
    (regression_continuous μ F E hF hE) (regression_continuous μ D E hD hE)
  rw [regression_covariance μ F D E hF hD hE hEV,
    ← regressionDefect_eq_residualVariance μ F E hF hE hEV,
    ← regressionDefect_eq_residualVariance μ D E hD hE hEV] at h
  exact h

end
end MGAP4D.MathlibAnalytic.CompactEnergyRegressionContrast

#print axioms MGAP4D.MathlibAnalytic.CompactEnergyRegressionContrast.covariance_swap
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyRegressionContrast.covariance_sub_mul_left
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyRegressionContrast.covariance_sub_mul_right
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyRegressionContrast.covariance_sq_le_variances
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyRegressionContrast.regressionResidual_eq_sub
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyRegressionContrast.regression_covariance
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyRegressionContrast.regression_pairing_sq_le
