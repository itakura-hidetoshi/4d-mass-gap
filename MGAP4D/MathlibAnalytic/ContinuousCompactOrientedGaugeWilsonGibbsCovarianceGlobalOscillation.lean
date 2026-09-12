import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathGibbsCovariance
import Mathlib.Tactic

/-!
# Gibbs covariance controlled by global oscillation

This file isolates the measure-theoretic exit needed by the finite-volume
Dobrushin route.  If a bounded continuous right observable has global
oscillation at most `R`, then its centered value around the actual Wilson Gibbs
mean is pointwise bounded by `R`, and consequently its Gibbs covariance with a
bounded continuous left observable is bounded by `‖F‖ * R`.

The argument uses only that the canonical Wilson Gibbs measure is a probability
measure.  No Dobrushin threshold, support separation, continuum limit, OS
reconstruction, or mass-gap conclusion is used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

private theorem continuous_compact_oriented_bcf_integrable_gibbs
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable (fun A : C.base.Configuration => O A) C.gibbsMeasure := by
  exact
    O.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

private theorem continuous_compact_oriented_bcf_abs_le_norm_covariance
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    |O A| ≤ ‖O‖ := by
  simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A

/-- A global oscillation bound centers sharply around the actual finite-volume
Wilson Gibbs mean. -/
theorem continuous_compact_oriented_abs_sub_gibbsMeanReal_le_of_globalOscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (R : ℝ)
    (hOsc : ∀ A B : C.base.Configuration, |O A - O B| ≤ R)
    (A : C.base.Configuration) :
    |O A - C.gibbsMeanReal (fun B => O B)| ≤ R := by
  let μ := C.gibbsMeasure
  have hOInt : Integrable (fun B : C.base.Configuration => O B) μ :=
    continuous_compact_oriented_bcf_integrable_gibbs C O
  have hConstInt : Integrable (fun _B : C.base.Configuration => O A) μ :=
    integrable_const (O A)
  have hDiffInt :
      Integrable (fun B : C.base.Configuration => O A - O B) μ :=
    hConstInt.sub' hOInt
  have hAbsDiffInt :
      Integrable (fun B : C.base.Configuration => |O A - O B|) μ := by
    simpa [Real.norm_eq_abs] using hDiffInt.norm
  have hRInt : Integrable (fun _B : C.base.Configuration => R) μ :=
    integrable_const R
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeanReal
  change |O A - ∫ B, O B ∂μ| ≤ R
  calc
    |O A - ∫ B, O B ∂μ| =
        |(∫ _B : C.base.Configuration, O A ∂μ) -
          ∫ B, O B ∂μ| := by simp
    _ = |∫ B, O A - O B ∂μ| := by
      rw [integral_sub hConstInt hOInt]
    _ ≤ ∫ B, |O A - O B| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _B : C.base.Configuration, R ∂μ := by
      apply integral_mono hAbsDiffInt hRInt
      intro B
      exact hOsc A B
    _ = R := by simp

/-- For the actual finite-volume Wilson Gibbs probability measure, a global
oscillation bound `R` on the right observable controls covariance by
`‖F‖ * R`. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_abs_le_norm_mul_globalOscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F O : BoundedContinuousFunction C.base.Configuration ℝ)
    (R : ℝ)
    (hOsc : ∀ A B : C.base.Configuration, |O A - O B| ≤ R) :
    |C.gibbsCovarianceReal (fun A => F A) (fun A => O A)| ≤ ‖F‖ * R := by
  let μ := C.gibbsMeasure
  let mO : ℝ := C.gibbsMeanReal (fun A => O A)
  have hFOInt :
      Integrable (fun A : C.base.Configuration => F A * O A) μ := by
    exact
      (F.continuous.mul O.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hFmInt :
      Integrable (fun A : C.base.Configuration => F A * mO) μ := by
    exact
      (F.continuous.mul continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hCenteredProductInt :
      Integrable (fun A : C.base.Configuration => F A * (O A - mO)) μ := by
    exact
      (F.continuous.mul (O.continuous.sub continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hAbsCenteredProductInt :
      Integrable (fun A : C.base.Configuration => |F A * (O A - mO)|) μ := by
    simpa [Real.norm_eq_abs] using hCenteredProductInt.norm
  have hConstInt :
      Integrable (fun _A : C.base.Configuration => ‖F‖ * R) μ :=
    integrable_const (‖F‖ * R)
  have hCentered : ∀ A : C.base.Configuration, |O A - mO| ≤ R := by
    intro A
    exact
      continuous_compact_oriented_abs_sub_gibbsMeanReal_le_of_globalOscillation
        C O R hOsc A
  have hPointwise :
      ∀ A : C.base.Configuration,
        |F A * (O A - mO)| ≤ ‖F‖ * R := by
    intro A
    rw [abs_mul]
    exact
      mul_le_mul
        (continuous_compact_oriented_bcf_abs_le_norm_covariance F A)
        (hCentered A) (abs_nonneg _) (norm_nonneg _)
  have hCenteredIntegral :
      (∫ A, F A * (O A - mO) ∂μ) =
        (∫ A, F A * O A ∂μ) - (∫ A, F A ∂μ) * mO := by
    simp_rw [mul_sub]
    rw [integral_sub hFOInt hFmInt, integral_mul_const]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
  change
    |(∫ A, F A * O A ∂μ) -
      (∫ A, F A ∂μ) * C.gibbsMeanReal (fun A => O A)| ≤ ‖F‖ * R
  change
    |(∫ A, F A * O A ∂μ) - (∫ A, F A ∂μ) * mO| ≤ ‖F‖ * R
  rw [← hCenteredIntegral]
  calc
    |∫ A, F A * (O A - mO) ∂μ| ≤
        ∫ A, |F A * (O A - mO)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _A : C.base.Configuration, ‖F‖ * R ∂μ := by
      apply integral_mono hAbsCenteredProductInt hConstInt
      intro A
      exact hPointwise A
    _ = ‖F‖ * R := by simp

end

end MathlibAnalytic
end MGAP4D
