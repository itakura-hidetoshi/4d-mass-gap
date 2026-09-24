import Mathlib.Tactic

/-!
# From pointwise RMS response bounds to integrated L2 response bounds

Suppose an outer-context response delta(x) is controlled pointwise by

  |delta(x)| <= K * sqrt(energy(x)).

After squaring and integrating, the same coefficient remains linear after the
final square root:

  sqrt(∫ delta(x)^2 dμ) <= K * sqrt(∫ energy(x) dμ).

This is the analytic passage required to lift the pointwise physical
centered-mean transport theorem to an outer-context L2 response vector.  No
finite-cardinality estimate is used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

namespace RealIntegralPointwiseRMSResponseL2

/-- Pointwise RMS domination integrates to an L2-amplitude domination with the
same linear coefficient.  Integrability is stated explicitly because the
physical bounded-concrete wrapper discharges it separately. -/
theorem sqrt_integral_sq_le_mul_sqrt_integral_of_pointwise
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (delta energy : α → ℝ)
    (coefficient : ℝ)
    (hDeltaSq : Integrable (fun x => delta x ^ 2) μ)
    (hEnergy : Integrable energy μ)
    (hEnergyNonneg : ∀ x, 0 ≤ energy x)
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hPointwise : ∀ x,
      |delta x| ≤ coefficient * Real.sqrt (energy x)) :
    Real.sqrt (∫ x, delta x ^ 2 ∂μ) ≤
      coefficient * Real.sqrt (∫ x, energy x ∂μ) := by
  have hSqPointwise : ∀ x,
      delta x ^ 2 ≤ coefficient ^ 2 * energy x := by
    intro x
    have hLeftNonneg : 0 ≤ |delta x| := abs_nonneg _
    have hRightNonneg :
        0 ≤ coefficient * Real.sqrt (energy x) :=
      mul_nonneg hCoefficientNonneg (Real.sqrt_nonneg _)
    have hSq :=
      (sq_le_sq₀ hLeftNonneg hRightNonneg).2 (hPointwise x)
    rw [sq_abs, mul_pow, Real.sq_sqrt (hEnergyNonneg x)] at hSq
    exact hSq
  have hScaledEnergy :
      Integrable (fun x => coefficient ^ 2 * energy x) μ :=
    hEnergy.const_mul (coefficient ^ 2)
  have hIntegralSq :
      (∫ x, delta x ^ 2 ∂μ) ≤
        coefficient ^ 2 * ∫ x, energy x ∂μ := by
    calc
      (∫ x, delta x ^ 2 ∂μ) ≤
          ∫ x, coefficient ^ 2 * energy x ∂μ := by
        exact integral_mono hDeltaSq hScaledEnergy hSqPointwise
      _ = coefficient ^ 2 * ∫ x, energy x ∂μ := by
        rw [integral_const_mul]
  have hDeltaIntegralNonneg :
      0 ≤ ∫ x, delta x ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg (delta x)
  have hEnergyIntegralNonneg :
      0 ≤ ∫ x, energy x ∂μ :=
    integral_nonneg hEnergyNonneg
  apply
    (sq_le_sq₀
      (Real.sqrt_nonneg _)
      (mul_nonneg hCoefficientNonneg (Real.sqrt_nonneg _))).mp
  rw [
    Real.sq_sqrt hDeltaIntegralNonneg,
    mul_pow,
    Real.sq_sqrt hEnergyIntegralNonneg]
  exact hIntegralSq

/-- If the integrated RMS energy is itself bounded by a declared amplitude,
the response L2 amplitude is bounded by coefficient times that amplitude. -/
theorem sqrt_integral_sq_le_mul_of_pointwise_and_energy_majorant
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (delta energy : α → ℝ)
    (coefficient amplitude : ℝ)
    (hDeltaSq : Integrable (fun x => delta x ^ 2) μ)
    (hEnergy : Integrable energy μ)
    (hEnergyNonneg : ∀ x, 0 ≤ energy x)
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hPointwise : ∀ x,
      |delta x| ≤ coefficient * Real.sqrt (energy x))
    (hEnergyMajorant :
      Real.sqrt (∫ x, energy x ∂μ) ≤ amplitude) :
    Real.sqrt (∫ x, delta x ^ 2 ∂μ) ≤
      coefficient * amplitude := by
  exact
    (sqrt_integral_sq_le_mul_sqrt_integral_of_pointwise
      μ delta energy coefficient
      hDeltaSq hEnergy hEnergyNonneg hCoefficientNonneg hPointwise).trans
      (mul_le_mul_of_nonneg_left hEnergyMajorant hCoefficientNonneg)

end RealIntegralPointwiseRMSResponseL2

end

end MGAP4D.MathlibAnalytic
