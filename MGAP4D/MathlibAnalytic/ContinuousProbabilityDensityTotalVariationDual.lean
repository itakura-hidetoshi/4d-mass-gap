import MGAP4D.MathlibAnalytic.ContinuousProbabilityDensityCenteredIntegral

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

theorem continuous_probabilityDensity_test_difference_abs_le_l1_mul_radius
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p q h : X → ℝ)
    (hp : Continuous p)
    (hq : Continuous q)
    (hh : Continuous h)
    (hp_int : ∫ x, p x ∂μ = 1)
    (hq_int : ∫ x, q x ∂μ = 1)
    (center radius : ℝ)
    (_hRadiusNonneg : 0 ≤ radius)
    (hRadius : ∀ x : X, |h x - center| ≤ radius) :
    |(∫ x, p x * h x ∂μ) - ∫ x, q x * h x ∂μ| ≤
      (∫ x, |p x - q x| ∂μ) * radius := by
  have hCenteredInt : Integrable
      (fun x : X => (p x - q x) * (h x - center)) μ :=
    ((hp.sub hq).mul (hh.sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAbsCenteredInt : Integrable
      (fun x : X => |(p x - q x) * (h x - center)|) μ := by
    simpa [Real.norm_eq_abs] using hCenteredInt.norm
  have hUpperInt : Integrable
      (fun x : X => |p x - q x| * radius) μ :=
    ((hp.sub hq).abs.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← continuous_probabilityDensity_centered_integral_identity
    μ p q h hp hq hh hp_int hq_int center]
  calc
    |∫ x, (p x - q x) * (h x - center) ∂μ| ≤
        ∫ x, |(p x - q x) * (h x - center)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, |p x - q x| * radius ∂μ := by
      apply integral_mono hAbsCenteredInt hUpperInt
      intro x
      simpa only [abs_mul] using
        mul_le_mul_of_nonneg_left (hRadius x) (abs_nonneg (p x - q x))
    _ = (∫ x, |p x - q x| ∂μ) * radius := by
      rw [integral_mul_const]

theorem continuous_probabilityDensity_test_difference_abs_le_two_mul_tv_mul_radius
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p q h : X → ℝ)
    (hp : Continuous p)
    (hq : Continuous q)
    (hh : Continuous h)
    (hp_int : ∫ x, p x ∂μ = 1)
    (hq_int : ∫ x, q x ∂μ = 1)
    (center radius : ℝ)
    (hRadiusNonneg : 0 ≤ radius)
    (hRadius : ∀ x : X, |h x - center| ≤ radius) :
    |(∫ x, p x * h x ∂μ) - ∫ x, q x * h x ∂μ| ≤
      2 * ((2 : ℝ)⁻¹ * ∫ x, |p x - q x| ∂μ) * radius := by
  have hBound :=
    continuous_probabilityDensity_test_difference_abs_le_l1_mul_radius
      μ p q h hp hq hh hp_int hq_int center radius hRadiusNonneg hRadius
  convert hBound using 1 <;> ring

end
end MathlibAnalytic
end MGAP4D
