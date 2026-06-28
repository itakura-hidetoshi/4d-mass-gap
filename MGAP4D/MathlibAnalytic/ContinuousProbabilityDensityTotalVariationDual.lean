import MGAP4D.MathlibAnalytic.ContinuousProbabilityDensityLikelihoodRatioTV

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A centered bounded test function is controlled by the `L¹` distance of two
continuous normalized densities. -/
theorem continuous_probabilityDensity_test_difference_abs_le_l1_mul_radius
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
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
      (∫ x, |p x - q x| ∂μ) * radius := by
  have hpInt : Integrable p μ :=
    hp.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace p)
  have hqInt : Integrable q μ :=
    hq.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace q)
  have hpHInt : Integrable (fun x : X => p x * h x) μ :=
    (hp.mul hh).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hqHInt : Integrable (fun x : X => q x * h x) μ :=
    (hq.mul hh).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDiffInt : Integrable (fun x : X => p x - q x) μ :=
    (hp.sub hq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCenteredProductInt : Integrable
      (fun x : X => (p x - q x) * (h x - center)) μ :=
    ((hp.sub hq).mul (hh.sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAbsCenteredProductInt : Integrable
      (fun x : X => |(p x - q x) * (h x - center)|) μ := by
    simpa [Real.norm_eq_abs] using hCenteredProductInt.norm
  have hAbsDiffRadiusInt : Integrable
      (fun x : X => |p x - q x| * radius) μ :=
    ((hp.sub hq).abs.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCenterDiffInt : Integrable
      (fun x : X => center * (p x - q x)) μ :=
    (continuous_const.mul (hp.sub hq)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCenteredIdentity :
      (∫ x, (p x - q x) * (h x - center) ∂μ) =
        (∫ x, p x * h x ∂μ) - ∫ x, q x * h x ∂μ := by
    calc
      (∫ x, (p x - q x) * (h x - center) ∂μ) =
          ∫ x, (p x * h x - q x * h x) -
            center * (p x - q x) ∂μ := by
        apply integral_congr
        intro x
        ring
      _ = (∫ x, p x * h x - q x * h x ∂μ) -
          ∫ x, center * (p x - q x) ∂μ := by
        rw [integral_sub (hpHInt.sub hqHInt) hCenterDiffInt]
      _ = ((∫ x, p x * h x ∂μ) - ∫ x, q x * h x ∂μ) -
          center * ((∫ x, p x ∂μ) - ∫ x, q x ∂μ) := by
        rw [integral_sub hpHInt hqHInt, integral_const_mul,
          integral_sub hpInt hqInt]
      _ = (∫ x, p x * h x ∂μ) - ∫ x, q x * h x ∂μ := by
        rw [hp_int, hq_int]
        ring
  rw [← hCenteredIdentity]
  calc
    |∫ x, (p x - q x) * (h x - center) ∂μ| ≤
        ∫ x, |(p x - q x) * (h x - center)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, |p x - q x| * radius ∂μ := by
      apply integral_mono hAbsCenteredProductInt hAbsDiffRadiusInt
      intro x
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hRadius x) (abs_nonneg _)
    _ = (∫ x, |p x - q x| ∂μ) * radius := by
      rw [integral_mul_const]

/-- Total variation in the density convention `TV = 1/2 * L¹` controls every
centered continuous test function. -/
theorem continuous_probabilityDensity_test_difference_abs_le_two_mul_tv_mul_radius
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
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
      μ p q h hp hq hh hp_int hq_int center radius
      hRadiusNonneg hRadius
  convert hBound using 1 <;> ring

end
end MathlibAnalytic
end MGAP4D
