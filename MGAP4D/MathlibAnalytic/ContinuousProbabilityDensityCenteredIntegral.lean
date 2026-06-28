import MGAP4D.MathlibAnalytic.ContinuousProbabilityDensityLikelihoodRatioTV

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

theorem continuous_probabilityDensity_centered_integral_identity
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
    (center : ℝ) :
    (∫ x, (p x - q x) * (h x - center) ∂μ) =
      (∫ x, p x * h x ∂μ) - ∫ x, q x * h x ∂μ := by
  have hpInt : Integrable p μ :=
    hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace p)
  have hqInt : Integrable q μ :=
    hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace q)
  have hpHInt : Integrable (fun x : X => p x * h x) μ :=
    (hp.mul hh).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hqHInt : Integrable (fun x : X => q x * h x) μ :=
    (hq.mul hh).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDiffInt : Integrable (fun x : X => p x - q x) μ := hpInt.sub hqInt
  have hProductDifferenceInt : Integrable
      (fun x : X => p x * h x - q x * h x) μ := hpHInt.sub hqHInt
  have hCenterDiffInt : Integrable
      (fun x : X => center * (p x - q x)) μ := hDiffInt.const_mul center
  have hPointwise :
      (∫ x, (p x - q x) * (h x - center) ∂μ) =
        ∫ x, (p x * h x - q x * h x) - center * (p x - q x) ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    ring
  have hOuter :
      (∫ x, (p x * h x - q x * h x) - center * (p x - q x) ∂μ) =
        (∫ x, p x * h x - q x * h x ∂μ) -
          ∫ x, center * (p x - q x) ∂μ :=
    integral_sub hProductDifferenceInt hCenterDiffInt
  have hProduct :
      (∫ x, p x * h x - q x * h x ∂μ) =
        (∫ x, p x * h x ∂μ) - ∫ x, q x * h x ∂μ :=
    integral_sub hpHInt hqHInt
  have hDensity :
      (∫ x, p x - q x ∂μ) = (∫ x, p x ∂μ) - ∫ x, q x ∂μ :=
    integral_sub hpInt hqInt
  rw [hPointwise, hOuter, hProduct, integral_const_mul,
    hDensity, hp_int, hq_int]
  ring

end
end MathlibAnalytic
end MGAP4D
