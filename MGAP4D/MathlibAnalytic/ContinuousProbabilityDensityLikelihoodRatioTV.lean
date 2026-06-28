import MGAP4D.MathlibAnalytic.RealDensityLikelihoodRatioPointwise
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Sharp total-variation estimate for two continuous probability densities
with a common multiplicative likelihood-ratio bound. -/
theorem continuous_probabilityDensity_totalVariation_le_of_mutual_le_mul
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p q : X → ℝ)
    (hp_cont : Continuous p)
    (hq_cont : Continuous q)
    (hp_int : ∫ x, p x ∂μ = 1)
    (hq_int : ∫ x, q x ∂μ = 1)
    (c : ℝ)
    (hc : 1 ≤ c)
    (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x)
    (hpq : ∀ x, p x ≤ c * q x)
    (hqp : ∀ x, q x ≤ c * p x) :
    (2 : ℝ)⁻¹ * ∫ x, |p x - q x| ∂μ ≤
      (c - 1) / (c + 1) := by
  have hPoint : ∀ x : X,
      (c + 1) * |p x - q x| ≤
        (c - 1) * (p x + q x) :=
    real_density_abs_sub_mul_le_of_mutual_le_mul
      p q c hc hp hq hpq hqp
  have hIntegral :
      ∫ x, (c + 1) * |p x - q x| ∂μ ≤
        ∫ x, (c - 1) * (p x + q x) ∂μ := by
    exact integral_mono (Filter.Eventually.of_forall hPoint)
  rw [integral_const_mul, integral_const_mul] at hIntegral
  have hp_integrable : Integrable p μ :=
    hp_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace p)
  have hq_integrable : Integrable q μ :=
    hq_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace q)
  have hpq_int : ∫ x, p x + q x ∂μ = 2 := by
    rw [integral_add hp_integrable hq_integrable, hp_int, hq_int]
    norm_num
  rw [hpq_int] at hIntegral
  have hden : 0 < c + 1 := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith

end
end MathlibAnalytic
end MGAP4D
