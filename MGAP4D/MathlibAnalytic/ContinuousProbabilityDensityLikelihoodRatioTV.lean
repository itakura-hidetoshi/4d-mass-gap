import MGAP4D.MathlibAnalytic.RealDensityLikelihoodRatioPointwise
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.CompactlySupported

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

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
  have hLeftContinuous : Continuous
      (fun x : X => (c + 1) * |p x - q x|) :=
    continuous_const.mul ((hp_cont.sub hq_cont).abs)
  have hRightContinuous : Continuous
      (fun x : X => (c - 1) * (p x + q x)) :=
    continuous_const.mul (hp_cont.add hq_cont)
  have hLeftIntegrable : Integrable
      (fun x : X => (c + 1) * |p x - q x|) μ :=
    hLeftContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRightIntegrable : Integrable
      (fun x : X => (c - 1) * (p x + q x)) μ :=
    hRightContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntegral :
      ∫ x, (c + 1) * |p x - q x| ∂μ ≤
        ∫ x, (c - 1) * (p x + q x) ∂μ :=
    integral_mono hLeftIntegrable hRightIntegrable hPoint
  rw [integral_const_mul, integral_const_mul] at hIntegral
  have hpIntegrable : Integrable p μ :=
    hp_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace p)
  have hqIntegrable : Integrable q μ :=
    hq_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace q)
  have hpqIntegral : ∫ x, p x + q x ∂μ = 2 := by
    rw [integral_add hpIntegrable hqIntegrable, hp_int, hq_int]
    norm_num
  rw [hpqIntegral] at hIntegral
  have hden : 0 < c + 1 := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith

end
end MathlibAnalytic
end MGAP4D
