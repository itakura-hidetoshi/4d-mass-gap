import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingRate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- A positive exponential tail integrated forward from `t₀` is bounded by the
inverse decay rate. -/
theorem intervalIntegral_exp_tail_from_start_le_inv
    (β t₀ t : ℝ) (ht : t₀ ≤ t) (hβpos : 0 < β) :
    (∫ s in t₀..t, Real.exp (-((s - t₀) * β))) ≤ 1 / β := by
  have hβne : β ≠ 0 := ne_of_gt hβpos
  have hclosed :=
    intervalIntegral_exp_memory_mul_exp_tail_eq_div 0 β t₀ t (by linarith)
  have hformula :
      (Real.exp (-((t - t₀) * β)) - Real.exp (-((t - t₀) * 0))) / (0 - β) =
        (1 - Real.exp (-((t - t₀) * β))) / β := by
    rw [mul_zero, neg_zero, Real.exp_zero]
    field_simp [hβne]
    ring
  have htail :
      (∫ s in t₀..t, Real.exp (-((s - t₀) * β))) =
        (1 - Real.exp (-((t - t₀) * β))) / β := by
    simpa [hformula] using hclosed
  rw [htail]
  apply (div_le_div_iff₀ hβpos hβpos).2
  nlinarith [Real.exp_pos (-((t - t₀) * β))]

/-- A positive exponential memory kernel integrated backward from `t` is bounded
by the inverse decay rate. -/
theorem intervalIntegral_exp_memory_to_end_le_inv
    (α t₀ t : ℝ) (ht : t₀ ≤ t) (hαpos : 0 < α) :
    (∫ s in t₀..t, Real.exp (-((t - s) * α))) ≤ 1 / α := by
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hclosed :=
    intervalIntegral_exp_memory_mul_exp_tail_eq_div α 0 t₀ t (by linarith)
  have hformula :
      (Real.exp (-((t - t₀) * 0)) - Real.exp (-((t - t₀) * α))) / (α - 0) =
        (1 - Real.exp (-((t - t₀) * α))) / α := by
    simp [hαne]
  have hmemory :
      (∫ s in t₀..t, Real.exp (-((t - s) * α))) =
        (1 - Real.exp (-((t - t₀) * α))) / α := by
    simpa [hformula] using hclosed
  rw [hmemory]
  apply (div_le_div_iff₀ hαpos hαpos).2
  nlinarith [Real.exp_pos (-((t - t₀) * α))]

/-- The convolution of spectral decay `δ` and forcing decay `μ` has a single
subcritical envelope at every `ν < min δ μ`, without a resonance split. -/
theorem intervalIntegral_exp_memory_mul_exp_tail_le_uniform_subcritical
    (δ μ ν t₀ t : ℝ) (ht : t₀ ≤ t) (hνδ : ν < δ) (hνμ : ν < μ) :
    (∫ s in t₀..t,
      Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ))) ≤
      (1 / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν)) := by
  rcases le_total δ μ with hδμ | hμδ
  · have hβpos : 0 < μ - ν := sub_pos.mpr hνμ
    have hleftContinuous : Continuous (fun s : ℝ =>
        Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ))) := by
      fun_prop
    have hrightContinuous : Continuous (fun s : ℝ =>
        Real.exp (-((t - t₀) * ν)) * Real.exp (-((s - t₀) * (μ - ν)))) := by
      fun_prop
    have hmono :
        (∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ))) ≤
          ∫ s in t₀..t,
            Real.exp (-((t - t₀) * ν)) *
              Real.exp (-((s - t₀) * (μ - ν))) := by
      apply intervalIntegral.integral_mono_on ht
        (hleftContinuous.intervalIntegrable t₀ t)
        (hrightContinuous.intervalIntegrable t₀ t)
      intro s hs
      have hts : 0 ≤ t - s := sub_nonneg.mpr hs.2
      have hres : Real.exp (-((t - s) * (δ - ν))) ≤ 1 := by
        have := Real.exp_le_exp.mpr (show -((t - s) * (δ - ν)) ≤ 0 by
          nlinarith)
        simpa using this
      have hfactor :
          Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ)) =
            Real.exp (-((t - t₀) * ν)) *
              Real.exp (-((t - s) * (δ - ν))) *
                Real.exp (-((s - t₀) * (μ - ν))) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hfactor]
      calc
        Real.exp (-((t - t₀) * ν)) *
              Real.exp (-((t - s) * (δ - ν))) *
                Real.exp (-((s - t₀) * (μ - ν))) ≤
            Real.exp (-((t - t₀) * ν)) * 1 *
              Real.exp (-((s - t₀) * (μ - ν))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hres (Real.exp_pos _).le)
            (Real.exp_pos _).le
        _ = Real.exp (-((t - t₀) * ν)) *
              Real.exp (-((s - t₀) * (μ - ν))) := by ring
    have htail := intervalIntegral_exp_tail_from_start_le_inv
      (μ - ν) t₀ t ht hβpos
    have hright :
        (∫ s in t₀..t,
          Real.exp (-((t - t₀) * ν)) *
            Real.exp (-((s - t₀) * (μ - ν)))) ≤
          Real.exp (-((t - t₀) * ν)) * (1 / (μ - ν)) := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
    calc
      (∫ s in t₀..t,
        Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ))) ≤
          Real.exp (-((t - t₀) * ν)) * (1 / (μ - ν)) := hmono.trans hright
      _ = (1 / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν)) := by
        rw [max_eq_right hδμ]
        ring
  · have hαpos : 0 < δ - ν := sub_pos.mpr hνδ
    have hleftContinuous : Continuous (fun s : ℝ =>
        Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ))) := by
      fun_prop
    have hrightContinuous : Continuous (fun s : ℝ =>
        Real.exp (-((t - t₀) * ν)) * Real.exp (-((t - s) * (δ - ν)))) := by
      fun_prop
    have hmono :
        (∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ))) ≤
          ∫ s in t₀..t,
            Real.exp (-((t - t₀) * ν)) *
              Real.exp (-((t - s) * (δ - ν))) := by
      apply intervalIntegral.integral_mono_on ht
        (hleftContinuous.intervalIntegrable t₀ t)
        (hrightContinuous.intervalIntegrable t₀ t)
      intro s hs
      have hs₀ : 0 ≤ s - t₀ := sub_nonneg.mpr hs.1
      have hres : Real.exp (-((s - t₀) * (μ - ν))) ≤ 1 := by
        have := Real.exp_le_exp.mpr (show -((s - t₀) * (μ - ν)) ≤ 0 by
          nlinarith)
        simpa using this
      have hfactor :
          Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ)) =
            Real.exp (-((t - t₀) * ν)) *
              Real.exp (-((t - s) * (δ - ν))) *
                Real.exp (-((s - t₀) * (μ - ν))) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hfactor]
      calc
        Real.exp (-((t - t₀) * ν)) *
              Real.exp (-((t - s) * (δ - ν))) *
                Real.exp (-((s - t₀) * (μ - ν))) ≤
            Real.exp (-((t - t₀) * ν)) *
              Real.exp (-((t - s) * (δ - ν))) * 1 :=
          mul_le_mul_of_nonneg_left hres
            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        _ = Real.exp (-((t - t₀) * ν)) *
              Real.exp (-((t - s) * (δ - ν))) := by ring
    have hmemory := intervalIntegral_exp_memory_to_end_le_inv
      (δ - ν) t₀ t ht hαpos
    have hright :
        (∫ s in t₀..t,
          Real.exp (-((t - t₀) * ν)) *
            Real.exp (-((t - s) * (δ - ν)))) ≤
          Real.exp (-((t - t₀) * ν)) * (1 / (δ - ν)) := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hmemory (Real.exp_pos _).le
    calc
      (∫ s in t₀..t,
        Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ))) ≤
          Real.exp (-((t - t₀) * ν)) * (1 / (δ - ν)) := hmono.trans hright
      _ = (1 / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν)) := by
        rw [max_eq_left hμδ]
        ring

end

end MathlibAnalytic
end MGAP4D
