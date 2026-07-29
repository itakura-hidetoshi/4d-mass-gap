import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformSubcriticalScalar

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- A forcing tail with rate `μ` contributes at every subcritical rate
`ν < min δ μ`, with a resonance-free denominator `max δ μ - ν`. -/
theorem intervalIntegral_exp_memory_mul_le_exponential_tail_uniform_subcritical
    (δ μ ν C t₀ t : ℝ) (ht : t₀ ≤ t) (hνδ : ν < δ) (hνμ : ν < μ)
    (hC : 0 ≤ C) (g : ℝ → ℝ) (hg : Continuous g)
    (hgC : ∀ s ∈ Set.Icc t₀ t,
      g s ≤ C * Real.exp (-((s - t₀) * μ))) :
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
      (C / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν)) := by
  have hleftContinuous : Continuous (fun s : ℝ =>
      Real.exp (-((t - s) * δ)) * g s) := by
    fun_prop
  have hrightContinuous : Continuous (fun s : ℝ =>
      Real.exp (-((t - s) * δ)) *
        (C * Real.exp (-((s - t₀) * μ)))) := by
    fun_prop
  have hmono :
      (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
        ∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) *
            (C * Real.exp (-((s - t₀) * μ))) := by
    apply intervalIntegral.integral_mono_on ht
      (hleftContinuous.intervalIntegrable t₀ t)
      (hrightContinuous.intervalIntegrable t₀ t)
    intro s hs
    exact mul_le_mul_of_nonneg_left (hgC s hs) (Real.exp_pos _).le
  have hfactor :
      (∫ s in t₀..t,
        Real.exp (-((t - s) * δ)) *
          (C * Real.exp (-((s - t₀) * μ)))) =
        (∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) *
            Real.exp (-((s - t₀) * μ))) * C := by
    have hfun :
        (fun s : ℝ =>
          Real.exp (-((t - s) * δ)) *
            (C * Real.exp (-((s - t₀) * μ)))) =
          fun s : ℝ =>
            (Real.exp (-((t - s) * δ)) *
              Real.exp (-((s - t₀) * μ))) * C := by
      funext s
      ring
    rw [hfun, intervalIntegral.integral_mul_const]
  have hkernel :=
    intervalIntegral_exp_memory_mul_exp_tail_le_uniform_subcritical
      δ μ ν t₀ t ht hνδ hνμ
  have hscaled :
      (∫ s in t₀..t,
        Real.exp (-((t - s) * δ)) *
          Real.exp (-((s - t₀) * μ))) * C ≤
        ((1 / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν))) * C :=
    mul_le_mul_of_nonneg_right hkernel hC
  calc
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
        ∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) *
            (C * Real.exp (-((s - t₀) * μ))) := hmono
    _ = (∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) *
            Real.exp (-((s - t₀) * μ))) * C := hfactor
    _ ≤ ((1 / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν))) * C := hscaled
    _ = (C / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν)) := by
      ring

end

end MathlibAnalytic
end MGAP4D
