import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathJointDensity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Exact one-link heat-bath integration on an assembled off-link fiber is
integration over the newly sampled Haar link value with its conditional
density. -/
theorem continuous_compact_oriented_lintegral_heatBathKernel_assemble
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge)
    (Aoff : C.base.OffLinkConfiguration target)
    (F : C.base.Configuration → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ B, F B
        ∂C.singleLinkHeatBathKernel target
          (C.base.singleLinkAssemble target g Aoff) =
      ∫⁻ h,
        C.singleLinkConditionalDensity target
            (C.base.singleLinkAssemble target g Aoff) h *
          F (C.base.singleLinkAssemble target h Aoff)
        ∂normalizedCompactHaar C.base.Gauge := by
  rw [continuous_compact_oriented_lintegral_singleLinkHeatBathKernel
      C target (C.base.singleLinkAssemble target g Aoff) F hF,
    continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity]
  let A : C.base.Configuration :=
    C.base.singleLinkAssemble target g Aoff
  let ρ : C.base.Gauge → ℝ≥0∞ :=
    fun h => C.singleLinkConditionalDensity target A h
  let U : C.base.Gauge → C.base.Configuration :=
    fun h => C.base.replaceLink A target h
  have hDensity : Measurable ρ := by
    exact
      (measurable_compact_oriented_singleLinkConditionalDensity_uncurry
        C target).comp
        (measurable_const.prodMk measurable_id)
  have hUpdated : Measurable (fun h : C.base.Gauge => F (U h)) := by
    exact hF.comp
      (continuous_compact_oriented_replaceLink C A target).measurable
  calc
    (∫⁻ h, F (U h)
        ∂(normalizedCompactHaar C.base.Gauge).withDensity ρ) =
        ∫⁻ h, ρ h * F (U h)
          ∂normalizedCompactHaar C.base.Gauge := by
      simpa only [Function.comp_apply] using
        (lintegral_withDensity_eq_lintegral_mul
          (normalizedCompactHaar C.base.Gauge) hDensity hUpdated)
    _ = ∫⁻ h,
        C.singleLinkConditionalDensity target
            (C.base.singleLinkAssemble target g Aoff) h *
          F (C.base.singleLinkAssemble target h Aoff)
        ∂normalizedCompactHaar C.base.Gauge := by
      apply lintegral_congr
      intro h
      dsimp [ρ, U, A]
      rw [compact_oriented_replaceLink_singleLinkAssemble]

end

end MathlibAnalytic
end MGAP4D
